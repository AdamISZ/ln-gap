//! A dispute played from one side (LN-GAP v3): each party runs its own
//! BitVMX emulator on the statement program and the claim's input, with
//! its own checkpoints, and learns the other's moves only from the chain,
//! by reading the one-time signatures in the links' witnesses.
//!
//! - Alice is the [`Prover`]: her move 1 is the claim with round 1's
//!   hashes, each later move answers the hub's choice of segment with the
//!   next round's hashes, and her last move is the disputed step (its
//!   record and the hashes on either side).
//! - The hub is the [`Verifier`]: on Alice's move 1 it decides whether to
//!   dispute at all (an honest hub doesn't dispute a true claim); then it
//!   chooses a segment after each of her rounds; on her last move it finds
//!   the rule that applies with BitVMX's own `verifier_choose_challenge`.
//!
//! Alice checks the hub's choices (`choice_<r>` disproves one out of
//! range: not built here, an honest party never sees one).

use std::path::Path;

use anyhow::{anyhow, bail, ensure, Context, Result};
use bitcoin::Transaction;
use bitvmx_cpu_definitions::challenge::{ChallengeType, EquivocationKind};
use bitvmx_cpu_definitions::memory::MemoryWitness;
use bitvmx_cpu_definitions::trace::{ProgramCounter, TraceRWStep, TraceRead, TraceReadPC, TraceStep, TraceWrite};
use emulator::decision::challenge::{
    prover_execute, prover_final_trace, prover_get_hashes_for_round, verifier_check_execution, verifier_choose_challenge, verifier_choose_segment, ForceChallenge, ForceCondition,
};
use emulator::decision::nary_search::NArySearchType;
use emulator::executor::utils::FailConfiguration;
use emulator::loader::program_definition::ProgramDefinition;
use lngap_ladder::jump::Hop;
use lngap_ladder::tail::Path as HopPath;
use lngap_ladder::moves::{claim_message, final_message, hashes_message, View};
use lngap_ladder::{Kind, Schedule, CLAIM_BYTES};
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::final_step;
use lngap_zk::game::Record;

use crate::contract::Program;

fn h20(s: &str) -> Result<[u8; 20]> {
    hex::decode(s)?.try_into().map_err(|_| anyhow!("a step hash is 20 bytes: {s}"))
}

fn emu(e: emulator::EmulatorError) -> anyhow::Error {
    anyhow!("{e}")
}

/// What a one-time signature signed, `wire` its items in wire order.
pub fn read_signed(key: &WotsPublic, wire: &[Vec<u8>]) -> Result<Vec<u8>> {
    let mut items = wire.to_vec();
    items.reverse();
    let sig = WotsSig::from_consumption_order(key.params, &items)?;
    key.verify(&sig)
}

/// A link's own witness items: below the two 2-of-2 signatures, the
/// script and the control block.
fn link_items(tx: &Transaction) -> Result<Vec<Vec<u8>>> {
    link_items_in(tx, 0)
}

/// [`link_items`] of input `i` (a combine carries a chunk in each).
fn link_items_in(tx: &Transaction, i: usize) -> Result<Vec<Vec<u8>>> {
    let w: Vec<Vec<u8>> = tx.input.get(i).context("no such input")?.witness.iter().map(|x| x.to_vec()).collect();
    ensure!(w.len() >= 4, "not a link");
    Ok(w[..w.len() - 4].to_vec())
}

/// [`move_wires`] of input `i`.
pub fn move_wires_in(tx: &Transaction, i: usize, keys: &[WotsPublic]) -> Result<Vec<Vec<Vec<u8>>>> {
    let items = link_items_in(tx, i)?;
    let mut end = items.len();
    let mut out = vec![];
    for k in keys {
        let n = 2 * k.params.total_digits() as usize;
        ensure!(end >= n, "the input carries no move");
        out.push(items[end - n..end].to_vec());
        end -= n;
    }
    Ok(out)
}

/// What input `i` carries under `keys`, field by field, in order.
pub fn read_move_in(tx: &Transaction, i: usize, keys: &[WotsPublic]) -> Result<Vec<u8>> {
    let wires = move_wires_in(tx, i, keys)?;
    let mut m = vec![];
    for (k, w) in keys.iter().zip(&wires) {
        m.extend(read_signed(k, w)?);
    }
    Ok(m)
}

/// A move's fields' signature items in a link, as they appear (wire
/// order), by field: to re-reveal one in a later leaf without the mover's
/// keys. The move's signatures are the link's last, field 0's on top.
pub fn move_wires(tx: &Transaction, keys: &[WotsPublic]) -> Result<Vec<Vec<Vec<u8>>>> {
    let items = link_items(tx)?;
    let mut end = items.len();
    let mut out = vec![];
    for k in keys {
        let n = 2 * k.params.total_digits() as usize;
        ensure!(end >= n, "the link carries no move");
        out.push(items[end - n..end].to_vec());
        end -= n;
    }
    Ok(out)
}

/// The move a link carries: its fields as `keys` signed them, in order.
pub fn read_move(tx: &Transaction, keys: &[WotsPublic]) -> Result<Vec<u8>> {
    let wires = move_wires(tx, keys)?;
    let mut m = vec![];
    for (k, w) in keys.iter().zip(&wires) {
        m.extend(read_signed(k, w)?);
    }
    Ok(m)
}

/// The items a move's signatures take in a link.
fn move_items(keys: &[WotsPublic]) -> usize {
    keys.iter().map(|k| 2 * k.params.total_digits() as usize).sum()
}

/// The input words a link carries (escalate: the claim's words, below its
/// move; `inputs`: the rest), `keys` the words' keys in word order, `with`
/// the move's key if a move follows them.
pub fn read_words(tx: &Transaction, keys: &[WotsPublic], with: Option<&[WotsPublic]>) -> Result<Vec<u32>> {
    let wires = word_wires(tx, keys, with)?;
    keys.iter()
        .zip(&wires)
        .map(|(k, w)| {
            let msg = read_signed(k, w)?;
            Ok(u32::from_be_bytes(msg.try_into().map_err(|_| anyhow!("a word is 4 bytes"))?))
        })
        .collect()
}

/// Each input word's signature items in a link, in word order (to
/// re-reveal one in a check without the signer's key).
pub fn word_wires(tx: &Transaction, keys: &[WotsPublic], with: Option<&[WotsPublic]>) -> Result<Vec<Vec<Vec<u8>>>> {
    let mut items = link_items(tx)?;
    if let Some(k) = with {
        items.truncate(items.len() - move_items(k));
    }
    // wire order: the last word's signature first
    let mut wires = vec![vec![]; keys.len()];
    let mut at = 0;
    for (j, k) in keys.iter().enumerate().rev() {
        let n = 2 * k.params.total_digits() as usize;
        wires[j] = items.get(at..at + n).context("too few words")?.to_vec();
        at += n;
    }
    ensure!(at == items.len(), "items left over");
    Ok(wires)
}

fn h20s(m: &[u8]) -> Vec<String> {
    m.chunks(20).map(hex::encode).collect()
}

fn hashes(v: &[String]) -> Result<Vec<[u8; 20]>> {
    v.iter().map(|x| h20(x)).collect()
}

/// The hashes after `steps` (and their writes) of the execution whose
/// checkpoints are in `dir`, in one pass: by step.
fn hashes_at(pdf: &str, dir: &str, input: &[u8], steps: &[u64], fail: Option<FailConfiguration>) -> Result<std::collections::BTreeMap<u64, ([u8; 20], lngap_zk::Step)>> {
    let mut want: Vec<u64> = steps.iter().copied().filter(|x| *x > 0).collect();
    want.sort_unstable();
    want.dedup();
    let mut out = std::collections::BTreeMap::new();
    if steps.contains(&0) {
        out.insert(0, (lngap_zk::game::initial_hash(), lngap_zk::Step::default()));
    }
    if want.is_empty() {
        return Ok(out);
    }
    let pd = ProgramDefinition::from_config(pdf).map_err(|e| anyhow!("{pdf}: {e:?}"))?;
    let (_, trace) = pd.execute_helper(dir, dir, input.to_vec(), Some(want.clone()), fail, false).map_err(emu)?;
    for (t, h) in trace {
        let x = t.step_number;
        if want.contains(&x) {
            let w = lngap_zk::Step { write_addr: t.trace_step.get_write().address, write_value: t.trace_step.get_write().value, pc: t.trace_step.get_pc().get_address(), micro: t.trace_step.get_pc().get_micro() };
            out.insert(x, (h20(&h)?, w));
        }
    }
    ensure!(want.iter().all(|x| out.contains_key(x)), "the emulator didn't reach every step asked for");
    Ok(out)
}

/// Step `x`'s preimage under a jump list, from an execution's hashes.
fn preimage_at(j: &lngap_ladder::jump::JumpList, x: u64, at: &std::collections::BTreeMap<u64, ([u8; 20], lngap_zk::Step)>) -> Vec<u8> {
    let prev = at[&(x - 1)].0;
    let jh = at[&j.jump(x)].0;
    lngap_ladder::jhash::preimage(&prev, &jh, &at[&x].1, x as u32)
}

/// Alice's side.
pub struct Prover {
    pdf: String,
    dir: String,
    s: Schedule,
    input: Vec<u8>,
    fail: Option<FailConfiguration>,
    claim_hash: String,
    claim_step: u64,
    /// Every move so far, hers and the hub's (as she checked them), depth 1
    /// first.
    pub msgs: Vec<Vec<u8>>,
}

impl Prover {
    /// Execute the program on `input` (checkpoints under `dir`) and make
    /// move 1: the claim, with round 1's hashes.
    pub fn start(program: &Program, input: &[u8], dir: &Path) -> Result<Prover> {
        Prover::start_with(program, input, dir, None)
    }
    /// [`Prover::start`] with BitVMX's fault injection (a cheating prover).
    pub fn start_with(program: &Program, input: &[u8], dir: &Path, fail: Option<FailConfiguration>) -> Result<Prover> {
        let d = format!("{}/", dir.display());
        std::fs::create_dir_all(&d)?;
        let pdf = program.pdf.clone();
        let (_, last_step, last_hash) = prover_execute(&pdf, input.to_vec(), &d, &d, true, fail.clone(), false).map_err(emu)?;
        let round1 = prover_get_hashes_for_round(&pdf, &d, &d, 1, 0, fail.clone(), NArySearchType::ConflictStep).map_err(emu)?;
        let m1 = claim_message(last_step, &h20(&last_hash)?, &hashes(&round1)?);
        Ok(Prover { pdf, dir: d, s: program.schedule.clone(), input: input.to_vec(), fail, claim_hash: last_hash, claim_step: last_step, msgs: vec![m1] })
    }
    /// Her latest move.
    pub fn last(&self) -> &[u8] {
        self.msgs.last().expect("move 1")
    }
    /// The hub's choice (`signed`, its move as read from the chain) and her
    /// answer: the next round's hashes, or at the end the disputed step.
    pub fn answer(&mut self, signed: &[u8]) -> Result<Vec<u8>> {
        let depth = self.msgs.len() as u32 + 1;
        let Kind::Choice(r) = self.s.kind(depth) else { bail!("depth {depth} isn't the hub's") };
        ensure!(signed.len() == 1, "a choice is one byte");
        let c = u32::from(signed[0]);
        ensure!(c < self.s.segments(r), "the hub's choice {c} in round {r} is out of range (choice_{r} disproves it)");
        self.msgs.push(signed.to_vec());
        let next = if r < self.s.rounds() {
            let h = prover_get_hashes_for_round(&self.pdf, &self.dir, &self.dir, (r + 1) as u8, c, self.fail.clone(), NArySearchType::ConflictStep).map_err(emu)?;
            hashes_message(&hashes(&h)?)
        } else {
            let (trace, step_hash, next_hash, step) = prover_final_trace(&self.pdf, &self.dir, &self.dir, c + 1, self.fail.clone())
                .map_err(emu)?
                .as_final_trace_with_hashes_and_step()
                .map_err(|e| anyhow!("{e:?}"))?;
            ensure!(trace.step_number == step + 1, "the final trace is of step {}, the last agreed {step}", trace.step_number);
            // under a jump list, the long jump's hash her step committed to
            let jh = match self.s.jump {
                None => None,
                Some(_) if self.fail.as_ref().and_then(|f| f.fail_jump) == Some(step + 1) => Some([0u8; 20]),
                Some(j) => {
                    let y = j.jump(step + 1);
                    Some(if y == step { h20(&step_hash)? } else { self.hashes_at(&[y])?[&y].0 })
                }
            };
            final_message(&final_step(&trace, &step_hash, &next_hash, self.claim_step, &self.claim_hash)?, jh.as_ref())
        };
        self.msgs.push(next.clone());
        Ok(next)
    }
}

impl Prover {
    fn hashes_at(&self, steps: &[u64]) -> Result<std::collections::BTreeMap<u64, ([u8; 20], lngap_zk::Step)>> {
        hashes_at(&self.pdf, &self.dir, &self.input, steps, self.fail.clone())
    }
    /// The hub's path as read (its chunks, from its combine's inputs): the
    /// first hop whose hash isn't the one in her own history (or `None`:
    /// the path is genuine). Her history up to the agreed step is the
    /// truth.
    pub fn check_path(&self, chunks: &[Vec<u8>]) -> Result<Option<usize>> {
        let j = self.s.jump.context("a jump list")?;
        let t = u64::from(View { s: &self.s, msgs: &self.msgs }.record().step);
        let (n, types, end, hops) = HopPath::parse(chunks);
        let mut xs = vec![t];
        for ty in &types {
            let x = *xs.last().unwrap();
            ensure!(x > 0, "a path below step 0");
            xs.push(if *ty == Hop::Long { j.jump(x) } else { x - 1 });
        }
        let mine = self.hashes_at(&xs)?;
        for k in 0..n {
            let posted = if k + 1 == n { end } else { hops[k] };
            if posted != mine[&xs[k + 1]].0 {
                return Ok(Some(k));
            }
        }
        Ok(None)
    }
}

/// What the hub proves with a path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathKind {
    /// Alice's disputed step commits to a wrong long-jump hash.
    Jump,
    /// Her read `r` isn't the last value written at its address.
    Read(u8),
}

/// The hub's side.
pub struct Verifier {
    pdf: String,
    dir: String,
    s: Schedule,
    info: ProgramInfo,
    input: Vec<u8>,
    /// Every move so far, depth 1 first.
    pub msgs: Vec<Vec<u8>>,
}

/// What the hub does at the end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The rule that applies (its name, without `disprove_`), and the hub's
    /// own witness for it (bytes; `program_counter`'s).
    Disprove(String, Vec<u8>),
    /// None applies and Alice's step doesn't prove: the hub waits for its
    /// timeout.
    Wait,
    /// None applies: Alice's step is valid; she can prove it.
    Proved,
    /// BitVMX's read challenge, without a jump list: not carried.
    ReadChallenge,
    /// Under a jump list: a path to step `y` proves `kind`.
    Path { kind: PathKind, y: u64 },
}

impl Verifier {
    /// Alice's move 1 as signed (the claim and round 1's hashes), on the
    /// claim's `input` (checkpoints under `dir`): `None` if the hub doesn't
    /// dispute (the claim is true, unless `force`).
    pub fn start(program: &Program, input: &[u8], dir: &Path, move1: &[u8], force: ForceCondition) -> Result<Option<Verifier>> {
        let s = program.schedule.clone();
        ensure!(move1.len() == s.bytes(1), "move 1 is {} bytes, not {}", move1.len(), s.bytes(1));
        let d = format!("{}/", dir.display());
        std::fs::create_dir_all(&d)?;
        let msgs = vec![move1.to_vec()];
        let (last_step, last_hash) = View { s: &s, msgs: &msgs }.claim();
        let challenge = verifier_check_execution(&program.pdf, input.to_vec(), &d, &d, last_step, &hex::encode(last_hash), force, None, false).map_err(emu)?;
        if challenge.is_none() {
            return Ok(None);
        }
        Ok(Some(Verifier { pdf: program.pdf.clone(), dir: d, s, info: program.info.clone(), input: input.to_vec(), msgs }))
    }
    /// The hub's choice after Alice's latest round (`signed`, her move as
    /// read; `None` right after move 1, already taken).
    pub fn choose(&mut self, signed: Option<&[u8]>) -> Result<Vec<u8>> {
        if let Some(m) = signed {
            let d = self.msgs.len() as u32 + 1;
            ensure!(m.len() == self.s.bytes(d), "Alice's move at depth {d} is {} bytes", m.len());
            self.msgs.push(m.to_vec());
        }
        let d = self.msgs.len() as u32;
        let r = (d + 1) / 2;
        let last = self.msgs.last().unwrap();
        let posted = if d == 1 { &last[CLAIM_BYTES..] } else { &last[..] };
        let c = verifier_choose_segment(&self.pdf, &self.dir, &self.dir, r as u8, h20s(posted), None, NArySearchType::ConflictStep).map_err(emu)?;
        ensure!(c < self.s.segments(r), "BitVMX chose {c} of {} segments", self.s.segments(r));
        let m = vec![c as u8];
        self.msgs.push(m.clone());
        Ok(m)
    }
    /// Alice's last move as signed: the rule that applies, if any, as
    /// BitVMX's verifier chooses it. `proves` runs her proof (her class's
    /// leaf on her signed move) when none applies.
    pub fn verdict(&mut self, signed: &[u8], proves: &dyn Fn(&Record) -> bool) -> Result<Verdict> {
        ensure!(signed.len() == self.s.bytes(self.s.depths()), "the last move is {} bytes", signed.len());
        self.msgs.push(signed.to_vec());
        let v = View { s: &self.s, msgs: &self.msgs };
        let (rec, sh, nh) = (v.record(), v.step_hash(), v.next_hash());
        let t = u64::from(rec.step);
        // under a jump list: the long jump's hash she committed to, against
        // the hub's own
        if let Some(j) = self.s.jump {
            if u64::from(v.succ()) == t + 1 {
                let y = j.jump(t + 1);
                let mine = if y == t { sh } else { self.hashes_at(&[y])?[&y].0 };
                if v.jump_hash() != mine {
                    return Ok(Verdict::Path { kind: PathKind::Jump, y });
                }
            }
        }
        let ch = verifier_choose_challenge(&self.pdf, &self.dir, &self.dir, trace_of(&rec), &hex::encode(sh), &hex::encode(nh), ForceChallenge::No, None, false).map_err(emu)?;
        let words = lngap_zk::final_d60::input_words(&self.input);
        let d = |n: String| Ok(Verdict::Disprove(n, vec![]));
        match ch {
            ChallengeType::EquivocationResign { kind, expected_round, expected_index, .. } => {
                let k = if kind == EquivocationKind::StepHash { "step" } else { "next" };
                d(format!("equiv_{k}_{expected_round}_{}", expected_index - 1))
            }
            ChallengeType::Halt { .. } => {
                let (last_step, last_hash) = v.claim();
                ensure!(u64::from(rec.step) + 1 == last_step, "BitVMX chose halt off the last step");
                if nh != last_hash {
                    d("halt_hash".into())
                } else {
                    d("halt_exit".into())
                }
            }
            ChallengeType::TraceHashZero { .. } if sh != lngap_zk::game::initial_hash() => d("initial".into()),
            ChallengeType::TraceHash { .. } | ChallengeType::TraceHashZero { .. } => Ok(Verdict::Wait),
            ChallengeType::AddressesSections { .. } => d("addresses_sections".into()),
            ChallengeType::EntryPoint { .. } => d("entry_point".into()),
            ChallengeType::ProgramCounter { pre_hash, trace, .. } => {
                let w = lngap_zk::Step { write_addr: trace.write_1.address, write_value: trace.write_1.value, pc: trace.write_pc.get_address(), micro: trace.write_pc.get_micro() };
                Ok(Verdict::Disprove("program_counter".into(), lngap_zk::final_d60::program_counter_wit(&h20(&pre_hash)?, &w)))
            }
            ChallengeType::Opcode { chunk_index, .. } => d(format!("opcode_{chunk_index}")),
            ChallengeType::InputData { address, .. } => {
                let j = ((address - self.info.input_base) / 4) as usize;
                ensure!(j < words.len(), "an input address beyond the input");
                d(format!("input_{j}"))
            }
            ChallengeType::InitializedData { read_selector, chunk_index, .. } => d(format!("initialized_{chunk_index}_{read_selector}")),
            ChallengeType::UninitializedData { read_selector, .. } => d(format!("uninitialized_{read_selector}")),
            ChallengeType::FutureRead { read_selector, .. } => d(format!("future_read_{read_selector}")),
            ChallengeType::ReadValueNArySearch { .. } if self.s.jump.is_some() => {
                // BitVMX's step to challenge: her last write, or the hub's, the
                // later if both name one
                let mine = self.trace_at(t + 1)?;
                let never = bitvmx_cpu_definitions::constants::LAST_STEP_INIT;
                let (r, ls, my) = if rec.read.read_1_value != mine.read_1.value { (1, rec.last_step_1, mine.read_1.last_step) } else { (2, rec.last_step_2, mine.read_2.last_step) };
                let y = if ls == never { my } else if my == never { ls } else { ls.max(my) };
                Ok(Verdict::Path { kind: PathKind::Read(r), y })
            }
            ChallengeType::ReadValueNArySearch { .. } => Ok(Verdict::ReadChallenge),
            ChallengeType::No => Ok(if proves(&rec) { Verdict::Proved } else { Verdict::Wait }),
            other => bail!("BitVMX chose {other:?}, which the ladder doesn't carry"),
        }
    }
}

impl Verifier {
    fn hashes_at(&self, steps: &[u64]) -> Result<std::collections::BTreeMap<u64, ([u8; 20], lngap_zk::Step)>> {
        hashes_at(&self.pdf, &self.dir, &self.input, steps, None)
    }
    fn trace_at(&self, x: u64) -> Result<TraceRWStep> {
        let pd = ProgramDefinition::from_config(&self.pdf).map_err(|e| anyhow!("{e:?}"))?;
        let (_, trace) = pd.execute_helper(&self.dir, &self.dir, self.input.clone(), Some(vec![x]), None, false).map_err(emu)?;
        trace.into_iter().map(|(t, _)| t).find(|t| t.step_number == x).context("the step")
    }
    /// The path from the agreed step back to `y` over the hub's history,
    /// and `y`'s preimage (the verdict's witness).
    pub fn path(&self, y: u64) -> Result<(HopPath, Vec<u8>)> {
        let j = self.s.jump.context("a jump list")?;
        let t = u64::from(View { s: &self.s, msgs: &self.msgs }.record().step);
        let hops = j.path(t, y);
        let mut steps: Vec<u64> = hops.iter().map(|h| h.1).collect();
        steps.extend([t, y, j.jump(y.max(1))]);
        if y > 0 {
            steps.push(y - 1);
        }
        let at = self.hashes_at(&steps)?;
        let path = HopPath { types: hops.iter().map(|h| h.0).collect(), hashes: hops.iter().map(|h| at[&h.1].0).collect() };
        Ok((path, preimage_at(&j, y, &at)))
    }
    /// Hop `k`'s preimage (`h(x_k)`'s), for its reveal.
    pub fn reveal(&self, path: &HopPath, k: usize) -> Result<Vec<u8>> {
        let j = self.s.jump.context("a jump list")?;
        let t = u64::from(View { s: &self.s, msgs: &self.msgs }.record().step);
        let mut x = t;
        for ty in &path.types[..k] {
            x = if *ty == Hop::Long { j.jump(x) } else { x - 1 };
        }
        let at = self.hashes_at(&[x, x - 1, j.jump(x)])?;
        Ok(preimage_at(&j, x, &at))
    }
}

/// A record as BitVMX's trace (the disputed step, `t + 1`).
pub fn trace_of(r: &Record) -> TraceRWStep {
    TraceRWStep::new(
        u64::from(r.step) + 1,
        TraceRead::new(r.read.read_1_addr, r.read.read_1_value, r.last_step_1),
        TraceRead::new(r.read.read_2_addr, r.read.read_2_value, r.last_step_2),
        TraceReadPC::new(ProgramCounter::new(r.read.pc, r.read.micro), r.read.opcode),
        TraceStep::new(TraceWrite::new(r.write.write_addr, r.write.write_value), ProgramCounter::new(r.write.pc, r.write.micro)),
        (r.witness != 0).then_some(r.witness),
        MemoryWitness::from_byte(r.read.mem_witness),
    )
}
