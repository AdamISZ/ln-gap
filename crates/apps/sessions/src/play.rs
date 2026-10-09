//! A dispute played from one side (LN-GAP v3): each party runs its own
//! BitVMX emulator on the statement program and the claim's input, with
//! its own checkpoints, and learns the other's moves only from the chain,
//! by reading the one-time signatures in the links' witnesses.
//!
//! - Alice is the [`Prover`]: her move 1 is the claim (with round 1's
//!   midpoint), each later move answers the hub's choice of half with the
//!   next midpoint, and her last move is the disputed step's record.
//! - The hub is the [`Verifier`]: on Alice's move 1 it decides whether to
//!   dispute at all (an honest hub doesn't dispute a true claim); then it
//!   chooses a half after each of her midpoints; on her record it finds the
//!   disprove that applies, if any, with the final rules' native mirrors.
//!
//! Either side checks that the other's move is the one the rules allow
//! (its head the transition of the last); a move that isn't is the other's
//! disprove (not built here: an honest party never sees one).

use std::path::Path;

use anyhow::{anyhow, bail, ensure, Context, Result};
use bitcoin::Transaction;
use emulator::decision::challenge::{prover_execute, prover_final_trace, prover_get_hashes_for_round, verifier_check_execution, verifier_choose_segment, ForceCondition};
use emulator::decision::nary_search::NArySearchType;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::final_step;
use lngap_zk::final_d60::{fires, input_fires};
use lngap_zk::game::{blocks, Claim, Entry, Record, Search, BLOCK};
use lngap_zk::HEAD_BYTES;

use crate::contract::{Contract, Program, GAME_ID};

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
    let w: Vec<Vec<u8>> = tx.input[0].witness.iter().map(|x| x.to_vec()).collect();
    ensure!(w.len() >= 4, "not a link");
    Ok(w[..w.len() - 4].to_vec())
}

/// The move a link carries (its last signature): what `key` signed.
pub fn read_move(tx: &Transaction, key: &WotsPublic) -> Result<Vec<u8>> {
    let items = link_items(tx)?;
    let n = 2 * key.params.total_digits() as usize;
    ensure!(items.len() >= n, "the link carries no move");
    read_signed(key, &items[items.len() - n..])
}

/// A move's signature items in a link, as they appear (wire order): to
/// re-reveal it in a later leaf without the mover's key.
pub fn move_wire(tx: &Transaction, key: &WotsPublic) -> Result<Vec<Vec<u8>>> {
    let items = link_items(tx)?;
    let n = 2 * key.params.total_digits() as usize;
    ensure!(items.len() >= n, "the link carries no move");
    Ok(items[items.len() - n..].to_vec())
}

/// The input words a link carries (escalate: the claim's words, below its
/// move; `inputs`: the rest), `keys` the words' keys in word order, `with`
/// the move's key if a move follows them.
pub fn read_words(tx: &Transaction, keys: &[WotsPublic], with: Option<&WotsPublic>) -> Result<Vec<u32>> {
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
pub fn word_wires(tx: &Transaction, keys: &[WotsPublic], with: Option<&WotsPublic>) -> Result<Vec<Vec<Vec<u8>>>> {
    let mut items = link_items(tx)?;
    if let Some(k) = with {
        items.truncate(items.len() - 2 * k.params.total_digits() as usize);
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

fn block(b: &[u8]) -> Result<[u8; BLOCK]> {
    b.try_into().map_err(|_| anyhow!("a block is {BLOCK} bytes"))
}

/// Alice's side.
pub struct Prover {
    pdf: String,
    dir: String,
    search: Search,
    claim_hash: String,
    claim_step: u64,
    /// The game so far, her moves and the hub's (as she checked them).
    pub entries: Vec<Entry>,
}

impl Prover {
    /// Execute the program on `input` (checkpoints under `dir`) and make
    /// move 1: the claim, with round 1's midpoint.
    pub fn start(program: &Program, input: &[u8], dir: &Path) -> Result<Prover> {
        let d = format!("{}/", dir.display());
        std::fs::create_dir_all(&d)?;
        let pdf = program.pdf.clone();
        let (_, last_step, last_hash) = prover_execute(&pdf, input.to_vec(), &d, &d, true, None, false).map_err(emu)?;
        let hashes = prover_get_hashes_for_round(&pdf, &d, &d, 1, 0, None, NArySearchType::ConflictStep).map_err(emu)?;
        let search = program.search();
        let claim = Claim { last_step, last_hash: h20(&last_hash)?, input: [0; 20] };
        let e = search.claim(claim, h20(&hashes[0])?);
        Ok(Prover { pdf, dir: d, search, claim_hash: last_hash, claim_step: last_step, entries: vec![e] })
    }
    /// Her latest move.
    pub fn last(&self) -> &Entry {
        self.entries.last().expect("move 1")
    }
    /// The hub's choice (`signed`, its move as read from the chain) and her
    /// answer: the next midpoint, or at the end the record.
    pub fn answer(&mut self, signed: &[u8]) -> Result<Entry> {
        let prior = self.last().clone();
        let (left, right) = (self.search.choice(&prior, false), self.search.choice(&prior, true));
        let (chosen, decision) = if signed == right.head {
            (right, 1u32)
        } else if signed == left.head {
            (left, 0)
        } else {
            bail!("the hub's move at depth {} is neither half (zk_choice disproves it)", prior.depth + 1);
        };
        let round = chosen.depth / 2;
        let next = if round < self.search.rounds {
            let hashes = prover_get_hashes_for_round(&self.pdf, &self.dir, &self.dir, (round + 1) as u8, decision, None, NArySearchType::ConflictStep).map_err(emu)?;
            self.search.midpoint(&chosen, h20(&hashes[0])?)
        } else {
            let (trace, step_hash, next_hash, step) = prover_final_trace(&self.pdf, &self.dir, &self.dir, decision + 1, None)
                .map_err(emu)?
                .as_final_trace_with_hashes_and_step()
                .map_err(|e| anyhow!("{e:?}"))?;
            ensure!(trace.step_number == step + 1, "the final trace is of step {}, the last agreed {step}", trace.step_number);
            let f = final_step(&trace, &step_hash, &next_hash, self.claim_step, &self.claim_hash)?;
            self.search.final_move(&chosen, blocks(&f).2)
        };
        self.entries.push(chosen);
        self.entries.push(next.clone());
        Ok(next)
    }
}

/// The hub's side.
pub struct Verifier {
    pdf: String,
    dir: String,
    search: Search,
    info: ProgramInfo,
    input: Vec<u8>,
    claim: Claim,
    /// The game so far.
    pub entries: Vec<Entry>,
}

/// What the hub does at the end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The disprove that applies (its leaf name, without `disprove_`).
    Disprove(String),
    /// None applies: Alice's record is a valid step; she can prove it.
    Proved,
}

impl Verifier {
    /// Alice's move 1 as signed (its head, then the claim block), on the
    /// claim's `input` (checkpoints under `dir`): `None` if the hub
    /// doesn't dispute (the claim is true, unless `force`).
    pub fn start(program: &Program, input: &[u8], dir: &Path, move1: &[u8], force: ForceCondition) -> Result<Option<Verifier>> {
        ensure!(move1.len() == HEAD_BYTES + BLOCK, "move 1 is a head and a claim block");
        let d = format!("{}/", dir.display());
        std::fs::create_dir_all(&d)?;
        let search = program.search();
        let claim = Claim::from_bytes(&block(&move1[HEAD_BYTES..])?);
        let mid: [u8; 20] = move1[4 + 20..4 + 40].try_into().unwrap();
        let e = search.claim(claim, mid);
        ensure!(e.head[..] == move1[..HEAD_BYTES], "move 1's head isn't its claim's (zk_claim disproves it)");
        let challenge = verifier_check_execution(&program.pdf, input.to_vec(), &d, &d, claim.last_step, &hex::encode(claim.last_hash), force, None, false).map_err(emu)?;
        if challenge.is_none() {
            return Ok(None);
        }
        Ok(Some(Verifier { pdf: program.pdf.clone(), dir: d, search, info: program.info.clone(), input: input.to_vec(), claim, entries: vec![e] }))
    }
    /// The hub's choice after Alice's latest midpoint (`signed`, her move as
    /// read; `None` right after move 1, already taken).
    pub fn choose(&mut self, signed: Option<&[u8]>) -> Result<Entry> {
        if let Some(head) = signed {
            let last = self.entries.last().unwrap().clone();
            let mid: [u8; 20] = head[4 + 20..4 + 40].try_into().unwrap();
            let e = self.search.midpoint(&last, mid);
            ensure!(e.head[..] == head[..HEAD_BYTES], "Alice's move at depth {} doesn't copy the state (zk_copied disproves it)", e.depth);
            self.entries.push(e);
        }
        let prior = self.entries.last().unwrap().clone();
        let round = prior.depth.div_ceil(2);
        let decision = verifier_choose_segment(&self.pdf, &self.dir, &self.dir, round as u8, vec![hex::encode(prior.second())], None, NArySearchType::ConflictStep).map_err(emu)?;
        let e = self.search.choice(&prior, decision == 1);
        self.entries.push(e.clone());
        Ok(e)
    }
    /// Alice's last move as signed (its head, then the record): the
    /// disprove that applies, if any.
    pub fn verdict(&mut self, signed: &[u8], disproves: &[String]) -> Result<Verdict> {
        ensure!(signed.len() == HEAD_BYTES + BLOCK, "the last move is a head and a record");
        let record = Record::from_bytes(&block(&signed[HEAD_BYTES..])?);
        let last = self.entries.last().unwrap().clone();
        let e = self.search.final_move(&last, record);
        ensure!(e.head[..] == signed[..HEAD_BYTES], "the last move's head isn't its record's");
        self.entries.push(e);
        let words = lngap_zk::final_d60::input_words(&self.input);
        for name in disproves {
            let fired = if let Some(j) = name.strip_prefix("zk_input_") {
                let j: usize = j.parse()?;
                input_fires(&record, &self.info, j, words[j])
            } else if name == "zk_program_counter" {
                false // needs the step before the agreed one (not built)
            } else {
                fires(name, &self.info, &last.state, &record, &self.claim, &[])
            };
            if fired {
                return Ok(Verdict::Disprove(name.clone()));
            }
        }
        Ok(Verdict::Proved)
    }
    /// The claim (for the disproves' witnesses).
    pub fn claim(&self) -> Claim {
        self.claim
    }
}

/// The witness of the final-depth disprove `name` (without `disprove_`):
/// the blocks it opens, as nibbles in its order, then `file` (the last two
/// moves' signatures as read from the chain). Only the disproves that need
/// no further witness.
pub fn disprove_witness(contract: &Contract, program: &Program, name: &str, state: &lngap_zk::game::State, record: &Record, claim: &Claim, file: Vec<Vec<u8>>) -> Result<Vec<Vec<u8>>> {
    use lngap_zk::game::Blk;
    let m = contract.m();
    let moves = &contract.spec.moves;
    let key = lngap_zk::LeanFile { prior: Some(moves[(m - 2) as usize].clone()), new: moves[(m - 1) as usize].clone() };
    let l = lngap_pos::ttt::Layout::at(m, GAME_ID, lngap_pos::instance::mover_at(m));
    let leaf = lngap_zk::final_d60::final_leaves(&l, &key, &program.info).into_iter().find(|f| f.name == name).with_context(|| format!("no final disprove {name}"))?;
    ensure!(leaf.wit == 0, "{name} needs a further witness (not built)");
    let mut w = vec![];
    for b in &leaf.blocks {
        let bytes = match b {
            Blk::State => state.to_bytes(),
            Blk::Record => record.to_bytes(),
            Blk::Claim => claim.to_bytes(),
            other => bail!("{name} opens {other:?} (not built)"),
        };
        w.extend(lngap_zk::nibble_witness(&bytes));
    }
    w.extend(file);
    Ok(w)
}
