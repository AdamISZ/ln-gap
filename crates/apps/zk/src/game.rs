//! The computation search as a channel game (D60): each head carries the
//! 20-byte BLAKE3 digest of the game's state after the move, and the entry
//! body carries the state itself (one 64-byte block). The prover moves at
//! odd depths, the verifier at even ones; with `R` rounds the game has
//! `2R + 1` depths, the last the disputed step's record.
//!
//! Head payload (head bytes 4..48): the state digest at 0..20; at 20..40
//! the prover's midpoint (depths 1 to 2R - 1), the claim block's digest
//! repeated (the verifier's depths: so that the final depth's leaves can
//! open the claim block without the state), or the record's digest (depth
//! 2R + 1); the rest zero.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_functions::hash::blake3;
use bitcoin_script_stack::stack::StackTracker;
use lngap_channel::Role;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_pos::ttt::{word0, Layout};

use crate::{blake3_160, nibble_witness, FinalStep, Read, Step, HEAD_BYTES};

/// Bytes in a block (the state, the claim block, the record).
pub const BLOCK: usize = 64;

/// Head payload offsets.
pub const H_STATE: usize = 0;
pub const H_SECOND: usize = 20;

/// The game's state after a move (D60).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct State {
    /// The agreed hash, at step `base`.
    pub lo: [u8; 20],
    /// The prover's hash at the interval's end.
    pub hi: [u8; 20],
    /// The interval's first step (round r's choice is bit R - r).
    pub base: u32,
    /// The claim block's digest.
    pub claim: [u8; 20],
}

pub const S_LO: usize = 0;
pub const S_HI: usize = 20;
pub const S_BASE: usize = 40;
pub const S_CLAIM: usize = 44;

impl State {
    pub fn to_bytes(&self) -> [u8; BLOCK] {
        let mut b = [0u8; BLOCK];
        b[S_LO..S_LO + 20].copy_from_slice(&self.lo);
        b[S_HI..S_HI + 20].copy_from_slice(&self.hi);
        b[S_BASE..S_BASE + 4].copy_from_slice(&self.base.to_be_bytes());
        b[S_CLAIM..S_CLAIM + 20].copy_from_slice(&self.claim);
        b
    }
    pub fn from_bytes(b: &[u8; BLOCK]) -> State {
        State {
            lo: b[S_LO..S_LO + 20].try_into().unwrap(),
            hi: b[S_HI..S_HI + 20].try_into().unwrap(),
            base: u32::from_be_bytes(b[S_BASE..S_BASE + 4].try_into().unwrap()),
            claim: b[S_CLAIM..S_CLAIM + 20].try_into().unwrap(),
        }
    }
    pub fn digest(&self) -> [u8; 20] {
        blake3_160(&self.to_bytes())
    }
}

/// The prover's claim, published at depth 1 (D60).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Claim {
    pub last_step: u64,
    pub last_hash: [u8; 20],
    /// The input's digest (InputData, not yet used).
    pub input: [u8; 20],
}

pub const C_LAST_STEP: usize = 0;
pub const C_LAST_HASH: usize = 8;
pub const C_INPUT: usize = 28;

impl Claim {
    pub fn to_bytes(&self) -> [u8; BLOCK] {
        let mut b = [0u8; BLOCK];
        b[C_LAST_STEP..C_LAST_STEP + 8].copy_from_slice(&self.last_step.to_be_bytes());
        b[C_LAST_HASH..C_LAST_HASH + 20].copy_from_slice(&self.last_hash);
        b[C_INPUT..C_INPUT + 20].copy_from_slice(&self.input);
        b
    }
    pub fn digest(&self) -> [u8; 20] {
        blake3_160(&self.to_bytes())
    }
}

/// The disputed step's record, published at depth 2R + 1 (D60): what the
/// state doesn't already hold.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Record {
    pub read: Read,
    pub write: Step,
    pub witness: u32,
    pub last_step_1: u64,
    pub last_step_2: u64,
    /// The last agreed step (the disputed step is the next): the state's
    /// `base`, repeated so that most final-step disproves read the record
    /// alone; `zk_record_step` holds the prover to it.
    pub step: u32,
}

pub const R_MEMW: usize = 0;
pub const R_R1A: usize = 1;
pub const R_R1V: usize = 5;
pub const R_R2A: usize = 9;
pub const R_R2V: usize = 13;
pub const R_PC: usize = 17;
pub const R_MICRO: usize = 21;
pub const R_OP: usize = 22;
pub const R_WADDR: usize = 26;
pub const R_WVAL: usize = 30;
pub const R_WPC: usize = 34;
pub const R_WMICRO: usize = 38;
pub const R_WITNESS: usize = 39;
pub const R_LS1: usize = 43;
pub const R_LS2: usize = 51;
pub const R_STEP: usize = 59;

impl Record {
    pub fn to_bytes(&self) -> [u8; BLOCK] {
        let mut b = [0u8; BLOCK];
        let r = &self.read;
        b[R_MEMW] = r.mem_witness;
        b[R_R1A..R_R1A + 4].copy_from_slice(&r.read_1_addr.to_be_bytes());
        b[R_R1V..R_R1V + 4].copy_from_slice(&r.read_1_value.to_be_bytes());
        b[R_R2A..R_R2A + 4].copy_from_slice(&r.read_2_addr.to_be_bytes());
        b[R_R2V..R_R2V + 4].copy_from_slice(&r.read_2_value.to_be_bytes());
        b[R_PC..R_PC + 4].copy_from_slice(&r.pc.to_be_bytes());
        b[R_MICRO] = r.micro;
        b[R_OP..R_OP + 4].copy_from_slice(&r.opcode.to_be_bytes());
        b[R_WADDR..R_WADDR + 13].copy_from_slice(&self.write.to_bytes());
        b[R_WITNESS..R_WITNESS + 4].copy_from_slice(&self.witness.to_be_bytes());
        b[R_LS1..R_LS1 + 8].copy_from_slice(&self.last_step_1.to_be_bytes());
        b[R_LS2..R_LS2 + 8].copy_from_slice(&self.last_step_2.to_be_bytes());
        b[R_STEP..R_STEP + 4].copy_from_slice(&self.step.to_be_bytes());
        b
    }
    pub fn digest(&self) -> [u8; 20] {
        blake3_160(&self.to_bytes())
    }
}

/// The final move's three blocks, from a final step (Z2's search output).
pub fn blocks(f: &FinalStep) -> (State, Claim, Record) {
    let claim = Claim { last_step: f.claim_last_step, last_hash: f.claim_last_hash, input: [0; 20] };
    let state = State { lo: f.prev_hash, hi: f.hash, base: f.agreed_step, claim: claim.digest() };
    let record = Record { read: f.read, write: f.write, witness: f.witness, last_step_1: f.last_step_1, last_step_2: f.last_step_2, step: f.agreed_step };
    (state, claim, record)
}

/// A head: word0, the state digest, then `second` (a midpoint or the
/// record's digest; zeros for the verifier).
pub fn head(game_id: u16, depth: u32, mover: Role, state: &[u8; 20], second: &[u8; 20]) -> [u8; HEAD_BYTES] {
    let mut h = [0u8; HEAD_BYTES];
    h[0..4].copy_from_slice(&word0(game_id, depth, mover).to_be_bytes());
    h[4 + H_STATE..4 + H_STATE + 20].copy_from_slice(state);
    h[4 + H_SECOND..4 + H_SECOND + 20].copy_from_slice(second);
    h
}

/// The final pair: the verifier's last head (the state after the last
/// choice) and the prover's record head.
pub fn final_heads(game_id: u16, depth: u32, state: &State, record: &Record) -> ([u8; HEAD_BYTES], [u8; HEAD_BYTES]) {
    let sd = state.digest();
    (head(game_id, depth - 1, lngap_pos::instance::mover_at(depth - 1), &sd, &state.claim), head(game_id, depth, lngap_pos::instance::mover_at(depth), &sd, &record.digest()))
}

/// The final leaves' witness below the pair reveal: the state, then the
/// record (each as nibbles, first deepest).
pub fn final_witness(state: &State, record: &Record) -> Vec<Vec<u8>> {
    let mut w = nibble_witness(&state.to_bytes());
    w.extend(nibble_witness(&record.to_bytes()));
    w
}

/// BLAKE3-160 of the 64-byte block below against the 40-nibble digest on
/// top; an equality verify. The block must be alone on the main stack
/// (BitVMX's gadget finds its tables by OP_DEPTH).
pub fn block_check_script() -> ScriptBuf {
    let mut st = StackTracker::new();
    let _ = st.define(BLOCK as u32 * 2, "block");
    let _ = st.define(40, "digest");
    st.to_altstack();
    let h = blake3::blake3(&mut st, BLOCK as u32, 5);
    let dg = st.from_altstack();
    st.equals(h, true, dg, true);
    st.get_script()
}

/// The step-hash check over `[prev (40), hash (40), write (26)]` (write
/// address, value, pc: 8 each; micro: 2): fails unless BLAKE3 of prev ||
/// write is the hash. The inputs must be alone on the main stack.
pub fn step_hash_script() -> ScriptBuf {
    let mut st = StackTracker::new();
    let prev = st.define(40, "prev");
    let hash = st.define(40, "hash");
    let wa = st.define(8, "write_add");
    let wd = st.define(8, "write_data");
    let wp = st.define(8, "write_pc");
    let wm = st.define(2, "write_micro");
    st.move_var(hash);
    st.to_altstack();
    st.explode(prev);
    st.explode(wa);
    st.explode(wd);
    st.explode(wp);
    st.explode(wm);
    let result = blake3::blake3(&mut st, 33, 5);
    let claimed = st.from_altstack();
    st.equals(result, true, claimed, true);
    st.get_script()
}

/// Emits a script while tracking the main stack's length, so items can be
/// PICKed by their index from the bottom.
pub struct Tracked {
    pub b: Builder,
    pub len: usize,
}

impl Tracked {
    pub fn new(b: Builder, len: usize) -> Tracked {
        Tracked { b, len }
    }
    /// PICK the item at bottom index `i` to the altstack.
    pub fn pick_alt(mut self, i: usize) -> Self {
        self.b = self.b.push_int((self.len - 1 - i) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
        self
    }
    /// PICK `idx` to the altstack, last first (so they come back in order).
    pub fn pick_all_alt(mut self, idx: &[usize]) -> Self {
        for &i in idx.iter().rev() {
            self = self.pick_alt(i);
        }
        self
    }
    pub fn from_alt(mut self, n: usize) -> Self {
        for _ in 0..n {
            self.b = self.b.push_opcode(OP_FROMALTSTACK);
        }
        self.len += n;
        self
    }
    /// Move the `n` items under the top `above` to the altstack (they come
    /// back in order).
    pub fn roll_alt(mut self, n: usize, above: usize) -> Self {
        for _ in 0..n {
            self.b = self.b.push_int(above as i64).push_opcode(OP_ROLL).push_opcode(OP_TOALTSTACK);
        }
        self.len -= n;
        self
    }
    pub fn drop(mut self, n: usize) -> Self {
        for _ in 0..n / 2 {
            self.b = self.b.push_opcode(OP_2DROP);
        }
        if n % 2 == 1 {
            self.b = self.b.push_opcode(OP_DROP);
        }
        self.len -= n;
        self
    }
    /// Append a script that consumes `consumes` items and leaves `leaves`.
    pub fn run(self, s: &ScriptBuf, consumes: usize, leaves: usize) -> Self {
        let mut bytes = self.b.into_script().into_bytes();
        bytes.extend_from_slice(s.as_bytes());
        Tracked { b: Builder::from(bytes), len: self.len - consumes + leaves }
    }
}

/// Nibble indices of payload bytes `off..off + len` of the head at file
/// offset `head`.
pub fn head_nibbles(head: usize, off: usize, len: usize) -> Vec<usize> {
    let d = head + 8 + 2 * off;
    (d..d + 2 * len).collect()
}

/// Nibble indices of block bytes `off..off + len`, the block at `base`.
fn block_nibbles(base: usize, off: usize, len: usize) -> Vec<usize> {
    (base + 2 * off..base + 2 * (off + len)).collect()
}

/// The verification script's inputs from the record, in its order: the
/// write record (micro: its low nibble), the witness if needed, the read
/// record, the opcode on top.
fn exec_inputs(r: usize, witness: bool) -> Vec<usize> {
    let mut v = block_nibbles(r, R_WADDR, 12);
    v.push(r + 2 * R_WMICRO + 1);
    if witness {
        v.extend(block_nibbles(r, R_WITNESS, 4));
    }
    v.extend(block_nibbles(r, R_MEMW, 1));
    v.extend(block_nibbles(r, R_R1A, 20));
    v.push(r + 2 * R_MICRO + 1);
    v.extend(block_nibbles(r, R_OP, 4));
    v
}

/// The prover's `zk_prove_<class>` leaf at D60's final depth: opens the
/// state (the prior head's digest: the state the last choice settled) and
/// the record (the new head's), checks the opcode and micro-step belong to
/// `class` (the guard), runs BitVMX's verification script for the class
/// on the record, and checks BLAKE3(lo || write) == hi. Witness, below
/// the pair reveal: the state, then the record.
///
/// The BLAKE3 gadget needs its block alone on the main stack, so: copy the
/// state's lo and hi out; park the record; check the state; bring the
/// record back, copy its fields out, check it; then restore lo and hi
/// below the record's fields and run the proof.
pub fn prove_script_d60(l: &Layout, key: &WotsPublic, class: &str, exec: &ScriptBuf, witness: bool) -> ScriptBuf {
    let p = l.prior.expect("depth >= 2");
    let n = l.new;
    let (s, file) = (0usize, 4 * BLOCK);
    let len = 4 * BLOCK + l.file;
    let f = |i: usize| file + i;
    let g1: Vec<usize> = block_nibbles(s, S_LO, 40);
    let mut t = Tracked::new(Builder::new().wots_verify(key), len);
    // lo and hi; the record's digest; the state's (the prior head's)
    t = t.pick_all_alt(&g1);
    t = t.pick_all_alt(&head_nibbles(n, H_SECOND, 20).into_iter().map(f).collect::<Vec<_>>());
    t = t.pick_all_alt(&head_nibbles(p, H_STATE, 20).into_iter().map(f).collect::<Vec<_>>());
    t = t.drop(l.file);
    // [state, record]: the state's digest on top, the record parked
    t = t.from_alt(40).roll_alt(2 * BLOCK, 40);
    t = t.run(&block_check_script(), 2 * BLOCK + 40, 0);
    // [record, its digest]; copy the record's fields out, check it
    t = t.from_alt(2 * BLOCK).from_alt(40);
    let mut g2: Vec<usize> = block_nibbles(0, R_WADDR, 12);
    g2.extend(block_nibbles(0, R_WMICRO, 1));
    g2.extend(exec_inputs(0, witness));
    // the class guard's inputs: the opcode, the micro-step (on top)
    g2.extend(block_nibbles(0, R_OP, 4));
    g2.push(2 * R_MICRO + 1);
    let n2 = g2.len();
    t = t.pick_all_alt(&g2);
    t = t.run(&block_check_script(), 2 * BLOCK + 40, 0);
    // [write26, exec..., lo, hi] -> [lo, hi, write26, exec...]
    t = t.from_alt(n2).from_alt(80);
    for _ in 0..n2 {
        t.b = t.b.push_int((n2 + 80 - 1) as i64).push_opcode(OP_ROLL);
    }
    t = t.run(&crate::guard::class_guard_script(class), 9, 0);
    let exec_n = n2 - 26 - 9;
    t = t.run(exec, exec_n, 0);
    t = t.run(&step_hash_script(), 106, 0);
    let mut script = t.b.into_script();
    script.push_opcode(OP_PUSHNUM_1);
    script
}

// ----- the game natively (step 2): moves, rules, the members' check -----

/// BitVMX's initial step hash (the state's `lo` at the claim).
pub fn initial_hash() -> [u8; 20] {
    bitvmx_cpu_definitions::trace::generate_initial_step_hash().try_into().expect("20 bytes")
}

/// One sealed move: its head and the preimages its body carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub depth: u32,
    pub head: [u8; HEAD_BYTES],
    pub state: State,
    /// At depth 1.
    pub claim: Option<Claim>,
    /// At the final depth.
    pub record: Option<Record>,
}

impl Entry {
    /// The body: the state, then the claim block or the record if any.
    pub fn body(&self) -> Vec<u8> {
        let mut b = self.state.to_bytes().to_vec();
        if let Some(c) = &self.claim {
            b.extend_from_slice(&c.to_bytes());
        }
        if let Some(r) = &self.record {
            b.extend_from_slice(&r.to_bytes());
        }
        b
    }
    /// The head's second field: the midpoint or the record's digest.
    pub fn second(&self) -> [u8; 20] {
        self.head[4 + H_SECOND..4 + H_SECOND + 20].try_into().unwrap()
    }
    pub fn state_digest(&self) -> [u8; 20] {
        self.head[4 + H_STATE..4 + H_STATE + 20].try_into().unwrap()
    }
}

/// The search game's constants (D60).
#[derive(Clone, Copy, Debug)]
pub struct Search {
    pub game_id: u16,
    /// R: binary rounds; 2^R is BitVMX's `max_steps`.
    pub rounds: u32,
}

impl Search {
    /// The game's depths: 2R + 1.
    pub fn depths(&self) -> u32 {
        2 * self.rounds + 1
    }
    /// The round a verifier depth 2r answers, or a prover depth 2r - 1
    /// opens (its midpoint).
    pub fn round_of(depth: u32) -> u32 {
        depth.div_ceil(2)
    }
    /// The base bit round r's right choice sets.
    pub fn bit(&self, r: u32) -> u32 {
        1 << (self.rounds - r)
    }
    /// That bit as (nibble index from the least significant, value in it).
    pub fn base_nibble(&self, r: u32) -> (u32, u32) {
        let b = self.rounds - r;
        (b / 4, 1 << (b % 4))
    }
    fn entry(&self, depth: u32, state: State, second: [u8; 20], claim: Option<Claim>, record: Option<Record>) -> Entry {
        let head = head(self.game_id, depth, lngap_pos::instance::mover_at(depth), &state.digest(), &second);
        Entry { depth, head, state, claim, record }
    }
    /// Depth 1: the claim, with round 1's midpoint.
    pub fn claim(&self, claim: Claim, mid: [u8; 20]) -> Entry {
        let state = State { lo: initial_hash(), hi: claim.last_hash, base: 0, claim: claim.digest() };
        self.entry(1, state, mid, Some(claim), None)
    }
    /// The verifier's choice at depth 2r: left (lo, mid) or right (mid, hi).
    pub fn choice(&self, prior: &Entry, right: bool) -> Entry {
        let d = prior.depth + 1;
        let r = d / 2;
        let (s, mid) = (prior.state, prior.second());
        let state = if right { State { lo: mid, base: s.base | self.bit(r), ..s } } else { State { hi: mid, ..s } };
        self.entry(d, state, state.claim, None, None)
    }
    /// The prover's next midpoint at depth 2r + 1 (r < R).
    pub fn midpoint(&self, prior: &Entry, mid: [u8; 20]) -> Entry {
        self.entry(prior.depth + 1, prior.state, mid, None, None)
    }
    /// The prover's final move at depth 2R + 1: the record.
    pub fn final_move(&self, prior: &Entry, record: Record) -> Entry {
        self.entry(prior.depth + 1, prior.state, record.digest(), None, Some(record))
    }

    // the rules: each disprove kind's semantics (its leaf's mirror)

    /// `zk_claim`: with the claim block opening the state's `claim`, the
    /// state isn't (H0, the claimed last hash, base 0).
    pub fn claim_fires(e: &Entry, claim: &Claim) -> bool {
        let s = &e.state;
        s.claim == claim.digest() && (s.lo != initial_hash() || s.hi != claim.last_hash || s.base != 0)
    }
    /// `zk_choice` at verifier depth 2r: the new state isn't one of the two
    /// halves of the prior's interval at its midpoint.
    pub fn choice_fires(&self, prior: &Entry, new: &Entry) -> bool {
        let r = new.depth / 2;
        let (s, n, mid) = (prior.state, new.state, prior.second());
        let left = n.lo == s.lo && n.hi == mid && n.base == s.base;
        // nibble-wise, as the leaf checks it: base's nibble holding bit r
        // gains the bit by addition (no carry out of the nibble), the rest
        // are unchanged
        let (k, v) = self.base_nibble(r);
        let nib = |x: u32, i: u32| (x >> (4 * i)) & 15;
        let right_base = (0..8).all(|i| if i == k { nib(n.base, i) == nib(s.base, i) + v } else { nib(n.base, i) == nib(s.base, i) });
        let right = n.lo == mid && n.hi == s.hi && right_base;
        !((left || right) && n.claim == s.claim && new.second() == n.claim)
    }
    /// `zk_record_step` at the final depth: the record's step isn't the
    /// state's base.
    pub fn record_step_fires(state: &State, record: &Record) -> bool {
        record.step != state.base
    }
    /// `zk_copied` at prover depths >= 3: the state digest isn't the
    /// prior's.
    pub fn copied_fires(prior_head: &[u8; HEAD_BYTES], new_head: &[u8; HEAD_BYTES]) -> bool {
        prior_head[4 + H_STATE..4 + H_STATE + 20] != new_head[4 + H_STATE..4 + H_STATE + 20]
    }

    /// The members' check (D60, availability): the body opens the head's
    /// digests (the state; the claim block at depth 1; the record at the
    /// final depth). Not the rules.
    pub fn body_opens(&self, depth: u32, head: &[u8; HEAD_BYTES], body: &[u8]) -> bool {
        let want = BLOCK * (1 + usize::from(depth == 1) + usize::from(depth == self.depths()));
        if body.len() != want {
            return false;
        }
        let block = |i: usize| -> [u8; BLOCK] { body[i * BLOCK..(i + 1) * BLOCK].try_into().unwrap() };
        let state = State::from_bytes(&block(0));
        if head[4 + H_STATE..4 + H_STATE + 20] != state.digest() {
            return false;
        }
        if depth == 1 && blake3_160(&block(1)) != state.claim {
            return false;
        }
        if depth == self.depths() && head[4 + H_SECOND..4 + H_SECOND + 20] != blake3_160(&block(1)) {
            return false;
        }
        true
    }
}

/// A game played to its end from BitVMX's search (a binary program
/// definition): the entries, depth 1 first, and the final step.
pub fn play(searched: &crate::dispute::Searched, search: &Search) -> anyhow::Result<Vec<Entry>> {
    let h = |s: &str| -> anyhow::Result<[u8; 20]> { hex::decode(s)?.try_into().map_err(|_| anyhow::anyhow!("a hash is 20 bytes")) };
    anyhow::ensure!(searched.rounds.len() as u32 == search.rounds, "the search ran {} rounds, the game has {}", searched.rounds.len(), search.rounds);
    let f = &searched.final_step;
    let claim = Claim { last_step: f.claim_last_step, last_hash: f.claim_last_hash, input: [0; 20] };
    let mut entries = vec![];
    for (i, (hashes, bits)) in searched.rounds.iter().enumerate() {
        anyhow::ensure!(hashes.len() == 1, "binary search: one hash per round");
        let mid = h(&hashes[0])?;
        let e = if i == 0 { search.claim(claim, mid) } else { search.midpoint(entries.last().unwrap(), mid) };
        entries.push(e);
        let c = search.choice(entries.last().unwrap(), *bits == 1);
        entries.push(c);
    }
    let (_, _, record) = blocks(f);
    let last = entries.last().unwrap();
    anyhow::ensure!(last.state.base == f.agreed_step, "the game's base {} is not the search's agreed step {}", last.state.base, f.agreed_step);
    entries.push(search.final_move(last, record));
    Ok(entries)
}

// ----- the bookkeeping disproves in Script (step 3) -----

/// Where a digest comes from: a head's payload (file nibbles), or the
/// first block's own bytes (its nibbles).
#[derive(Clone, Copy)]
pub enum Dig {
    /// The head at file offset `head`, payload offset `off`.
    Head { head: usize, off: usize },
    /// The first block, byte offset `off`.
    FirstBlock(usize),
}

/// The leaf body over two blocks below the pair reveal (`[A, B, reveal]`,
/// A deepest), after the pair signature: `verdict` (which pushes one item,
/// the rule's result, picking from A, B and the file) goes to the
/// altstack; then A is checked against `dig_a` and B against `dig_b`, each
/// alone on the main stack (BitVMX's gadget), the other parked; then the
/// verdict. Fires iff both blocks open and the verdict is true.
pub fn two_block_leaf(l: &Layout, key: &WotsPublic, verdict: impl FnOnce(Tracked) -> Tracked, dig_a: Dig, dig_b: Dig) -> ScriptBuf {
    let file = l.file;
    let len = 4 * BLOCK + file;
    let t = Tracked::new(Builder::new().wots_verify(key), len);
    let mut t = verdict(t);
    t.b = t.b.push_opcode(OP_TOALTSTACK);
    t.len -= 1;
    let idx = |d: Dig| -> Vec<usize> {
        match d {
            Dig::Head { head, off } => head_nibbles(head, off, 20).into_iter().map(|i| 4 * BLOCK + i).collect(),
            Dig::FirstBlock(off) => block_nibbles(0, off, 20),
        }
    };
    t = t.pick_all_alt(&idx(dig_b));
    t = t.pick_all_alt(&idx(dig_a));
    t = t.drop(file);
    t = t.from_alt(40).roll_alt(2 * BLOCK, 40);
    t = t.run(&block_check_script(), 2 * BLOCK + 40, 0);
    t = t.from_alt(2 * BLOCK).from_alt(40);
    t = t.run(&block_check_script(), 2 * BLOCK + 40, 0);
    t = t.from_alt(1);
    t.b.into_script()
}

/// Push (A[a + k] == B[b + k] for all k < n), AND-ed onto the item on top;
/// `a`, `b` are bottom indices.
fn and_eq_range(mut t: Tracked, a: usize, b: usize, n: usize) -> Tracked {
    for k in 0..n {
        t = Tracked { b: t.b.push_int((t.len - 1 - (a + k)) as i64).push_opcode(OP_PICK), len: t.len + 1 };
        t = Tracked { b: t.b.push_int((t.len - 1 - (b + k)) as i64).push_opcode(OP_PICK), len: t.len + 1 };
        t.b = t.b.push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
        t.len -= 2;
    }
    t
}

/// Push (item[a + k] == consts[k] for all k), AND-ed onto the top.
fn and_eq_const(mut t: Tracked, a: usize, consts: &[u8]) -> Tracked {
    for (k, &c) in consts.iter().enumerate() {
        t = Tracked { b: t.b.push_int((t.len - 1 - (a + k)) as i64).push_opcode(OP_PICK), len: t.len + 1 };
        t.b = t.b.push_int(c as i64).push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
        t.len -= 1;
    }
    t
}

fn nibbles_of(bytes: &[u8]) -> Vec<u8> {
    bytes.iter().flat_map(|b| [b >> 4, b & 15]).collect()
}

impl Search {
    /// `zk_choice` at verifier depth `d = 2r`. Witness below the reveal: the
    /// prior state, then the new state. The midpoint is read from the prior
    /// head.
    pub fn choice_leaf(&self, key: &WotsPublic, d: u32) -> ScriptBuf {
        let l = Layout::at(d, self.game_id, lngap_pos::instance::mover_at(d));
        let p = l.prior.expect("a choice is at depth >= 2");
        let r = d / 2;
        let (s, n, f) = (0usize, 2 * BLOCK, 4 * BLOCK);
        let mid = f + head_nibbles(p, H_SECOND, 20)[0];
        let (k, v) = self.base_nibble(r);
        let kpos = 2 * S_BASE + 7 - k as usize;
        let verdict = |mut t: Tracked| {
            // left: lo = lo, hi = mid, base = base
            t.b = t.b.push_opcode(OP_PUSHNUM_1);
            t.len += 1;
            t = and_eq_range(t, n + 2 * S_LO, s + 2 * S_LO, 40);
            t = and_eq_range(t, n + 2 * S_HI, mid, 40);
            t = and_eq_range(t, n + 2 * S_BASE, s + 2 * S_BASE, 8);
            // right: lo = mid, hi = hi, base gains the bit
            t.b = t.b.push_opcode(OP_PUSHNUM_1);
            t.len += 1;
            t = and_eq_range(t, n + 2 * S_LO, mid, 40);
            t = and_eq_range(t, n + 2 * S_HI, s + 2 * S_HI, 40);
            for i in 0..8 {
                let (a, b) = (n + 2 * S_BASE + i, s + 2 * S_BASE + i);
                t = Tracked { b: t.b.push_int((t.len - 1 - a) as i64).push_opcode(OP_PICK), len: t.len + 1 };
                t = Tracked { b: t.b.push_int((t.len - 1 - b) as i64).push_opcode(OP_PICK), len: t.len + 1 };
                if 2 * S_BASE + i == kpos {
                    t.b = t.b.push_int(v as i64).push_opcode(OP_ADD);
                }
                t.b = t.b.push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
                t.len -= 2;
            }
            t.b = t.b.push_opcode(OP_BOOLOR);
            t.len -= 1;
            // and the claim copied, and repeated in the head
            t = and_eq_range(t, n + 2 * S_CLAIM, s + 2 * S_CLAIM, 40);
            t = and_eq_range(t, f + head_nibbles(l.new, H_SECOND, 20)[0], n + 2 * S_CLAIM, 40);
            t.b = t.b.push_opcode(OP_NOT);
            t
        };
        two_block_leaf(&l, key, verdict, Dig::Head { head: p, off: H_STATE }, Dig::Head { head: l.new, off: H_STATE })
    }

    /// `zk_claim` at depth 1. Witness below the reveal: the state, then the
    /// claim block (opened against the state's `claim`).
    pub fn claim_leaf(&self, key: &WotsPublic) -> ScriptBuf {
        let l = Layout::at(1, self.game_id, lngap_pos::instance::mover_at(1));
        let (s, c) = (0usize, 2 * BLOCK);
        let h0 = nibbles_of(&initial_hash());
        let verdict = |mut t: Tracked| {
            t.b = t.b.push_opcode(OP_PUSHNUM_1);
            t.len += 1;
            t = and_eq_const(t, s + 2 * S_LO, &h0);
            t = and_eq_range(t, s + 2 * S_HI, c + 2 * C_LAST_HASH, 40);
            t = and_eq_const(t, s + 2 * S_BASE, &[0; 8]);
            t.b = t.b.push_opcode(OP_NOT);
            t
        };
        two_block_leaf(&l, key, verdict, Dig::Head { head: l.new, off: H_STATE }, Dig::FirstBlock(S_CLAIM))
    }

    /// `zk_copied` at prover depth `d >= 3`: the head's state digest isn't
    /// the prior head's. No witness below the reveal.
    pub fn copied_leaf(&self, key: &WotsPublic, d: u32) -> ScriptBuf {
        let l = Layout::at(d, self.game_id, lngap_pos::instance::mover_at(d));
        let p = l.prior.expect("depth >= 2");
        let mut t = Tracked::new(Builder::new().wots_verify(key), l.file);
        t.b = t.b.push_opcode(OP_PUSHNUM_1);
        t.len += 1;
        t = and_eq_range(t, head_nibbles(l.new, H_STATE, 20)[0], head_nibbles(p, H_STATE, 20)[0], 40);
        t.b = t.b.push_opcode(OP_NOT).push_opcode(OP_TOALTSTACK);
        t.len -= 1;
        t = t.drop(l.file);
        t = t.from_alt(1);
        t.b.into_script()
    }
}

// ----- final-depth leaves over the blocks (step 4) -----

/// A block the final move's leaves can open.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Blk {
    /// Against the prior head's state digest (the state the last choice
    /// settled).
    State,
    /// Against the final head's record digest.
    Record,
    /// Against the claim digest the prior (verifier's) head repeats.
    Claim,
}

/// A final-depth leaf's input: a nibble of a block or of the claimant's
/// extra witness, or a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FIn {
    St(usize),
    Rec(usize),
    Cl(usize),
    Wit(usize),
    /// A digit of the signed message verified first (D61: an input word).
    Pre(usize),
    K(i64),
}

/// The nibbles of block bytes `off..off + len`, as inputs.
pub fn fin(f: fn(usize) -> FIn, off: usize, len: usize) -> Vec<FIn> {
    (2 * off..2 * (off + len)).map(f).collect()
}

/// A leaf at the final depth over one or two blocks (`blocks`, first
/// deepest in the witness), then `wit` nibbles of the claimant's own
/// witness, then the pair reveal: each block is checked against its digest
/// alone on the main stack (BitVMX's gadget), its inputs copied out just
/// before; then the inputs are arranged in `inputs`' order (constants
/// pushed) and `check` runs; then 1.
pub fn final_leaf(l: &Layout, key: &WotsPublic, blocks: &[Blk], wit: usize, inputs: &[FIn], check: &ScriptBuf) -> ScriptBuf {
    final_leaf_pre(l, key, None, blocks, wit, inputs, check)
}

/// [`final_leaf`], first verifying a Winternitz signature under `pre`
/// whose elements sit on top of the pair reveal (D61: the prover's
/// signature on an input word); its message digits are the `FIn::Pre`
/// inputs.
pub fn final_leaf_pre(l: &Layout, key: &WotsPublic, pre: Option<&WotsPublic>, blocks: &[Blk], wit: usize, inputs: &[FIn], check: &ScriptBuf) -> ScriptBuf {
    assert!(matches!(blocks.len(), 1 | 2), "one or two blocks: three don't fit under the stack limit");
    let p = l.prior.expect("the final depth reads a prior head");
    let n = blocks.len();
    let file = l.file;
    let (wit_at, file_at) = (n * 2 * BLOCK, n * 2 * BLOCK + wit);
    let of = |x: &FIn| -> Option<(Blk, usize)> {
        match *x {
            FIn::St(i) => Some((Blk::State, i)),
            FIn::Rec(i) => Some((Blk::Record, i)),
            FIn::Cl(i) => Some((Blk::Claim, i)),
            _ => None,
        }
    };
    let digest_idx = |b: Blk| -> Vec<usize> {
        match b {
            Blk::State => head_nibbles(p, H_STATE, 20).into_iter().map(|i| file_at + i).collect(),
            Blk::Record => head_nibbles(l.new, H_SECOND, 20).into_iter().map(|i| file_at + i).collect(),
            Blk::Claim => head_nibbles(p, H_SECOND, 20).into_iter().map(|i| file_at + i).collect(),
        }
    };
    let first = blocks[0];
    // early: the first block's inputs and the witness's (both gone before
    // the checks); late: the second block's (copied when it is alone)
    let early: Vec<usize> = (0..inputs.len()).filter(|&j| matches!(inputs[j], FIn::Wit(_)) || of(&inputs[j]).is_some_and(|(b, _)| b == first)).collect();
    let late: Vec<usize> = (0..inputs.len()).filter(|&j| n == 2 && of(&inputs[j]).is_some_and(|(b, _)| b == blocks[1])).collect();
    for x in inputs {
        if let Some((b, _)) = of(x) {
            assert!(blocks.contains(&b), "input {x:?} from a block the leaf doesn't open");
        }
    }
    let mut b0 = Builder::new();
    let pre_n = match pre {
        Some(pk) => {
            b0 = b0.wots_verify(pk);
            let m = pk.params.message_digits as usize;
            for _ in 0..m {
                b0 = b0.push_opcode(OP_TOALTSTACK);
            }
            m
        }
        None => 0,
    };
    assert!(inputs.iter().all(|x| !matches!(x, FIn::Pre(i) if *i >= pre_n)), "a Pre input beyond the signed message");
    let mut t = Tracked::new(b0.wots_verify(key), n * 2 * BLOCK + wit + file);
    let early_idx: Vec<usize> = early
        .iter()
        .map(|&j| match inputs[j] {
            FIn::Wit(i) => wit_at + i,
            x => {
                let (_, i) = of(&x).unwrap();
                i
            }
        })
        .collect();
    t = t.pick_all_alt(&early_idx);
    if n == 2 {
        t = t.pick_all_alt(&digest_idx(blocks[1]));
    }
    t = t.pick_all_alt(&digest_idx(first));
    t = t.drop(wit + file);
    t = t.from_alt(40);
    if n == 2 {
        t = t.roll_alt(2 * BLOCK, 40);
    }
    t = t.run(&block_check_script(), 2 * BLOCK + 40, 0);
    if n == 2 {
        t = t.from_alt(2 * BLOCK).from_alt(40);
        let late_idx: Vec<usize> = late.iter().map(|&j| of(&inputs[j]).unwrap().1).collect();
        t = t.pick_all_alt(&late_idx);
        t = t.run(&block_check_script(), 2 * BLOCK + 40, 0);
    }
    // restore: the late copies, the early ones, the signed digits; then
    // arrange
    t = t.from_alt(late.len()).from_alt(early.len()).from_alt(pre_n);
    let pres: Vec<usize> = (0..pre_n).map(|i| inputs.iter().position(|x| *x == FIn::Pre(i)).map_or(usize::MAX - i, |j| j)).collect();
    let mut labels: Vec<Option<usize>> = late.iter().chain(early.iter()).map(|&j| Some(j)).chain(pres.iter().map(|&j| Some(j))).collect();
    for (j, x) in inputs.iter().enumerate() {
        if let FIn::K(v) = x {
            t.b = t.b.push_int(*v);
            t.len += 1;
            labels.push(None);
        } else {
            let pos = labels.iter().position(|&l| l == Some(j)).expect("every input copied once");
            let depth = labels.len() - 1 - pos;
            if depth > 0 {
                t.b = t.b.push_int(depth as i64).push_opcode(OP_ROLL);
            }
            let lab = labels.remove(pos);
            labels.push(lab);
        }
    }
    // signed digits no input uses sit below the inputs: drop them
    let unused = labels.iter().filter(|l| l.is_some_and(|j| j >= inputs.len())).count();
    for _ in 0..unused {
        t.b = t.b.push_int(inputs.len() as i64).push_opcode(OP_ROLL).push_opcode(OP_DROP);
        t.len -= 1;
    }
    t = t.run(check, inputs.len(), 0);
    let mut script = t.b.into_script();
    script.push_opcode(OP_PUSHNUM_1);
    script
}

/// The witness below the reveal for a final leaf over `blocks`, then the
/// claimant's extra witness.
pub fn final_leaf_witness(blocks: &[Blk], state: &State, record: &Record, claim: &Claim, wit: &[u8]) -> Vec<Vec<u8>> {
    let mut w = vec![];
    for b in blocks {
        w.extend(nibble_witness(&match b {
            Blk::State => state.to_bytes(),
            Blk::Record => record.to_bytes(),
            Blk::Claim => claim.to_bytes(),
        }));
    }
    w.extend(nibble_witness(wit));
    w
}
