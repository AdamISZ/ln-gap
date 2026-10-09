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

use crate::OpensFile;
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
    // key-independent and built once per process (two per leaf otherwise)
    static S: std::sync::OnceLock<ScriptBuf> = std::sync::OnceLock::new();
    S.get_or_init(build_block_check_script).clone()
}

fn build_block_check_script() -> ScriptBuf {
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
    static S: std::sync::OnceLock<ScriptBuf> = std::sync::OnceLock::new();
    S.get_or_init(build_step_hash_script).clone()
}

fn build_step_hash_script() -> ScriptBuf {
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
pub fn prove_script_d60(l: &Layout, key: &impl OpensFile, class: &str, exec: &ScriptBuf, witness: bool) -> ScriptBuf {
    let p = l.prior.expect("depth >= 2");
    let n = l.new;
    let (s, file) = (0usize, 4 * BLOCK);
    let len = 4 * BLOCK + l.file;
    let f = |i: usize| file + i;
    let g1: Vec<usize> = block_nibbles(s, S_LO, 40);
    let mut t = Tracked::new(key.open_file(Builder::new()), len);
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
    /// Phase 1's depths, 2R + 1: the last is the disputed step's record.
    pub fn depths(&self) -> u32 {
        2 * self.rounds + 1
    }
    /// All depths with the read challenge (D62): phase 1, the verifier's
    /// opening at 2R + 2, R rounds, the prover's terminal move at 4R + 3.
    pub fn total(&self) -> u32 {
        4 * self.rounds + 3
    }
    /// The read challenge's opening depth.
    pub fn open_depth(&self) -> u32 {
        2 * self.rounds + 2
    }
    /// The round a verifier's choice at depth `d` answers, in its phase.
    pub fn choice_round(&self, d: u32) -> u32 {
        if d <= 2 * self.rounds {
            d / 2
        } else {
            (d - self.open_depth()) / 2
        }
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
        let r = self.choice_round(d);
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
        let r = self.choice_round(new.depth);
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
pub fn two_block_leaf(l: &Layout, key: &impl OpensFile, verdict: impl FnOnce(Tracked) -> Tracked, dig_a: Dig, dig_b: Dig) -> ScriptBuf {
    let file = l.file;
    let len = 4 * BLOCK + file;
    let t = Tracked::new(key.open_file(Builder::new()), len);
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
    pub fn choice_leaf(&self, key: &impl OpensFile, d: u32) -> ScriptBuf {
        let l = Layout::at(d, self.game_id, lngap_pos::instance::mover_at(d));
        let p = l.prior.expect("a choice is at depth >= 2");
        let r = self.choice_round(d);
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
    pub fn claim_leaf(&self, key: &impl OpensFile) -> ScriptBuf {
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
    pub fn copied_leaf(&self, key: &impl OpensFile, d: u32) -> ScriptBuf {
        let l = Layout::at(d, self.game_id, lngap_pos::instance::mover_at(d));
        let p = l.prior.expect("depth >= 2");
        let mut t = Tracked::new(key.open_file(Builder::new()), l.file);
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
    /// Against the claim digest the prior (verifier's) head repeats. In
    /// the read challenge (D62) that field links phase 1's record, so this
    /// block is then the record (its bytes at the record's offsets).
    Claim,
    /// Against the NEW head's state digest (a verifier's own move, D62's
    /// opening).
    NewState,
}

/// A final-depth leaf's input: a nibble of a block or of the claimant's
/// extra witness, or a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FIn {
    St(usize),
    Rec(usize),
    Cl(usize),
    Wit(usize),
    /// A nibble of the new head's state block.
    Ns(usize),
    /// A nibble of the register file (the parked heads).
    File(usize),
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
pub fn final_leaf(l: &Layout, key: &impl OpensFile, blocks: &[Blk], wit: usize, inputs: &[FIn], check: &ScriptBuf) -> ScriptBuf {
    final_leaf_pre(l, key, None, blocks, wit, inputs, check)
}

/// [`final_leaf`], first verifying a Winternitz signature under `pre`
/// whose elements sit on top of the pair reveal (D61: the prover's
/// signature on an input word); its message digits are the `FIn::Pre`
/// inputs.
pub fn final_leaf_pre(l: &Layout, key: &impl OpensFile, pre: Option<&WotsPublic>, blocks: &[Blk], wit: usize, inputs: &[FIn], check: &ScriptBuf) -> ScriptBuf {
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
            FIn::Ns(i) => Some((Blk::NewState, i)),
            _ => None,
        }
    };
    let digest_idx = |b: Blk| -> Vec<usize> {
        match b {
            Blk::State => head_nibbles(p, H_STATE, 20).into_iter().map(|i| file_at + i).collect(),
            Blk::Record => head_nibbles(l.new, H_SECOND, 20).into_iter().map(|i| file_at + i).collect(),
            Blk::Claim => head_nibbles(p, H_SECOND, 20).into_iter().map(|i| file_at + i).collect(),
            Blk::NewState => head_nibbles(l.new, H_STATE, 20).into_iter().map(|i| file_at + i).collect(),
        }
    };
    let first = blocks[0];
    // early: the first block's inputs and the witness's (both gone before
    // the checks); late: the second block's (copied when it is alone)
    let early: Vec<usize> = (0..inputs.len()).filter(|&j| matches!(inputs[j], FIn::Wit(_) | FIn::File(_)) || of(&inputs[j]).is_some_and(|(b, _)| b == first)).collect();
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
    let mut t = Tracked::new(key.open_file(b0), n * 2 * BLOCK + wit + file);
    let early_idx: Vec<usize> = early
        .iter()
        .map(|&j| match inputs[j] {
            FIn::Wit(i) => wit_at + i,
            FIn::File(i) => file_at + i,
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
            Blk::NewState => state.to_bytes(),
        }));
    }
    w.extend(nibble_witness(wit));
    w
}

// ----- the read challenge (D62): BitVMX's second search as phase 2 -----

/// A right-hand side in an equality check: another input, or a constant.
#[derive(Clone, Copy, Debug)]
pub enum Rhs {
    I(usize),
    K(u8),
}

/// A check over `n` inputs (consumed): passes iff NOT all of `eqs` hold
/// (input `a` equals the right-hand side): a disprove's verdict.
pub fn not_all_equal_script(n: usize, eqs: &[(usize, Rhs)]) -> ScriptBuf {
    let mut t = Tracked::new(Builder::new(), n);
    t.b = t.b.push_opcode(OP_PUSHNUM_1);
    t.len += 1;
    for &(a, rhs) in eqs {
        t.b = t.b.push_int((t.len - 1 - a) as i64).push_opcode(OP_PICK);
        t.len += 1;
        match rhs {
            Rhs::I(b) => t.b = t.b.push_int((t.len - 1 - b) as i64).push_opcode(OP_PICK),
            Rhs::K(v) => t.b = t.b.push_int(i64::from(v)),
        }
        t.b = t.b.push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
        t.len -= 1;
    }
    t.b = t.b.push_opcode(OP_NOT).push_opcode(OP_VERIFY);
    t.len -= 1;
    t.drop(n).b.into_script()
}

impl Search {
    /// The verifier's opening of the read challenge (depth 2R + 2), after
    /// phase 1's record: the state restarts the search (BitVMX's initial
    /// hash, base 0; the upper hash is never read, since the target is
    /// before the disputed step, and is zero) and links phase 1's record,
    /// in the state's `claim` field and the head's second field.
    pub fn open(&self, last: &Entry) -> Entry {
        let link = last.second();
        let state = State { lo: initial_hash(), hi: [0; 20], base: 0, claim: link };
        self.entry(self.open_depth(), state, link, None, None)
    }
    /// `zk_open`: the opening isn't (H0, 0, 0, the record's digest), or
    /// its head doesn't repeat the link.
    pub fn open_fires(prior: &Entry, new: &Entry) -> bool {
        let s = &new.state;
        !(s.lo == initial_hash() && s.hi == [0; 20] && s.base == 0 && s.claim == prior.second() && new.second() == s.claim)
    }
    /// The prover's terminal move (depth 4R + 3): the state copied.
    pub fn terminal(&self, prior: &Entry) -> Entry {
        self.entry(self.total(), prior.state, [0; 20], None, None)
    }

    /// `zk_open` in Script: the new head's state (one block) against the
    /// file's link fields.
    pub fn open_leaf(&self, key: &impl OpensFile) -> ScriptBuf {
        let d = self.open_depth();
        let l = Layout::at(d, self.game_id, lngap_pos::instance::mover_at(d));
        let p = l.prior.expect("depth >= 2");
        let mut inputs: Vec<FIn> = (0..2 * BLOCK).map(FIn::Ns).collect();
        inputs.extend(head_nibbles(p, H_SECOND, 20).into_iter().map(FIn::File));
        inputs.extend(head_nibbles(l.new, H_SECOND, 20).into_iter().map(FIn::File));
        let h0 = nibbles_of(&initial_hash());
        let (prior2, new2) = (2 * BLOCK, 2 * BLOCK + 40);
        let mut eqs: Vec<(usize, Rhs)> = vec![];
        eqs.extend((0..40).map(|k| (2 * S_LO + k, Rhs::K(h0[k]))));
        eqs.extend((0..40).map(|k| (2 * S_HI + k, Rhs::K(0))));
        eqs.extend((0..8).map(|k| (2 * S_BASE + k, Rhs::K(0))));
        eqs.extend((0..40).map(|k| (2 * S_CLAIM + k, Rhs::I(prior2 + k))));
        eqs.extend((0..40).map(|k| (new2 + k, Rhs::I(2 * S_CLAIM + k))));
        final_leaf(&l, key, &[Blk::NewState], 0, &inputs, &not_all_equal_script(inputs.len(), &eqs))
    }

    /// `zk_read_value_<r>` at the terminal depth: phase 1's record (the
    /// reads; against the link) and phase 2's final state (against the
    /// prior head), and the verifier's write W at the step after the
    /// state's base (26 nibbles: address, value, pc, micro byte). BitVMX's
    /// `read_value_challenge` unchanged.
    pub fn read_value_leaf(&self, key: &impl OpensFile, r: u8) -> ScriptBuf {
        let d = self.total();
        let l = Layout::at(d, self.game_id, lngap_pos::instance::mover_at(d));
        let inputs = [
            fin(FIn::Cl, R_R1A, 4),
            fin(FIn::Cl, R_R1V, 4),
            fin(FIn::Cl, R_LS1, 8),
            fin(FIn::Cl, R_R2A, 4),
            fin(FIn::Cl, R_R2V, 4),
            fin(FIn::Cl, R_LS2, 8),
            vec![FIn::K(i64::from(r))],
            fin(FIn::St, S_LO, 20),
            (0..26).map(FIn::Wit).collect(),
            fin(FIn::St, S_HI, 20),
            vec![FIn::K(0); 8],
            fin(FIn::St, S_BASE, 4),
            vec![FIn::K(0); 8],
            fin(FIn::Cl, R_STEP, 4),
        ]
        .concat();
        let mut st = bitcoin_script_stack::stack::StackTracker::new();
        bitcoin_script_riscv::riscv::challenges::read_value_challenge(&mut st);
        final_leaf(&l, key, &[Blk::Claim, Blk::State], 26, &inputs, &st.get_script())
    }

    /// `zk_correct_hash` at the terminal depth: phase 2's final state, and
    /// the verifier's hash at the base and write W after it (66 nibbles).
    /// BitVMX's `correct_hash_challenge` unchanged.
    pub fn correct_hash_leaf(&self, key: &impl OpensFile) -> ScriptBuf {
        let d = self.total();
        let l = Layout::at(d, self.game_id, lngap_pos::instance::mover_at(d));
        let inputs = [fin(FIn::St, S_LO, 20), (0..66).map(FIn::Wit).collect(), fin(FIn::St, S_HI, 20)].concat();
        let mut st = bitcoin_script_stack::stack::StackTracker::new();
        bitcoin_script_riscv::riscv::challenges::correct_hash_challenge(&mut st);
        final_leaf(&l, key, &[Blk::State], 66, &inputs, &st.get_script())
    }
}

/// The verifier's write as BitVMX's challenges take it (13 bytes).
pub fn write_bytes(w: &Step) -> [u8; 13] {
    w.to_bytes()
}

/// `zk_read_value_<r>`'s mirror (BitVMX's `read_value_challenge`): the
/// write step (base + 1) is before the disputed step, W is the prover's
/// committed write there (it hashes lo to hi), and it contradicts read r:
/// the read names this step but W wrote elsewhere or another value, or the
/// read names an earlier step (or none) but W wrote its address.
pub fn read_value_fires(record: &Record, state: &State, w: &Step, r: u8) -> bool {
    let write_step = u64::from(state.base) + 1;
    let (addr, value, ls) =
        if r == 1 { (record.read.read_1_addr, record.read.read_1_value, record.last_step_1) } else { (record.read.read_2_addr, record.read.read_2_value, record.last_step_2) };
    let never = crate::challenges::NEVER;
    let contradicts = (ls == write_step && (w.write_addr != addr || w.write_value != value)) || ((ls == never || ls < write_step) && w.write_addr == addr);
    u64::from(state.base) < u64::from(record.step) && contradicts && crate::step_hash(&state.lo, w) == state.hi
}

/// `zk_correct_hash`'s mirror: the prover's hash at the base isn't the
/// verifier's, yet the verifier's hash and W reach the prover's next hash.
pub fn correct_hash_fires(state: &State, verifier_hash: &[u8; 20], w: &Step) -> bool {
    state.lo != *verifier_hash && crate::step_hash(verifier_hash, w) == state.hi
}

/// Phase 2's entries from BitVMX's read search, after phase 1's: the
/// opening, each round's midpoint and choice, the terminal move.
pub fn play_read(read: &crate::dispute::ReadSearched, search: &Search, phase1: &[Entry]) -> anyhow::Result<Vec<Entry>> {
    let h = |s: &str| -> anyhow::Result<[u8; 20]> { hex::decode(s)?.try_into().map_err(|_| anyhow::anyhow!("a hash is 20 bytes")) };
    anyhow::ensure!(read.rounds.len() as u32 == search.rounds, "the read search ran {} rounds", read.rounds.len());
    let mut v = vec![search.open(phase1.last().expect("phase 1 played"))];
    for (hashes, bits) in &read.rounds {
        anyhow::ensure!(hashes.len() == 1, "binary search: one hash per round");
        let mid = search.midpoint(v.last().unwrap(), h(&hashes[0])?);
        v.push(mid);
        let c = search.choice(v.last().unwrap(), *bits == 1);
        v.push(c);
    }
    let last = v.last().unwrap().clone();
    anyhow::ensure!(
        (last.state.lo, last.state.hi, u64::from(last.state.base)) == (read.step_hash, read.next_hash, read.step),
        "the game's final interval is not the read search's"
    );
    v.push(search.terminal(&last));
    Ok(v)
}
