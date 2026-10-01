//! The computation search as a channel game (D60): each head carries the
//! 20-byte BLAKE3 digest of the game's state after the move, and the entry
//! body carries the state itself (one 64-byte block). The prover moves at
//! odd depths, the verifier at even ones; with `R` rounds the game has
//! `2R + 1` depths, the last the disputed step's record.
//!
//! Head payload (head bytes 4..48): the state digest at 0..20; the prover's
//! midpoint (depths 1 to 2R - 1) or the record's digest (depth 2R + 1) at
//! 20..40; the rest zero.

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
        b
    }
    pub fn digest(&self) -> [u8; 20] {
        blake3_160(&self.to_bytes())
    }
}

/// The final move's three blocks, from a final step (Z2's search output).
pub fn blocks(f: &FinalStep) -> (State, Claim, Record) {
    let claim = Claim {
        last_step: f.claim_last_step,
        last_hash: f.claim_last_hash,
        input: [0; 20],
    };
    let state = State {
        lo: f.prev_hash,
        hi: f.hash,
        base: f.agreed_step,
        claim: claim.digest(),
    };
    let record = Record {
        read: f.read,
        write: f.write,
        witness: f.witness,
        last_step_1: f.last_step_1,
        last_step_2: f.last_step_2,
    };
    (state, claim, record)
}

/// A head: word0, the state digest, then `second` (a midpoint or the
/// record's digest; zeros for the verifier).
pub fn head(
    game_id: u16,
    depth: u32,
    mover: Role,
    state: &[u8; 20],
    second: &[u8; 20],
) -> [u8; HEAD_BYTES] {
    let mut h = [0u8; HEAD_BYTES];
    h[0..4].copy_from_slice(&word0(game_id, depth, mover).to_be_bytes());
    h[4 + H_STATE..4 + H_STATE + 20].copy_from_slice(state);
    h[4 + H_SECOND..4 + H_SECOND + 20].copy_from_slice(second);
    h
}

/// The final pair: the verifier's last head (the state after the last
/// choice) and the prover's record head.
pub fn final_heads(
    game_id: u16,
    depth: u32,
    state: &State,
    record: &Record,
) -> ([u8; HEAD_BYTES], [u8; HEAD_BYTES]) {
    let sd = state.digest();
    (
        head(
            game_id,
            depth - 1,
            lngap_pos::instance::mover_at(depth - 1),
            &sd,
            &[0; 20],
        ),
        head(
            game_id,
            depth,
            lngap_pos::instance::mover_at(depth),
            &sd,
            &record.digest(),
        ),
    )
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
        self.b = self
            .b
            .push_int((self.len - 1 - i) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_TOALTSTACK);
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
            self.b = self
                .b
                .push_int(above as i64)
                .push_opcode(OP_ROLL)
                .push_opcode(OP_TOALTSTACK);
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
        Tracked {
            b: Builder::from(bytes),
            len: self.len - consumes + leaves,
        }
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
pub fn prove_script_d60(
    l: &Layout,
    key: &WotsPublic,
    class: &str,
    exec: &ScriptBuf,
    witness: bool,
) -> ScriptBuf {
    let p = l.prior.expect("depth >= 2");
    let n = l.new;
    let (s, file) = (0usize, 4 * BLOCK);
    let len = 4 * BLOCK + l.file;
    let f = |i: usize| file + i;
    let g1: Vec<usize> = block_nibbles(s, S_LO, 40);
    let mut t = Tracked::new(Builder::new().wots_verify(key), len);
    // lo and hi; the record's digest; the state's (the prior head's)
    t = t.pick_all_alt(&g1);
    t = t.pick_all_alt(
        &head_nibbles(n, H_SECOND, 20)
            .into_iter()
            .map(f)
            .collect::<Vec<_>>(),
    );
    t = t.pick_all_alt(
        &head_nibbles(p, H_STATE, 20)
            .into_iter()
            .map(f)
            .collect::<Vec<_>>(),
    );
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
