//! ZKP verification as a venue game (DEMOS_PLAN.md section 3).
//!
//! Z1: one BitVMX terminal challenge, the trace-hash check, as an LN-GAP
//! disprove leaf. In BitVMX an execution trace is a hash chain,
//! `h_i = BLAKE3(h_{i-1} || write_i)[..20]`, where `write_i` is the step's
//! 13-byte write record (write address, write value, next pc, micro-step).
//! The prover commits to hashes; the challenger wins by showing that one
//! committed hash is not the hash of its predecessor and its step.
//!
//! Here the two values come from the parked pair of a refutation, as
//! every disprove leaf's do: the prior head carries `h_{i-1}`, the new
//! head the step record and the claimed `h_i`. The leaf re-verifies the
//! mover's Winternitz signature over the pair (leaving the 192 digits on
//! the stack), gathers the 106 digits the challenge reads in the order it
//! expects, drops the rest, and runs BitVMX's own `trace_hash_challenge`
//! script (Apache-2.0, FairgateLabs/BitVMX-CPU) unchanged.
//!
//! The head layout is Z1's: in Z2 the heads carry the n-ary search's
//! interval, and the final round's heads take this shape.

use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_stack::stack::StackTracker;
use lngap_channel::Role;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_pos::ttt::{word0, Layout, PosLeaf};

/// Head bytes (the venue's fixed head size).
pub const HEAD_BYTES: usize = 48;
/// The leaf's name.
pub const TRACE_HASH: &str = "zk_trace_hash";

/// Nibbles the BitVMX challenge reads: prev hash (40), write address,
/// write value and pc (8 each), micro (2), claimed hash (40).
pub const CHALLENGE_INPUTS: usize = 40 + 8 + 8 + 8 + 2 + 40;

/// One step's write record, as BitVMX hashes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Step {
    pub write_addr: u32,
    pub write_value: u32,
    pub pc: u32,
    pub micro: u8,
}

impl Step {
    /// The 13 bytes BitVMX hashes (big-endian words, then the micro-step).
    pub fn to_bytes(&self) -> [u8; 13] {
        let mut b = [0u8; 13];
        b[0..4].copy_from_slice(&self.write_addr.to_be_bytes());
        b[4..8].copy_from_slice(&self.write_value.to_be_bytes());
        b[8..12].copy_from_slice(&self.pc.to_be_bytes());
        b[12] = self.micro;
        b
    }
}

/// `BLAKE3(prev || step)` truncated to 20 bytes: BitVMX's step hash.
pub fn step_hash(prev: &[u8; 20], step: &Step) -> [u8; 20] {
    let mut h = blake3::Hasher::new();
    h.update(prev);
    h.update(&step.to_bytes());
    let mut out = [0u8; 20];
    h.finalize_xof().fill(&mut out);
    out
}

/// The prior head: word0, then `h_{i-1}` (head bytes 4..24).
pub fn prior_head(game_id: u16, depth: u32, mover: Role, prev: &[u8; 20]) -> [u8; HEAD_BYTES] {
    let mut h = [0u8; HEAD_BYTES];
    h[0..4].copy_from_slice(&word0(game_id, depth, mover).to_be_bytes());
    h[4..24].copy_from_slice(prev);
    h
}

/// The new head: word0, the step record (head bytes 4..17), then the
/// claimed `h_i` (head bytes 17..37).
pub fn step_head(game_id: u16, depth: u32, mover: Role, step: &Step, hash: &[u8; 20]) -> [u8; HEAD_BYTES] {
    let mut h = [0u8; HEAD_BYTES];
    h[0..4].copy_from_slice(&word0(game_id, depth, mover).to_be_bytes());
    h[4..17].copy_from_slice(&step.to_bytes());
    h[17..37].copy_from_slice(hash);
    h
}

/// Decode a new head's step record and claimed hash.
pub fn parse_step_head(h: &[u8; HEAD_BYTES]) -> (Step, [u8; 20]) {
    let w = |i: usize| u32::from_be_bytes(h[i..i + 4].try_into().unwrap());
    let step = Step { write_addr: w(4), write_value: w(8), pc: w(12), micro: h[16] };
    (step, h[17..37].try_into().unwrap())
}

/// The native mirror: the claimed hash is not the step hash of the prior
/// head's hash and the step.
pub fn trace_hash_fires(prior: &[u8; HEAD_BYTES], new: &[u8; HEAD_BYTES]) -> bool {
    let prev: [u8; 20] = prior[4..24].try_into().unwrap();
    let (step, claimed) = parse_step_head(new);
    step_hash(&prev, &step) != claimed
}

/// BitVMX's challenge script, compiled: consumes the 106 input nibbles
/// (the prev hash deepest, the claimed hash on top) and fails unless the
/// hash differs.
pub fn challenge_script() -> ScriptBuf {
    let mut st = StackTracker::new();
    bitcoin_script_riscv::riscv::challenges::trace_hash_challenge(&mut st);
    st.get_script()
}

/// The `zk_trace_hash` disprove leaf over the parked pair (depth >= 2).
///
/// Script: verify the pair signature (192 digits left, the prior head's
/// digit 0 deepest); PICK the 106 challenge inputs to the altstack, last
/// first; drop the register file; bring them back (the prev hash's first
/// nibble deepest); run the BitVMX challenge; push 1.
pub fn trace_hash_leaf(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let p = l.prior.expect("the trace-hash leaf reads a prior head: depth >= 2");
    let n = l.new;
    let file = l.file;
    // prior-head digits 8..48 are h_{i-1}; new-head digits 8..74 are the
    // step record then the claimed hash: contiguous, in BitVMX's order
    let src: Vec<usize> = (p + 8..p + 48).chain(n + 8..n + 74).collect();
    assert_eq!(src.len(), CHALLENGE_INPUTS);
    let mut b = Builder::new().wots_verify(key);
    for &j in src.iter().rev() {
        b = b.push_int((file - 1 - j) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
    }
    for _ in 0..file / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    for _ in 0..src.len() {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    let mut bytes = b.into_script().into_bytes();
    bytes.extend_from_slice(challenge_script().as_bytes());
    let mut script = ScriptBuf::from_bytes(bytes);
    script.push_opcode(OP_PUSHNUM_1);
    PosLeaf { name: TRACE_HASH.into(), script, fires: Arc::new(|p, h| trace_hash_fires(p, h)) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn head_digits_line_up() {
        // the leaf reads new-head digits 8..74: bytes 4..37
        let s = Step { write_addr: 0x1234_5678, write_value: 0x9abc_def0, pc: 0x8000_0000, micro: 3 };
        let h = step_head(1, 2, Role::User, &s, &[0xee; 20]);
        assert_eq!(parse_step_head(&h), (s, [0xee; 20]));
        assert!(h[37..].iter().all(|b| *b == 0));
    }
}
