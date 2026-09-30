//! ZKP verification as a venue game (DEMOS_PLAN.md section 3).
//!
//! Z1: BitVMX terminal challenges as LN-GAP disprove leaves. In BitVMX an
//! execution trace is a hash chain, `h_i = BLAKE3(h_{i-1} || write_i)[..20]`,
//! where `write_i` is the step's 13-byte write record (write address,
//! write value, next pc, micro-step). A search between prover and
//! challenger narrows a dispute to one step, whose record is then checked:
//!
//! - `zk_trace_hash`: the claimed `h_i` is not the hash of `h_{i-1}` and
//!   the step's write record (BitVMX's `trace_hash_challenge`, unchanged);
//! - `zk_exec_<instruction>`: the step's read record is consistent with
//!   its opcode (the instruction class, the register addresses, the memory
//!   witness: BitVMX's own assertions) and the committed write differs
//!   from the write the instruction computes (BitVMX's `execute_step`,
//!   unchanged, with its final equality inverted). One leaf per
//!   instruction class, as BitVMX has one verification script per class.
//!
//! The values come from the parked pair of a refutation, as every disprove
//! leaf's do: each leaf re-verifies the mover's Winternitz signature over
//! the pair (leaving the 192 digits on the stack), gathers the digits its
//! BitVMX script reads, in that script's order, drops the rest, and runs
//! the script (Apache-2.0, FairgateLabs/BitVMX-CPU).
//!
//! The final step's record spans both heads (88 payload bytes after the
//! two word0s), in [`FinalStep`]'s layout. In Z2 the search's last round
//! produces these heads.

use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::instruction_mapping::requires_witness;
use bitcoin_script_riscv::riscv::instructions::{execute_step, ProgramSpec};
use bitcoin_script_riscv::riscv::trace::{STraceRead, STraceStep};
use bitcoin_script_stack::stack::StackTracker;
use lngap_channel::Role;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_pos::ttt::{word0, Layout, PosLeaf};
use riscv_decode::Instruction;

/// Head bytes (the venue's fixed head size).
pub const HEAD_BYTES: usize = 48;

/// The trace-hash leaf's name.
pub const TRACE_HASH: &str = "zk_trace_hash";

/// Where the emulator puts the registers (the Groth16 ELF's layout).
pub const BASE_REGISTER_ADDRESS: u32 = 0xF000_0000;

/// One step's write record, as BitVMX hashes it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
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

/// One step's read record: the memory witness, the two reads, the pc and
/// micro-step read, and the opcode fetched.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Read {
    pub mem_witness: u8,
    pub read_1_addr: u32,
    pub read_1_value: u32,
    pub read_2_addr: u32,
    pub read_2_value: u32,
    pub pc: u32,
    pub micro: u8,
    pub opcode: u32,
}

/// The disputed step: `h_{i-1}`, its reads and write, the claimed `h_i`,
/// and the witness word division needs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FinalStep {
    pub prev_hash: [u8; 20],
    pub read: Read,
    pub write: Step,
    pub hash: [u8; 20],
    pub witness: u32,
}

// Payload byte offsets (head byte = 4 + offset; each head's bytes 0..4 are
// word0). Prior head: prev hash, then the read record up to the opcode's
// high half. New head: the opcode's low half, the write record, the
// claimed hash (contiguous after the write, as the trace hash reads
// them), the witness.
const P_PREV: usize = 0;
const P_MEMW: usize = 20;
const P_R1A: usize = 21;
const P_R1V: usize = 25;
const P_R2A: usize = 29;
const P_R2V: usize = 33;
const P_PC: usize = 37;
const P_MICRO: usize = 41;
const P_OPHI: usize = 42;
const N_OPLO: usize = 0;
const N_WADDR: usize = 2;
const N_WVAL: usize = 6;
const N_WPC: usize = 10;
const N_WMICRO: usize = 14;
const N_HASH: usize = 15;
const N_WITNESS: usize = 35;

impl FinalStep {
    /// The prior head (at depth `d - 1`, by `mover`).
    pub fn prior_head(&self, game_id: u16, depth: u32, mover: Role) -> [u8; HEAD_BYTES] {
        let mut h = [0u8; HEAD_BYTES];
        h[0..4].copy_from_slice(&word0(game_id, depth, mover).to_be_bytes());
        let p = &mut h[4..];
        let r = &self.read;
        p[P_PREV..P_PREV + 20].copy_from_slice(&self.prev_hash);
        p[P_MEMW] = r.mem_witness;
        p[P_R1A..P_R1A + 4].copy_from_slice(&r.read_1_addr.to_be_bytes());
        p[P_R1V..P_R1V + 4].copy_from_slice(&r.read_1_value.to_be_bytes());
        p[P_R2A..P_R2A + 4].copy_from_slice(&r.read_2_addr.to_be_bytes());
        p[P_R2V..P_R2V + 4].copy_from_slice(&r.read_2_value.to_be_bytes());
        p[P_PC..P_PC + 4].copy_from_slice(&r.pc.to_be_bytes());
        p[P_MICRO] = r.micro;
        p[P_OPHI..P_OPHI + 2].copy_from_slice(&r.opcode.to_be_bytes()[0..2]);
        h
    }

    /// The new head (at depth `d`, by `mover`).
    pub fn new_head(&self, game_id: u16, depth: u32, mover: Role) -> [u8; HEAD_BYTES] {
        let mut h = [0u8; HEAD_BYTES];
        h[0..4].copy_from_slice(&word0(game_id, depth, mover).to_be_bytes());
        let n = &mut h[4..];
        n[N_OPLO..N_OPLO + 2].copy_from_slice(&self.read.opcode.to_be_bytes()[2..4]);
        n[N_WADDR..N_WADDR + 13].copy_from_slice(&self.write.to_bytes());
        n[N_HASH..N_HASH + 20].copy_from_slice(&self.hash);
        n[N_WITNESS..N_WITNESS + 4].copy_from_slice(&self.witness.to_be_bytes());
        h
    }

    /// Decode a parked pair.
    pub fn parse(prior: &[u8; HEAD_BYTES], new: &[u8; HEAD_BYTES]) -> FinalStep {
        let p = &prior[4..];
        let n = &new[4..];
        let w = |b: &[u8], i: usize| u32::from_be_bytes(b[i..i + 4].try_into().unwrap());
        FinalStep {
            prev_hash: p[P_PREV..P_PREV + 20].try_into().unwrap(),
            read: Read {
                mem_witness: p[P_MEMW],
                read_1_addr: w(p, P_R1A),
                read_1_value: w(p, P_R1V),
                read_2_addr: w(p, P_R2A),
                read_2_value: w(p, P_R2V),
                pc: w(p, P_PC),
                micro: p[P_MICRO],
                opcode: u32::from_be_bytes([p[P_OPHI], p[P_OPHI + 1], n[N_OPLO], n[N_OPLO + 1]]),
            },
            write: Step { write_addr: w(n, N_WADDR), write_value: w(n, N_WVAL), pc: w(n, N_WPC), micro: n[N_WMICRO] },
            hash: n[N_HASH..N_HASH + 20].try_into().unwrap(),
            witness: w(n, N_WITNESS),
        }
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

/// The trace-hash leaf's native mirror.
pub fn trace_hash_fires(prior: &[u8; HEAD_BYTES], new: &[u8; HEAD_BYTES]) -> bool {
    let s = FinalStep::parse(prior, new);
    step_hash(&s.prev_hash, &s.write) != s.hash
}

// ----- digit selection -----

/// A word's 8 file digits (most significant first) at payload offset `off`
/// of the head at file offset `head`.
fn word_digits(head: usize, off: usize) -> impl Iterator<Item = usize> {
    let d = head + 8 + 2 * off;
    d..d + 8
}

/// A byte's 2 file digits.
fn byte_digits(head: usize, off: usize) -> impl Iterator<Item = usize> {
    let d = head + 8 + 2 * off;
    d..d + 2
}

/// A byte's low digit only (BitVMX's micro-steps are one nibble).
fn low_digit(head: usize, off: usize) -> impl Iterator<Item = usize> {
    std::iter::once(head + 8 + 2 * off + 1)
}

/// The leaf body: verify the pair signature (192 digits left, the prior
/// head's digit 0 deepest); PICK `src` to the altstack, last first; drop
/// the register file; bring them back (`src[0]` deepest); run `check`;
/// push 1.
fn leaf_script(l: &Layout, key: &WotsPublic, src: &[usize], check: &ScriptBuf) -> ScriptBuf {
    let file = l.file;
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
    bytes.extend_from_slice(check.as_bytes());
    let mut script = ScriptBuf::from_bytes(bytes);
    script.push_opcode(OP_PUSHNUM_1);
    script
}

fn offsets(l: &Layout) -> (usize, usize) {
    (l.prior.expect("the zk leaves read a prior head: depth >= 2"), l.new)
}

// ----- the trace-hash leaf -----

/// BitVMX's trace-hash challenge, compiled: consumes 106 nibbles (the prev
/// hash deepest, the claimed hash on top) and fails unless the hash
/// differs.
pub fn trace_hash_script() -> ScriptBuf {
    let mut st = StackTracker::new();
    bitcoin_script_riscv::riscv::challenges::trace_hash_challenge(&mut st);
    st.get_script()
}

/// The `zk_trace_hash` disprove leaf over the parked pair (depth >= 2).
pub fn trace_hash_leaf(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let (p, n) = offsets(l);
    // prev hash (40), then the write record and the claimed hash, which
    // sit contiguously in the new head (26 + 40)
    let d = n + 8 + 2 * N_WADDR;
    let src: Vec<usize> = (p + 8 + 2 * P_PREV..p + 8 + 2 * P_PREV + 40).chain(d..d + 66).collect();
    PosLeaf { name: TRACE_HASH.into(), script: leaf_script(l, key, &src, &trace_hash_script()), fires: Arc::new(|p, h| trace_hash_fires(p, h)) }
}

// ----- the execution leaves -----

/// The leaf name of an instruction class's execution leaf.
pub fn exec_name(key: &str) -> String {
    format!("zk_exec_{}", key.to_lowercase())
}

/// BitVMX's verification script for `instruction` at `micro`, with its
/// final comparison inverted: consumes the write record (write address,
/// value, pc: 8 nibbles each; micro: 1), the witness if the class needs
/// one (8), then the read record (memory witness 2, read 1 address and
/// value, read 2 address and value, pc: 8 each; micro 1; opcode 8, on
/// top). Fails if BitVMX's assertions fail (a read record inconsistent
/// with the opcode); otherwise succeeds iff some field of the committed
/// write differs from the computed one.
pub fn exec_script(instruction: &Instruction, micro: u8) -> ScriptBuf {
    let mut st = StackTracker::new();
    let program = ProgramSpec::new(BASE_REGISTER_ADDRESS);
    let commit = STraceStep::define(&mut st);
    let witness = requires_witness(instruction).then(|| st.define(8, "witness"));
    let read = STraceRead::define(&mut st);
    let result = execute_step(&mut st, &read, &commit, witness, instruction, micro, program).expect("a BitVMX instruction class");
    // BitVMX's compare_trace_step asserts equality field by field (micro,
    // pc, value, address); a disprove fires iff any differs. The one-nibble
    // micro is compared by hand (equality() mishandles size-1 variables).
    st.move_var(commit.micro);
    st.move_var(result.micro);
    st.op_numnotequal();
    st.to_altstack();
    for (c, r) in [(commit.program_counter, result.program_counter), (commit.write_1_value, result.write_1_value), (commit.write_1_add, result.write_1_add)] {
        st.equality(c, true, r, true, false, false);
        st.from_altstack();
        st.op_boolor();
        st.to_altstack();
    }
    st.from_altstack();
    st.op_verify();
    st.get_script()
}

/// The execution leaf for `instruction` (a representative of its class)
/// at micro-step `micro`, named `zk_exec_<key>` with BitVMX's key.
pub fn exec_leaf(l: &Layout, key: &WotsPublic, instruction: &Instruction, micro: u8, fires: Arc<dyn Fn(&[u8; HEAD_BYTES], &[u8; HEAD_BYTES]) -> bool + Send + Sync>) -> PosLeaf {
    let (p, n) = offsets(l);
    let mut src: Vec<usize> = vec![];
    src.extend(word_digits(n, N_WADDR));
    src.extend(word_digits(n, N_WVAL));
    src.extend(word_digits(n, N_WPC));
    src.extend(low_digit(n, N_WMICRO));
    if requires_witness(instruction) {
        src.extend(word_digits(n, N_WITNESS));
    }
    src.extend(byte_digits(p, P_MEMW));
    src.extend(word_digits(p, P_R1A));
    src.extend(word_digits(p, P_R1V));
    src.extend(word_digits(p, P_R2A));
    src.extend(word_digits(p, P_R2V));
    src.extend(word_digits(p, P_PC));
    src.extend(low_digit(p, P_MICRO));
    // the opcode: its high half in the prior head, its low half in the new
    let (hi, lo) = (p + 8 + 2 * P_OPHI, n + 8 + 2 * N_OPLO);
    src.extend((hi..hi + 4).chain(lo..lo + 4));
    let name = exec_name(&bitcoin_script_riscv::riscv::instruction_mapping::get_key_from_instruction_and_micro(instruction, micro));
    PosLeaf { name, script: leaf_script(l, key, &src, &exec_script(instruction, micro)), fires }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn heads_round_trip() {
        let s = FinalStep {
            prev_hash: [0x11; 20],
            read: Read { mem_witness: 0x2a, read_1_addr: 1, read_1_value: 2, read_2_addr: 3, read_2_value: 4, pc: 5, micro: 6, opcode: 0x1234_5678 },
            write: Step { write_addr: 7, write_value: 8, pc: 9, micro: 10 },
            hash: [0x22; 20],
            witness: 11,
        };
        let (p, n) = (s.prior_head(1, 1, Role::User), s.new_head(1, 2, Role::Hub));
        assert_eq!(FinalStep::parse(&p, &n), s);
        assert!(n[4 + N_WITNESS + 4..].iter().all(|b| *b == 0));
    }
}
