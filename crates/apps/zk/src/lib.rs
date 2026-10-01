//! ZKP verification as a venue game (DEMOS_PLAN.md section 3).
//!
//! Z1: the last step of a disputed BitVMX execution, on the LN-GAP
//! graph. In BitVMX an execution trace is a hash chain,
//! `h_i = BLAKE3(h_{i-1} || write_i)[..20]`, where `write_i` is the step's
//! 13-byte write record (write address, write value, next pc,
//! micro-step). A search between prover and challenger narrows a dispute
//! to one step, which the prover must then prove (D59): the step's read
//! record and write are what the instruction does (BitVMX's verification
//! script for the instruction class, unchanged), and its claimed hash is
//! `h_i` (BitVMX's BLAKE3, with an equality). If no proof appears in its
//! window, the claimant takes the output by timeout.
//!
//! The values come from the pair the prover's refutation parked: the
//! `zk_prove_<class>` leaf re-verifies the prover's Winternitz signature
//! over the pair (leaving the 192 digits on the stack), gathers the digits
//! BitVMX's scripts read, in their order, drops the rest, and runs them
//! (Apache-2.0, FairgateLabs/BitVMX-CPU).
//!
//! The final step's record spans both heads (88 payload bytes after the
//! two word0s), in [`FinalStep`]'s layout. In Z2 the search's last round
//! produces these heads.

pub mod challenges;
pub mod chain;
pub mod dispute;
pub mod game;
pub mod guard;

use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_functions::hash::blake3;
use bitcoin_script_riscv::riscv::instruction_mapping::{generate_verification_script, get_key_from_instruction_and_micro, requires_witness};
use bitcoin_script_stack::stack::StackTracker;
use lngap_channel::Role;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_pos::ttt::{word0, Layout, PosLeaf};
use riscv_decode::Instruction;

/// Head bytes (the venue's fixed head size).
pub const HEAD_BYTES: usize = 48;

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
/// the witness word division needs, and the fields only some challenges
/// read. Those (`hash`, the reads' last-write steps, the prover's claim)
/// are not in the heads: the new head carries the 20-byte BLAKE3 digest of
/// [`FinalStep::extra`], which travels in the entry body, and a leaf that
/// needs them takes the 64 bytes as witness nibbles and checks the digest
/// (ZK_SOUNDNESS_PLAN.md, prerequisite 1, option b).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FinalStep {
    pub prev_hash: [u8; 20],
    pub read: Read,
    pub write: Step,
    pub hash: [u8; 20],
    pub witness: u32,
    /// The last step both parties agree on (the disputed step is the next
    /// one): BitVMX's "conflict step".
    pub agreed_step: u32,
    /// The step that last wrote each read's address (`u64::MAX`: never).
    pub last_step_1: u64,
    pub last_step_2: u64,
    /// The prover's claim: the program halts with success at this step,
    /// with this final hash.
    pub claim_last_step: u64,
    pub claim_last_hash: [u8; 20],
}

// Payload byte offsets (head byte = 4 + offset; each head's bytes 0..4 are
// word0). Prior head: prev hash, then the read record up to the opcode's
// high half. New head: the opcode's low half, the write record, the digest
// of the extra data, the witness, the agreed step. Extra data (64 bytes,
// one BLAKE3 block): the claimed hash, the two last-write steps, the
// claim's last step and final hash.
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
const N_DIGEST: usize = 15;
const N_WITNESS: usize = 35;
const N_AGREED: usize = 39;
/// Bytes of extra data.
pub const EXTRA_BYTES: usize = 64;
const X_HASH: usize = 0;
const X_LS1: usize = 20;
const X_LS2: usize = 28;
const X_CLS: usize = 36;
const X_CLH: usize = 44;

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
        n[N_DIGEST..N_DIGEST + 20].copy_from_slice(&self.digest());
        n[N_WITNESS..N_WITNESS + 4].copy_from_slice(&self.witness.to_be_bytes());
        n[N_AGREED..N_AGREED + 4].copy_from_slice(&self.agreed_step.to_be_bytes());
        h
    }

    /// The extra data the new head's digest commits to.
    pub fn extra(&self) -> [u8; EXTRA_BYTES] {
        let mut x = [0u8; EXTRA_BYTES];
        x[X_HASH..X_HASH + 20].copy_from_slice(&self.hash);
        x[X_LS1..X_LS1 + 8].copy_from_slice(&self.last_step_1.to_be_bytes());
        x[X_LS2..X_LS2 + 8].copy_from_slice(&self.last_step_2.to_be_bytes());
        x[X_CLS..X_CLS + 8].copy_from_slice(&self.claim_last_step.to_be_bytes());
        x[X_CLH..X_CLH + 20].copy_from_slice(&self.claim_last_hash);
        x
    }

    /// BLAKE3 of the extra data, truncated to 20 bytes.
    pub fn digest(&self) -> [u8; 20] {
        blake3_160(&self.extra())
    }

    /// The extra data as witness nibbles (first deepest), for a leaf that
    /// reads it; they go below the pair reveal.
    pub fn extra_witness(&self) -> Vec<Vec<u8>> {
        nibble_witness(&self.extra())
    }

    /// Decode a parked pair with its extra data.
    pub fn parse_with(prior: &[u8; HEAD_BYTES], new: &[u8; HEAD_BYTES], x: &[u8; EXTRA_BYTES]) -> FinalStep {
        let q = |i: usize| u64::from_be_bytes(x[i..i + 8].try_into().unwrap());
        FinalStep {
            hash: x[X_HASH..X_HASH + 20].try_into().unwrap(),
            last_step_1: q(X_LS1),
            last_step_2: q(X_LS2),
            claim_last_step: q(X_CLS),
            claim_last_hash: x[X_CLH..X_CLH + 20].try_into().unwrap(),
            ..FinalStep::parse(prior, new)
        }
    }

    /// Decode a parked pair: the fields in the heads only (the extra
    /// data's fields are zero; see [`FinalStep::parse_with`]).
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
            hash: [0; 20],
            witness: w(n, N_WITNESS),
            agreed_step: w(n, N_AGREED),
            last_step_1: 0,
            last_step_2: 0,
            claim_last_step: 0,
            claim_last_hash: [0; 20],
        }
    }
}

/// BLAKE3, truncated to 20 bytes (BitVMX's BLAKE3-160).
pub fn blake3_160(data: &[u8]) -> [u8; 20] {
    let mut h = ::blake3::Hasher::new();
    h.update(data);
    let mut out = [0u8; 20];
    h.finalize_xof().fill(&mut out);
    out
}

/// Bytes as witness nibbles, most significant first, first deepest.
pub fn nibble_witness(bytes: &[u8]) -> Vec<Vec<u8>> {
    bytes.iter().flat_map(|b| [b >> 4, b & 15]).map(|v| if v == 0 { vec![] } else { vec![v] }).collect()
}

/// `BLAKE3(prev || step)` truncated to 20 bytes: BitVMX's step hash.
pub fn step_hash(prev: &[u8; 20], step: &Step) -> [u8; 20] {
    let mut h = ::blake3::Hasher::new();
    h.update(prev);
    h.update(&step.to_bytes());
    let mut out = [0u8; 20];
    h.finalize_xof().fill(&mut out);
    out
}

/// Whether the step's claimed hash is the step hash of its prior hash
/// and write (half of what a proof shows).
pub fn hash_holds(f: &FinalStep) -> bool {
    step_hash(&f.prev_hash, &f.write) == f.hash
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

/// A leaf input: a file digit, a nibble of the extra data, or a constant.
#[derive(Clone, Copy, Debug)]
pub enum Src {
    Dig(usize),
    X(usize),
    Konst(i64),
}

/// The extra data's nibbles for bytes `off..off + len`.
fn x_nibbles(off: usize, len: usize) -> impl Iterator<Item = Src> {
    (2 * off..2 * (off + len)).map(Src::X)
}

/// The digest check: consumes the extra data's nibbles (deepest) and the
/// 40-nibble digest (on top); fails unless BLAKE3-160 of the data is the
/// digest.
pub fn digest_check_script() -> ScriptBuf {
    let mut st = StackTracker::new();
    let _ = st.define(EXTRA_BYTES as u32 * 2, "extra");
    let _ = st.define(40, "digest");
    st.to_altstack();
    let h = blake3::blake3(&mut st, EXTRA_BYTES as u32, 5);
    let dg = st.from_altstack();
    st.equals(h, true, dg, true);
    st.get_script()
}

/// The digest's 40 file digits in the new head.
fn digest_src(n: usize) -> Vec<Src> {
    let d = n + 8 + 2 * N_DIGEST;
    (d..d + 40).map(Src::Dig).collect()
}

/// A leaf that reads the extra data: verify the pair; gather every phase's
/// inputs (file digits, extra-data nibbles, constants) to the altstack;
/// drop the register file; check the extra data against the new head's
/// digest (which consumes it); then, per phase, bring its inputs back and
/// run its script; push 1. The extra data's nibbles lie below the pair
/// reveal in the witness.
pub(crate) fn leaf_with_extra(l: &Layout, key: &WotsPublic, phases: &[(Vec<Src>, ScriptBuf)]) -> ScriptBuf {
    let mut all = vec![(digest_src(l.new), digest_check_script())];
    all.extend(phases.iter().cloned());
    leaf_phases(l, key, EXTRA_BYTES * 2, &all)
}

/// The general leaf body: `n_extra` witness nibbles below the pair reveal;
/// gather all phases' inputs, last phase first (so the first comes back
/// first), drop the file, then restore and run each phase in order.
pub(crate) fn leaf_phases(l: &Layout, key: &WotsPublic, n_extra: usize, phases: &[(Vec<Src>, ScriptBuf)]) -> ScriptBuf {
    let file = l.file;
    let mut b = Builder::new().wots_verify(key);
    for (src, _) in phases.iter().rev() {
        for s in src.iter().rev() {
            b = match *s {
                Src::Dig(j) => b.push_int((file - 1 - j) as i64).push_opcode(OP_PICK),
                Src::X(i) => {
                    assert!(i < n_extra, "extra nibble {i} of {n_extra}");
                    b.push_int((file + n_extra - 1 - i) as i64).push_opcode(OP_PICK)
                }
                Src::Konst(v) => b.push_int(v),
            }
            .push_opcode(OP_TOALTSTACK);
        }
    }
    for _ in 0..file / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    let mut bytes = b.into_script().into_bytes();
    for (src, check) in phases {
        let mut r = Builder::new();
        for _ in 0..src.len() {
            r = r.push_opcode(OP_FROMALTSTACK);
        }
        bytes.extend_from_slice(r.into_script().as_bytes());
        bytes.extend_from_slice(check.as_bytes());
    }
    let mut script = ScriptBuf::from_bytes(bytes);
    script.push_opcode(OP_PUSHNUM_1);
    script
}

/// The leaf body: verify the pair signature (192 digits left, the prior
/// head's digit 0 deepest; any extra witness items lie below them); PICK
/// `src` (or push its constants) to the altstack, last first; drop the
/// register file; bring them back (`src[0]` deepest); run `check`; push 1.
pub(crate) fn leaf_script_src(l: &Layout, key: &WotsPublic, src: &[Src], check: &ScriptBuf) -> ScriptBuf {
    leaf_phases(l, key, 0, &[(src.to_vec(), check.clone())])
}

/// The step-hash check: consumes the prev hash (40 nibbles, deepest), the
/// write record (write address, value, pc: 8 each; micro: 2) and the
/// claimed hash (40, on top); fails unless BLAKE3 of the first 33 bytes
/// is the claimed hash. BitVMX's `trace_hash_challenge` with its final
/// inequality an equality.
pub fn hash_script() -> ScriptBuf {
    let mut st = StackTracker::new();
    let prev_hash = st.define(40, "prev_hash");
    let write_add = st.define(8, "write_add");
    let write_data = st.define(8, "write_data");
    let write_pc = st.define(8, "write_pc");
    let write_micro = st.define(2, "write_micro");
    let hash = st.define(40, "hash");
    st.to_altstack();
    st.explode(prev_hash);
    st.explode(write_add);
    st.explode(write_data);
    st.explode(write_pc);
    st.explode(write_micro);
    let _ = hash;
    let result = blake3::blake3(&mut st, (40 + 8 + 8 + 8 + 2) / 2, 5);
    let claimed = st.from_altstack();
    st.equals(result, true, claimed, true);
    st.get_script()
}

/// The proof for one instruction class: BitVMX's verification script for
/// `instruction` at `micro`, unchanged (it consumes the write record, the
/// witness if the class needs one, then the read record with the opcode
/// on top, and fails unless the write is what the instruction does with
/// those reads), then [`hash_script`].
pub fn prove_script(instruction: &Instruction, micro: u8) -> ScriptBuf {
    let mut bytes = generate_verification_script(instruction, micro, BASE_REGISTER_ADDRESS, requires_witness(instruction)).into_bytes();
    bytes.extend_from_slice(hash_script().as_bytes());
    ScriptBuf::from_bytes(bytes)
}

/// The leaf name of an instruction class's proof, from BitVMX's key.
pub fn prove_name(instruction: &Instruction, micro: u8) -> String {
    format!("zk_prove_{}", get_key_from_instruction_and_micro(instruction, micro).to_lowercase())
}

/// The prover's `zk_prove_<class>` leaf over the parked pair (depth >= 2),
/// for `instruction`'s class at micro-step `micro`. `holds` is its native
/// mirror (a proof exists for the pair), which needs an executor.
pub fn prove_leaf(l: &Layout, key: &WotsPublic, instruction: &Instruction, micro: u8, holds: Arc<dyn Fn(&[u8; HEAD_BYTES], &[u8; HEAD_BYTES]) -> bool + Send + Sync>) -> PosLeaf {
    let p = l.prior.expect("the proof reads a prior head: depth >= 2");
    let n = l.new;
    // the hash check's inputs (deepest): prev hash, the write record, and
    // the claimed hash from the extra data
    let d = n + 8 + 2 * N_WADDR;
    let mut src: Vec<Src> = (p + 8 + 2 * P_PREV..p + 8 + 2 * P_PREV + 40).chain(d..d + 26).map(Src::Dig).collect();
    src.extend(x_nibbles(X_HASH, 20));
    let mut src_exec: Vec<usize> = vec![];
    let src_ref = &mut src_exec;
    // then the verification script's: the write record, the witness, the
    // read record (the opcode on top: its high half in the prior head)
    src_ref.extend(word_digits(n, N_WADDR));
    src_ref.extend(word_digits(n, N_WVAL));
    src_ref.extend(word_digits(n, N_WPC));
    src_ref.extend(low_digit(n, N_WMICRO));
    if requires_witness(instruction) {
        src_ref.extend(word_digits(n, N_WITNESS));
    }
    src_ref.extend(byte_digits(p, P_MEMW));
    src_ref.extend(word_digits(p, P_R1A));
    src_ref.extend(word_digits(p, P_R1V));
    src_ref.extend(word_digits(p, P_R2A));
    src_ref.extend(word_digits(p, P_R2V));
    src_ref.extend(word_digits(p, P_PC));
    src_ref.extend(low_digit(p, P_MICRO));
    let (hi, lo) = (p + 8 + 2 * P_OPHI, n + 8 + 2 * N_OPLO);
    src_ref.extend((hi..hi + 4).chain(lo..lo + 4));
    src.extend(src_exec.into_iter().map(Src::Dig));
    // the class guard first: the opcode and micro-step belong to the class
    let mut guard: Vec<Src> = (hi..hi + 4).chain(lo..lo + 4).map(Src::Dig).collect();
    guard.extend(low_digit(p, P_MICRO).map(Src::Dig));
    let class = get_key_from_instruction_and_micro(instruction, micro);
    let script = leaf_with_extra(l, key, &[(guard, guard::class_guard_script(&class)), (src, prove_script(instruction, micro))]);
    PosLeaf { name: prove_name(instruction, micro), script, fires: holds }
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
            agreed_step: 12,
            last_step_1: 13,
            last_step_2: u64::MAX,
            claim_last_step: 15,
            claim_last_hash: [0x33; 20],
        };
        let (p, n) = (s.prior_head(1, 1, Role::User), s.new_head(1, 2, Role::Hub));
        assert_eq!(FinalStep::parse_with(&p, &n, &s.extra()), s);
        assert_eq!(&n[4 + N_DIGEST..4 + N_DIGEST + 20], &s.digest());
        assert!(n[4 + N_AGREED + 4..].iter().all(|b| *b == 0));
    }
}
