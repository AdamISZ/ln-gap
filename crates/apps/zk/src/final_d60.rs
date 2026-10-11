//! The claimant's disproves at D60's final depth (step 4): S1 and S2
//! (`challenges.rs`) ported from the two-head layout to the blocks the
//! final move publishes, plus `zk_record_step` and the halt split. Each
//! leaf opens at most two blocks (`game::final_leaf`) and runs BitVMX's
//! challenge script unchanged.
//!
//! - `zk_record_step` (state, record): the record's step isn't the state's
//!   base.
//! - `zk_entry_point`, `zk_opcode_<k>`, `zk_addresses_sections`,
//!   `zk_future_read_<r>`, `zk_initialized_<k>_<r>`, `zk_uninitialized_<r>`
//!   (the record alone; the agreed step is the record's).
//! - `zk_program_counter` (state, record, and the claimant's witness: the
//!   hash after step i-2 and step i-1's write): the previous step wrote a
//!   different pc than the one read.
//! - Halt, split in two so that each opens two blocks; both run BitVMX's
//!   `halt_challenge` with constants in place of the fields they don't
//!   read: `zk_halt_hash` (state, claim block): the disputed step is the
//!   claimed last, and its hash isn't the claimed final hash;
//!   `zk_halt_exit` (record, claim block): the disputed step is the claimed
//!   last, and it isn't an ecall exit with 0.

use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::challenges::{
    addresses_sections_challenge, entry_point_challenge, future_read_challenge, halt_challenge, initialized_challenge, input_challenge, opcode_challenge,
    program_counter_challenge, uninitialized_challenge,
};
use bitcoin_script_stack::stack::StackTracker;
use lngap_lamport::winternitz::WotsPublic;
use lngap_pos::ttt::Layout;

use crate::OpensFile;
use crate::challenges::{ProgramInfo, NEVER};
use crate::game::*;
use crate::{FinalStep, Step};

/// A final-depth disprove: its name, the blocks its witness carries, the
/// claimant's extra witness length (nibbles), and its script.
pub struct FinalLeaf {
    pub name: String,
    pub blocks: Vec<Blk>,
    pub wit: usize,
    pub script: ScriptBuf,
}

fn tracked(f: impl FnOnce(&mut StackTracker)) -> ScriptBuf {
    let mut st = StackTracker::new();
    f(&mut st);
    st.get_script()
}

fn konst_word(v: u32) -> Vec<FIn> {
    (0..8).map(|i| FIn::K(((v >> (28 - 4 * i)) & 15) as i64)).collect()
}

fn zeros(n: usize) -> Vec<FIn> {
    vec![FIn::K(0); n]
}

/// The agreed step as BitVMX's 16 nibbles: 8 zeros, then the record's.
fn agreed16() -> Vec<FIn> {
    [zeros(8), fin(FIn::Rec, R_STEP, 4)].concat()
}

/// The two reads as BitVMX's challenges take them: address, value, last
/// write step, for read 1 then read 2.
fn reads() -> Vec<FIn> {
    [fin(FIn::Rec, R_R1A, 4), fin(FIn::Rec, R_R1V, 4), fin(FIn::Rec, R_LS1, 8), fin(FIn::Rec, R_R2A, 4), fin(FIn::Rec, R_R2V, 4), fin(FIn::Rec, R_LS2, 8)].concat()
}

fn leaf(l: &Layout, key: &impl OpensFile, name: String, blocks: &[Blk], wit: usize, inputs: &[FIn], check: &ScriptBuf) -> FinalLeaf {
    FinalLeaf { name, blocks: blocks.to_vec(), wit, script: final_leaf(l, key, blocks, wit, inputs, check) }
}

pub fn record_step_leaf(l: &Layout, key: &impl OpensFile) -> FinalLeaf {
    let inputs = [fin(FIn::St, S_BASE, 4), fin(FIn::Rec, R_STEP, 4)].concat();
    let check = tracked(|st| {
        let a = st.define(8, "base");
        let b = st.define(8, "step");
        st.not_equal(a, true, b, true);
    });
    leaf(l, key, "zk_record_step".into(), &[Blk::State, Blk::Record], 0, &inputs, &check)
}

pub fn entry_point_leaf(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> FinalLeaf {
    let inputs = [fin(FIn::Rec, R_PC, 4), fin(FIn::Rec, R_MICRO, 1), agreed16()].concat();
    let entry = info.entry;
    leaf(l, key, "zk_entry_point".into(), &[Blk::Record], 0, &inputs, &tracked(|st| entry_point_challenge(st, entry)))
}

/// The claimant's witness for `zk_program_counter`: the hash after step
/// i-2, then step i-1's write record (33 bytes).
pub fn program_counter_wit(prev_prev_hash: &[u8; 20], prev_write: &Step) -> Vec<u8> {
    let mut b = prev_prev_hash.to_vec();
    b.extend_from_slice(&prev_write.to_bytes());
    b
}

pub fn program_counter_leaf(l: &Layout, key: &impl OpensFile) -> FinalLeaf {
    let inputs = [(0..66).map(FIn::Wit).collect(), fin(FIn::Rec, R_PC, 4), fin(FIn::Rec, R_MICRO, 1), fin(FIn::St, S_LO, 20)].concat();
    leaf(l, key, "zk_program_counter".into(), &[Blk::State, Blk::Record], 66, &inputs, &tracked(program_counter_challenge))
}

pub fn opcode_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<FinalLeaf> {
    let inputs = [fin(FIn::Rec, R_PC, 4), fin(FIn::Rec, R_OP, 4)].concat();
    info.code_chunks.iter().enumerate().map(|(k, c)| leaf(l, key, format!("zk_opcode_{k}"), &[Blk::Record], 0, &inputs, &tracked(|st| opcode_challenge(st, c)))).collect()
}

pub fn addresses_leaf(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> FinalLeaf {
    let inputs = [fin(FIn::Rec, R_R1A, 4), fin(FIn::Rec, R_R2A, 4), fin(FIn::Rec, R_WADDR, 4), fin(FIn::Rec, R_MEMW, 1), fin(FIn::Rec, R_PC, 4)].concat();
    let i = info.clone();
    leaf(l, key, "zk_addresses_sections".into(), &[Blk::Record], 0, &inputs, &tracked(|st| addresses_sections_challenge(st, &i.read_write, &i.read_only, &i.registers, &i.code)))
}

pub fn future_read_leaf(l: &Layout, key: &impl OpensFile, r: u8) -> FinalLeaf {
    let inputs = [agreed16(), fin(FIn::Rec, R_LS1, 8), fin(FIn::Rec, R_LS2, 8), vec![FIn::K(i64::from(r))]].concat();
    leaf(l, key, format!("zk_future_read_{r}"), &[Blk::Record], 0, &inputs, &tracked(future_read_challenge))
}

pub fn initialized_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<FinalLeaf> {
    let mut v = vec![];
    for (k, c) in info.data_chunks.iter().enumerate() {
        for r in [1u8, 2] {
            let inputs = [reads(), vec![FIn::K(i64::from(r))]].concat();
            v.push(leaf(l, key, format!("zk_initialized_{k}_{r}"), &[Blk::Record], 0, &inputs, &tracked(|st| initialized_challenge(st, c))));
        }
    }
    v
}

pub fn uninitialized_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<FinalLeaf> {
    [1u8, 2]
        .into_iter()
        .map(|r| {
            let inputs = [reads(), vec![FIn::K(i64::from(r))]].concat();
            leaf(l, key, format!("zk_uninitialized_{r}"), &[Blk::Record], 0, &inputs, &tracked(|st| uninitialized_challenge(st, &info.uninitialized)))
        })
        .collect()
}

pub fn halt_hash_leaf(l: &Layout, key: &impl OpensFile) -> FinalLeaf {
    // halt_challenge's inputs: claimed last step, agreed step, read 1 and
    // read 2 values, opcode, hash, claimed final hash; a success exit in
    // place of the record's fields
    let inputs =
        [fin(FIn::Cl, C_LAST_STEP, 8), zeros(8), fin(FIn::St, S_BASE, 4), konst_word(93), konst_word(0), konst_word(0x73), fin(FIn::St, S_HI, 20), fin(FIn::Cl, C_LAST_HASH, 20)]
            .concat();
    leaf(l, key, "zk_halt_hash".into(), &[Blk::State, Blk::Claim], 0, &inputs, &tracked(halt_challenge))
}

pub fn halt_exit_leaf(l: &Layout, key: &impl OpensFile) -> FinalLeaf {
    // equal constants in place of the two hashes
    let inputs = [fin(FIn::Cl, C_LAST_STEP, 8), agreed16(), fin(FIn::Rec, R_R1V, 4), fin(FIn::Rec, R_R2V, 4), fin(FIn::Rec, R_OP, 4), zeros(40), zeros(40)].concat();
    leaf(l, key, "zk_halt_exit".into(), &[Blk::Record, Blk::Claim], 0, &inputs, &tracked(halt_challenge))
}

// ----- InputData (D61): the input committed by signature -----

/// The input's words as the trace reads them: little-endian, zero-padded
/// (checked against the emulator in tests/zk_input.rs).
pub fn input_words(input: &[u8]) -> Vec<u32> {
    emulator::loader::program::vec_u8_to_vec_u32(input, true)
}

/// The Winternitz parameters of an input word's key (4 bytes).
pub fn input_key_params() -> lngap_lamport::winternitz::WotsParams {
    lngap_lamport::winternitz::WotsParams::for_bytes(4)
}

/// The message an input key signs: the word, big-endian.
pub fn input_message(word: u32) -> [u8; 4] {
    word.to_be_bytes()
}

/// The members' check of a claim's input (availability, D61): one valid
/// signature per word, under the prover's key for that word.
pub fn input_signed(keys: &[WotsPublic], words: &[u32], sigs: &[lngap_lamport::winternitz::WotsSig]) -> bool {
    keys.len() == words.len() && sigs.len() == words.len() && keys.iter().zip(words).zip(sigs).all(|((k, w), s)| k.verify(s).is_ok_and(|m| m == input_message(*w)))
}

/// `zk_input_<j>` (the record, and the prover's signature on input word j
/// on top of the pair reveal): a read of word j's address that was never
/// written doesn't return the signed word. BitVMX's `input_challenge`.
pub fn input_leaves(l: &Layout, key: &impl OpensFile, input_keys: &[WotsPublic], info: &ProgramInfo) -> Vec<FinalLeaf> {
    assert_eq!(input_keys.len(), info.input_words, "one key per input word");
    input_keys
        .iter()
        .enumerate()
        .map(|(j, k)| {
            let inputs = [(0..8).map(FIn::Pre).collect(), reads()].concat();
            let address = info.input_base + 4 * j as u32;
            FinalLeaf {
                name: format!("zk_input_{j}"),
                blocks: vec![Blk::Record],
                wit: 0,
                script: final_leaf_pre(l, key, Some(k), &[Blk::Record], 0, &inputs, &tracked(|st| input_challenge(st, address))),
            }
        })
        .collect()
}

/// Native mirror: a never-written read of word j's address whose value
/// isn't `word`.
pub fn input_fires(record: &Record, info: &ProgramInfo, j: usize, word: u32) -> bool {
    let a = info.input_base + 4 * j as u32;
    let r = &record.read;
    (record.last_step_1 == NEVER && r.read_1_addr == a && r.read_1_value != word) || (record.last_step_2 == NEVER && r.read_2_addr == a && r.read_2_value != word)
}

/// All of the claimant's final-depth disproves for a program.
pub fn final_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<FinalLeaf> {
    let mut v = vec![
        record_step_leaf(l, key),
        entry_point_leaf(l, key, info),
        program_counter_leaf(l, key),
        addresses_leaf(l, key, info),
        future_read_leaf(l, key, 1),
        future_read_leaf(l, key, 2),
        halt_hash_leaf(l, key),
        halt_exit_leaf(l, key),
    ];
    v.extend(uninitialized_leaves(l, key, info));
    v.extend(initialized_leaves(l, key, info));
    v.extend(opcode_leaves(l, key, info));
    v
}

// ----- mirrors -----

/// The final step the blocks describe, for the challenges' mirrors (the
/// agreed step is the record's).
pub fn as_final_step(state: &State, record: &Record, claim: &Claim) -> FinalStep {
    FinalStep {
        prev_hash: state.lo,
        read: record.read,
        write: record.write,
        hash: state.hi,
        witness: record.witness,
        agreed_step: record.step,
        last_step_1: record.last_step_1,
        last_step_2: record.last_step_2,
        claim_last_step: claim.last_step,
        claim_last_hash: claim.last_hash,
    }
}

/// Whether the leaf named `name` fires on these blocks (and, for the
/// program counter, the claimant's witness).
pub fn fires(name: &str, info: &ProgramInfo, state: &State, record: &Record, claim: &Claim, wit: &[u8]) -> bool {
    use crate::challenges as c;
    let f = as_final_step(state, record, claim);
    let last = u64::from(record.step) + 1 == claim.last_step;
    match name {
        "zk_record_step" => record.step != state.base,
        "zk_entry_point" => c::entry_point_fires(&f, info.entry),
        "zk_program_counter" => {
            let pph: [u8; 20] = wit[..20].try_into().unwrap();
            let w = |i: usize| u32::from_be_bytes(wit[i..i + 4].try_into().unwrap());
            let pw = Step { write_addr: w(20), write_value: w(24), pc: w(28), micro: wit[32] };
            c::program_counter_fires(&f, &pph, &pw)
        }
        "zk_addresses_sections" => c::addresses_fire(&f, info),
        "zk_future_read_1" => c::future_read_fires(&f, 1),
        "zk_future_read_2" => c::future_read_fires(&f, 2),
        "zk_uninitialized_1" => c::uninitialized_fires(&f, 1, info),
        "zk_uninitialized_2" => c::uninitialized_fires(&f, 2, info),
        "zk_halt_hash" => last && state.hi != claim.last_hash,
        "zk_halt_exit" => last && !(record.read.read_1_value == 93 && record.read.read_2_value == 0 && record.read.opcode == 0x73),
        n if n.starts_with("zk_opcode_") => c::opcode_fires(&f, &info.code_chunks[n["zk_opcode_".len()..].parse::<usize>().unwrap()]),
        n if n.starts_with("zk_initialized_") => {
            let mut it = n["zk_initialized_".len()..].split('_');
            let k: usize = it.next().unwrap().parse().unwrap();
            let r: u8 = it.next().unwrap().parse().unwrap();
            c::initialized_fires(&f, r, &info.data_chunks[k])
        }
        _ => panic!("unknown final leaf {name}"),
    }
}

/// `NEVER`, re-exported for tests building records.
pub const NEVER_WRITTEN: u64 = NEVER;
