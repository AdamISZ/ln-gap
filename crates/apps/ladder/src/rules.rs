//! The rules: each a check over re-revealed moves, with its native mirror.
//!
//! - Alice's, on the hub's choice at depth `2r`: `choice_<r>` (the choice
//!   isn't one of round `r`'s segments).
//! - The hub's, on Alice's final move (depth `2R + 1`):
//!   - `step`: the record's agreed step isn't the hub's choices
//!     concatenated;
//!   - `equiv_<kind>_<r>_<i>`: the final move's hash after step `t`
//!     (`step`) or `t + 1` (`next`) isn't the one Alice posted for that
//!     step as round `r`'s hash `i` (BitVMX's `equivocation_resign`);
//!   - `initial`: the agreed step is 0 and the hash after it isn't
//!     BitVMX's initial hash;
//!   - `halt_hash`, `halt_exit`: the disputed step is the claimed last,
//!     and its hash isn't the claimed one, or it isn't a success exit;
//!   - BitVMX's other final-step challenges over the record:
//!     `entry_point`, `program_counter`, `addresses_sections`,
//!     `future_read_<r>`, `uninitialized_<r>`, `initialized_<k>_<r>`,
//!     `opcode_<k>`, `input_<j>`.
//! - Alice's proof of the disputed step, `prove_<class>`: the step is what
//!   its instruction does (BitVMX's verification script for the class),
//!   and the hash after it is BLAKE3 of the hash before and its write.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::challenges::{
    addresses_sections_challenge, entry_point_challenge, equivocation_resign_challenge, future_read_challenge, halt_challenge, initialized_challenge, input_challenge,
    opcode_challenge, program_counter_challenge, uninitialized_challenge,
};
use bitcoin_script_riscv::riscv::instruction_mapping::{generate_verification_script, requires_witness};
use bitcoin_script_stack::stack::StackTracker;
use bitvmx_cpu_definitions::challenge::EquivocationKind;
use lngap_lamport::winternitz::WotsPublic;
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::game::*;

use crate::script::{konst_bytes, konst_word, ms, rule_script, zeros, In, Msg};
use crate::{digits, Schedule, C_LAST_HASH, C_LAST_STEP, FIELD_CLAIM, FIELD_JUMP_HASH, FIELD_NEXT_HASH, FIELD_RECORD, FIELD_STEP_HASH, FIELD_SUCC};

/// A rule: the messages it re-reveals (in verify order), the poster's
/// own witness (nibbles), its check's inputs and the check.
#[derive(Clone, Debug)]
pub struct Rule {
    pub name: String,
    pub msgs: Vec<Msg>,
    pub wit: usize,
    pub inputs: Vec<In>,
    pub check: ScriptBuf,
}

impl Rule {
    /// The leaf script after `gate`, `key` resolving each message's key.
    pub fn script(&self, gate: Builder, key: &dyn Fn(Msg) -> WotsPublic) -> ScriptBuf {
        let keys: Vec<WotsPublic> = self.msgs.iter().map(|m| key(*m)).collect();
        let refs: Vec<&WotsPublic> = keys.iter().collect();
        rule_script(gate, &refs, self.wit, &self.inputs, &self.check)
    }
}

fn tracked(f: impl FnOnce(&mut StackTracker)) -> ScriptBuf {
    let mut st = StackTracker::new();
    f(&mut st);
    st.get_script()
}

/// Script's limit on the main and alt stacks together.
pub const MAX_STACK: usize = 1000;

/// Run a script on a witness: (it leaves exactly one true item within
/// the stack limit, peak stack).
pub fn spends(script: &ScriptBuf, wire: Vec<Vec<u8>>) -> (bool, usize) {
    match lngap_script32::sim::run_peak(script.as_script(), wire) {
        Ok((st, peak)) => (peak <= MAX_STACK && st.len() == 1 && st[0].iter().enumerate().any(|(i, b)| *b != 0 && !(i == st[0].len() - 1 && *b == 0x80)), peak),
        Err(_) => (false, 0),
    }
}

// ----- the final move's fields: its record is always message 0 -----

fn rec(off: usize, len: usize) -> Vec<In> {
    ms(0, digits(off, len))
}

/// A field of the final move.
fn fin(s: &Schedule, f: usize) -> Msg {
    Msg::Field(s.depths(), f)
}

/// Move 1's claim.
fn claim_field() -> Msg {
    Msg::Field(1, FIELD_CLAIM)
}

/// All 20 bytes of message `m` (a hash field).
fn hash20(m: usize) -> Vec<In> {
    ms(m, 0..40)
}

/// The agreed step as BitVMX's 16 nibbles (8 zeros, then the record's).
fn agreed16() -> Vec<In> {
    [zeros(8), rec(R_STEP, 4)].concat()
}

/// The reads as BitVMX's challenges take them: address, value, last
/// write step, read 1 then read 2.
fn reads() -> Vec<In> {
    [rec(R_R1A, 4), rec(R_R1V, 4), rec(R_LS1, 8), rec(R_R2A, 4), rec(R_R2V, 4), rec(R_LS2, 8)].concat()
}

/// The final move's record, re-revealed first by every rule on it.
#[allow(non_snake_case)]
fn FINAL(s: &Schedule) -> Msg {
    fin(s, FIELD_RECORD)
}

// ----- Alice's rule on a choice -----

/// `choice_<r>` on the hub's move at depth `2r`: its byte isn't below
/// round `r`'s segments.
pub fn choice_rule(s: &Schedule, r: u32) -> Rule {
    let check = Builder::new()
        .push_int(i64::from(s.segments(r)))
        .push_opcode(OP_GREATERTHANOREQUAL)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_0NOTEQUAL)
        .push_opcode(OP_BOOLOR)
        .push_opcode(OP_VERIFY)
        .into_script();
    Rule { name: format!("choice_{r}"), msgs: vec![Msg::Field(2 * r, 0)], wit: 0, inputs: vec![In::M(0, 0), In::M(0, 1)], check }
}

pub fn choice_fires(s: &Schedule, r: u32, byte: u8) -> bool {
    u32::from(byte) >= s.segments(r)
}

// ----- the hub's rules on the final move -----

/// Script: a number from the nibbles on top (the most significant
/// deepest), by Horner's rule with doublings.
fn horner(b: Builder, n: usize, bits: impl Fn(usize) -> u32) -> Builder {
    // [x_0 .. x_{n-1}] (x_{n-1} on top) -> sum x_k 2^(bits after k)
    let mut b = b;
    for k in 0..n {
        if k == 0 {
            b = b.push_int((n - 1) as i64).push_opcode(OP_ROLL);
            continue;
        }
        for _ in 0..bits(k) {
            b = b.push_opcode(OP_DUP).push_opcode(OP_ADD);
        }
        b = b.push_int((n - k) as i64).push_opcode(OP_ROLL).push_opcode(OP_ADD);
    }
    b
}

/// `step`: the record's agreed step (8 nibbles) isn't the hub's choices'
/// bits concatenated.
pub fn step_rule(s: &Schedule) -> Rule {
    let r = s.rounds() as usize;
    let mut msgs = vec![FINAL(s)];
    msgs.extend((1..=s.rounds()).map(|q| Msg::Field(2 * q, 0)));
    let mut inputs = rec(R_STEP, 4);
    inputs.extend((1..=r).map(|q| In::M(q, 1)));
    // the choices: [c_1 .. c_R]: c_1 deepest
    let b = horner(Builder::new(), r, |k| s.bits(k as u32 + 1));
    let b = b.push_opcode(OP_TOALTSTACK);
    let b = horner(b, 8, |_| 4);
    let check = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_VERIFY).into_script();
    Rule { name: "step".into(), msgs, wit: 0, inputs, check }
}

pub fn step_fires(s: &Schedule, record: &Record, choices: &[u32]) -> bool {
    u64::from(record.step) != s.agreed_step(choices)
}

/// `equiv_<kind>_<r>_<i>`: BitVMX's `equivocation_resign_challenge`, round
/// `r`'s hash `i` (0-based) against the final move's hash after the agreed
/// step (`StepHash`) or the next (`NextHash`).
pub fn equiv_rule(s: &Schedule, kind: EquivocationKind, r: u32, i: usize) -> Rule {
    let (depth, field) = s.hash_field(r, i);
    let theirs = if kind == EquivocationKind::StepHash { FIELD_STEP_HASH } else { FIELD_NEXT_HASH };
    let inputs = [hash20(2), hash20(1), agreed16()].concat();
    let (rounds, nary, last) = (s.def.total_rounds(), s.def.nary, s.def.nary_last_round);
    let k = if kind == EquivocationKind::StepHash { "step" } else { "next" };
    let check = tracked(|st| equivocation_resign_challenge(st, kind, r as u8, i as u8 + 1, rounds, nary, last));
    Rule { name: format!("equiv_{k}_{r}_{i}"), msgs: vec![FINAL(s), fin(s, theirs), Msg::Field(depth, field)], wit: 0, inputs, check }
}

/// All equivocation rules.
pub fn equiv_rules(s: &Schedule) -> Vec<Rule> {
    let mut v = vec![];
    for r in 1..=s.rounds() {
        for i in 0..s.hashes(r) {
            for kind in [EquivocationKind::StepHash, EquivocationKind::NextHash] {
                v.push(equiv_rule(s, kind, r, i));
            }
        }
    }
    v
}

/// Where step `x`'s hash was posted, read from `x`'s own digits (BitVMX's
/// `get_round_and_index`): the last round whose digit isn't zero, and that
/// digit less one (a 0-based index); `None` for step 0 (the initial hash).
/// For the agreed step this is where Alice posted it as long as the step
/// is the hub's choices, which `step` enforces.
pub fn posted_at(s: &Schedule, x: u64) -> Option<(u32, usize)> {
    (1..=s.rounds()).rev().find_map(|r| {
        let d = s.def.step_bits_for_round(r as u8, x);
        (d != 0).then(|| (r, d as usize - 1))
    })
}

/// Mirror of the equivocation rules: the one that fires on a final move
/// whose agreed step is `t`, if any: the hash posted where `t`'s (or
/// `t + 1`'s) digits say differs from the final move's. `posted(r, i)` is
/// round `r`'s hash `i`.
pub fn equiv_fires(s: &Schedule, t: u64, step_hash: &[u8; 20], next_hash: &[u8; 20], posted: &dyn Fn(u32, usize) -> [u8; 20]) -> Vec<String> {
    let mut v = vec![];
    for (kind, x, h) in [("step", t, step_hash), ("next", t + 1, next_hash)] {
        if let Some((r, i)) = posted_at(s, x) {
            if i < s.hashes(r) && posted(r, i) != *h {
                v.push(format!("equiv_{kind}_{r}_{i}"));
            }
        }
    }
    v
}

/// `initial`: the agreed step is 0 and the hash after it isn't BitVMX's
/// initial hash.
pub fn initial_rule(s: &Schedule) -> Rule {
    let h0 = initial_hash();
    let inputs = [rec(R_STEP, 4), hash20(1), konst_bytes(&h0)].concat();
    // [step 8, hash 40, h0 40]: fires iff step == 0 and hash != h0
    let mut b = Builder::new().push_int(1);
    // hash == h0, nibble by nibble (h0's nibble k at depth 40 - 1 - k + 1)
    for k in 0..40 {
        b = b.push_int(80 - k as i64).push_opcode(OP_PICK).push_int(41 - k as i64).push_opcode(OP_PICK).push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
    }
    b = b.push_opcode(OP_NOT).push_opcode(OP_TOALTSTACK);
    for _ in 0..40 {
        b = b.push_opcode(OP_2DROP);
    }
    // the step's nibbles all zero
    b = b.push_int(1);
    for _ in 0..8 {
        b = b.push_opcode(OP_SWAP).push_opcode(OP_NOT).push_opcode(OP_BOOLAND);
    }
    let check = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLAND).push_opcode(OP_VERIFY).into_script();
    Rule { name: "initial".into(), msgs: vec![FINAL(s), fin(s, FIELD_STEP_HASH)], wit: 0, inputs, check }
}

pub fn initial_fires(record: &Record, step_hash: &[u8; 20]) -> bool {
    record.step == 0 && *step_hash != initial_hash()
}

/// `halt_hash`: the disputed step is the claimed last, and the hash after
/// it isn't the claimed final hash (BitVMX's `halt_challenge`, a success
/// exit in place of the record's fields).
pub fn halt_hash_rule(s: &Schedule) -> Rule {
    let inputs = [ms(2, digits(C_LAST_STEP, 8)), agreed16(), konst_word(93), konst_word(0), konst_word(0x73), hash20(1), ms(2, digits(C_LAST_HASH, 20))].concat();
    Rule { name: "halt_hash".into(), msgs: vec![FINAL(s), fin(s, FIELD_NEXT_HASH), claim_field()], wit: 0, inputs, check: tracked(halt_challenge) }
}

/// `halt_exit`: the disputed step is the claimed last, and it isn't an
/// ecall exit with 0 (equal constants in place of the hashes).
pub fn halt_exit_rule(s: &Schedule) -> Rule {
    let inputs = [ms(1, digits(C_LAST_STEP, 8)), agreed16(), rec(R_R1V, 4), rec(R_R2V, 4), rec(R_OP, 4), zeros(40), zeros(40)].concat();
    Rule { name: "halt_exit".into(), msgs: vec![FINAL(s), claim_field()], wit: 0, inputs, check: tracked(halt_challenge) }
}

pub fn entry_point_rule(s: &Schedule, info: &ProgramInfo) -> Rule {
    let inputs = [rec(R_PC, 4), rec(R_MICRO, 1), agreed16()].concat();
    let e = info.entry;
    Rule { name: "entry_point".into(), msgs: vec![FINAL(s)], wit: 0, inputs, check: tracked(|st| entry_point_challenge(st, e)) }
}

/// `program_counter`, the poster's witness: the hash after step `t - 1`
/// and step `t`'s write (33 bytes, `final_d60::program_counter_wit`);
/// under a jump list, the hash after `t - 1`, step `t`'s long jump's hash
/// and its write (53 bytes, `jhash::preimage` less the step).
pub fn program_counter_rule(s: &Schedule) -> Rule {
    if s.jump.is_some() {
        let inputs = [(0..106).map(In::W).collect(), rec(R_STEP, 4), rec(R_PC, 4), vec![In::M(0, 2 * R_MICRO + 1)], hash20(1)].concat();
        return Rule { name: "program_counter".into(), msgs: vec![FINAL(s), fin(s, FIELD_STEP_HASH)], wit: 106, inputs, check: crate::jhash::program_counter_jump_script() };
    }
    let inputs = [(0..66).map(In::W).collect(), rec(R_PC, 4), rec(R_MICRO, 1), hash20(1)].concat();
    Rule { name: "program_counter".into(), msgs: vec![FINAL(s), fin(s, FIELD_STEP_HASH)], wit: 66, inputs, check: tracked(program_counter_challenge) }
}

/// `succ` (a jump list): the disputed step's signed number isn't the
/// agreed step's successor.
pub fn succ_rule(s: &Schedule) -> Rule {
    let inputs = [rec(R_STEP, 4), ms(1, 0..8)].concat();
    let check = crate::jscript::verify_not_succ(Builder::new()).into_script();
    Rule { name: "succ".into(), msgs: vec![FINAL(s), fin(s, FIELD_SUCC)], wit: 0, inputs, check }
}

pub fn addresses_rule(s: &Schedule, info: &ProgramInfo) -> Rule {
    let inputs = [rec(R_R1A, 4), rec(R_R2A, 4), rec(R_WADDR, 4), rec(R_MEMW, 1), rec(R_PC, 4)].concat();
    let i = info.clone();
    Rule { name: "addresses_sections".into(), msgs: vec![FINAL(s)], wit: 0, inputs, check: tracked(|st| addresses_sections_challenge(st, &i.read_write, &i.read_only, &i.registers, &i.code)) }
}

pub fn future_read_rule(s: &Schedule, r: u8) -> Rule {
    let inputs = [agreed16(), rec(R_LS1, 8), rec(R_LS2, 8), vec![In::K(i64::from(r))]].concat();
    Rule { name: format!("future_read_{r}"), msgs: vec![FINAL(s)], wit: 0, inputs, check: tracked(future_read_challenge) }
}

pub fn uninitialized_rules(s: &Schedule, info: &ProgramInfo) -> Vec<Rule> {
    [1u8, 2]
        .into_iter()
        .map(|r| {
            let inputs = [reads(), vec![In::K(i64::from(r))]].concat();
            Rule { name: format!("uninitialized_{r}"), msgs: vec![FINAL(s)], wit: 0, inputs, check: tracked(|st| uninitialized_challenge(st, &info.uninitialized)) }
        })
        .collect()
}

pub fn initialized_rules(s: &Schedule, info: &ProgramInfo) -> Vec<Rule> {
    let mut v = vec![];
    for (k, c) in info.data_chunks.iter().enumerate() {
        for r in [1u8, 2] {
            let inputs = [reads(), vec![In::K(i64::from(r))]].concat();
            v.push(Rule { name: format!("initialized_{k}_{r}"), msgs: vec![FINAL(s)], wit: 0, inputs, check: tracked(|st| initialized_challenge(st, c)) });
        }
    }
    v
}

pub fn opcode_rules(s: &Schedule, info: &ProgramInfo) -> Vec<Rule> {
    let inputs = [rec(R_PC, 4), rec(R_OP, 4)].concat();
    info.code_chunks
        .iter()
        .enumerate()
        .map(|(k, c)| Rule { name: format!("opcode_{k}"), msgs: vec![FINAL(s)], wit: 0, inputs: inputs.clone(), check: tracked(|st| opcode_challenge(st, c)) })
        .collect()
}

/// `input_<j>`: a never-written read of input word `j`'s address doesn't
/// return Alice's signed word (BitVMX's `input_challenge`).
pub fn input_rules(s: &Schedule, info: &ProgramInfo) -> Vec<Rule> {
    (0..info.input_words)
        .map(|j| {
            let inputs = [ms(1, 0..8), reads()].concat();
            let address = info.input_base + 4 * j as u32;
            Rule { name: format!("input_{j}"), msgs: vec![FINAL(s), Msg::Word(j)], wit: 0, inputs, check: tracked(|st| input_challenge(st, address)) }
        })
        .collect()
}

/// Every rule of the hub's on Alice's final move.
pub fn final_rules(s: &Schedule, info: &ProgramInfo) -> Vec<Rule> {
    let mut v = vec![step_rule(s), initial_rule(s), halt_hash_rule(s), halt_exit_rule(s), entry_point_rule(s, info), program_counter_rule(s), addresses_rule(s, info)];
    if s.jump.is_some() {
        v.push(succ_rule(s));
    }
    v.push(future_read_rule(s, 1));
    v.push(future_read_rule(s, 2));
    v.extend(equiv_rules(s));
    v.extend(uninitialized_rules(s, info));
    v.extend(initialized_rules(s, info));
    v.extend(opcode_rules(s, info));
    v.extend(input_rules(s, info));
    v
}

// ----- Alice's proof -----

/// `prove_<class>`: the class guard, BitVMX's verification script for the
/// class on the record, and BLAKE3(hash before || write) == hash after.
pub fn prove_rule(s: &Schedule, class: &str, opcode: u32, micro: u8) -> Rule {
    let ins = riscv_decode::decode(opcode).expect("a class sample decodes");
    let witness = requires_witness(&ins);
    let exec = generate_verification_script(&ins, micro, lngap_zk::BASE_REGISTER_ADDRESS, witness);
    // bottom to top: the step hash's inputs (hash before, hash after, the
    // write: address, value, pc, micro), the verification script's, the
    // guard's (the opcode, the micro-step)
    let write26 = [rec(R_WADDR, 12), rec(R_WMICRO, 1)].concat();
    let mut ex = rec(R_WADDR, 12);
    ex.push(In::M(0, 2 * R_WMICRO + 1));
    if witness {
        ex.extend(rec(R_WITNESS, 4));
    }
    ex.extend(rec(R_MEMW, 1));
    ex.extend(rec(R_R1A, 20));
    ex.push(In::M(0, 2 * R_MICRO + 1));
    ex.extend(rec(R_OP, 4));
    let mut guard = rec(R_OP, 4);
    guard.push(In::M(0, 2 * R_MICRO + 1));
    let mut check = lngap_zk::guard::class_guard_script(class).into_bytes();
    check.extend_from_slice(exec.as_bytes());
    if s.jump.is_some() {
        // the step hash: BLAKE3(before || long jump's || write || t + 1)
        let inputs = [hash20(1), hash20(3), hash20(2), write26, ms(4, 0..8), ex, guard].concat();
        check.extend_from_slice(crate::jhash::step_hash_jump_script().as_bytes());
        let msgs = vec![FINAL(s), fin(s, FIELD_STEP_HASH), fin(s, FIELD_NEXT_HASH), fin(s, FIELD_JUMP_HASH), fin(s, FIELD_SUCC)];
        return Rule { name: format!("prove_{class}"), msgs, wit: 0, inputs, check: ScriptBuf::from_bytes(check) };
    }
    let inputs = [hash20(1), hash20(2), write26, ex, guard].concat();
    check.extend_from_slice(step_hash_script().as_bytes());
    Rule { name: format!("prove_{class}"), msgs: vec![FINAL(s), fin(s, FIELD_STEP_HASH), fin(s, FIELD_NEXT_HASH)], wit: 0, inputs, check: ScriptBuf::from_bytes(check) }
}

/// One proof rule per instruction class of the program's code.
pub fn prove_rules(s: &Schedule, info: &ProgramInfo) -> Vec<Rule> {
    lngap_zk::family::code_classes(info).into_iter().map(|(class, (op, micro))| prove_rule(s, &class, op, micro)).collect()
}
