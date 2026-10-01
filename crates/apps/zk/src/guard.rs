//! The class guard (D59 amended, 2026-10-01): a prove leaf proves only
//! steps whose opcode and micro-step belong to its class. BitVMX's
//! verification scripts for `nop` and `ecall` never check the opcode
//! (`op_nop` drops it; `op_ecall` reads a register), so without the guard
//! a prover could prove any step as a nop (no write, pc + 4) or as an
//! ecall. The other classes' scripts assert their opcode bits themselves;
//! the guard covers them all the same.
//!
//! The class is a function of a few fixed fields: the major opcode (bits
//! 0..7), funct3 (12..15), funct7 (25..32, which BitVMX's mapping reads
//! only as 0x00, 0x20, 0x01 or "other"), whether rd is zero, and the
//! micro-step. They are packed into one number, the feature; each class's
//! allowed features are enumerated from BitVMX's own mapping
//! (`get_key_from_instruction_and_micro`), so the guard cannot drift from
//! it. SYSTEM instructions (major opcode 0x73) are matched exactly: ecall
//! is 0x00000073, ebreak (a nop) 0x00100073.

use std::collections::BTreeSet;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::instruction_mapping::{get_key_from_instruction_and_micro, get_required_microinstruction};

const MAJORS: [u32; 10] = [0x03, 0x0f, 0x13, 0x17, 0x23, 0x33, 0x37, 0x63, 0x67, 0x6f];
const F7: [u32; 4] = [0x00, 0x20, 0x01, 0x7f];
const ECALL: u32 = 0x0000_0073;
const EBREAK: u32 = 0x0010_0073;

/// funct7's class: 0x00, 0x20, 0x01, anything else.
fn f7_class(opcode: u32) -> u32 {
    match opcode >> 25 {
        0x00 => 0,
        0x20 => 1,
        0x01 => 2,
        _ => 3,
    }
}

/// The feature: major + 128·(funct3 + 8·(f7 class + 4·(rd == 0 + 2·micro))).
pub fn feature(opcode: u32, micro: u8) -> u32 {
    let major = opcode & 0x7f;
    let f3 = (opcode >> 12) & 7;
    let rd0 = u32::from((opcode >> 7) & 0x1f == 0);
    major + 128 * (f3 + 8 * (f7_class(opcode) + 4 * (rd0 + 2 * u32::from(micro))))
}

/// BitVMX's key for `opcode` at `micro`, if it decodes to a supported
/// instruction at a micro-step it has.
pub fn key_of(opcode: u32, micro: u8) -> Option<String> {
    let ins = riscv_decode::decode(opcode).ok()?;
    if micro >= get_required_microinstruction(&ins) {
        return None;
    }
    // BitVMX panics on instructions it doesn't support
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let k = std::panic::catch_unwind(|| get_key_from_instruction_and_micro(&ins, micro)).ok();
    std::panic::set_hook(prev);
    k
}

/// The features (non-SYSTEM) that map to `key`.
pub fn allowed(key: &str) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    for &major in &MAJORS {
        for f3 in 0..8u32 {
            for &f7 in &F7 {
                for rd in [0u32, 5] {
                    for micro in 0..8u8 {
                        let op = major | rd << 7 | f3 << 12 | 1 << 15 | 2 << 20 | f7 << 25;
                        if key_of(op, micro).as_deref() == Some(key) {
                            out.insert(feature(op, micro));
                        }
                    }
                }
            }
        }
    }
    out
}

/// The guard natively: does (opcode, micro) belong to `key`'s class?
pub fn guard_holds(key: &str, opcode: u32, micro: u8) -> bool {
    if opcode & 0x7f == 0x73 {
        return micro == 0 && ((opcode == ECALL && key == "ecall") || (opcode == EBREAK && key == "nop"));
    }
    allowed(key).contains(&feature(opcode, micro))
}

/// Emits code over the 9 inputs `[o0 .. o7, micro]` (the opcode's nibbles,
/// most significant first; the micro-step on top), tracking how many
/// computed items sit above them.
struct G {
    b: Builder,
    above: usize,
}

impl G {
    /// PICK input `i` (0 = o0 .. 8 = micro).
    fn pick(mut self, i: usize) -> Self {
        self.b = self.b.push_int((8 - i + self.above) as i64).push_opcode(OP_PICK);
        self.above += 1;
        self
    }
    fn op(mut self, o: bitcoin::opcodes::Opcode, pops: usize, pushes: usize) -> Self {
        self.b = self.b.push_opcode(o);
        self.above = self.above + pushes - pops;
        self
    }
    fn int(mut self, v: i64) -> Self {
        self.b = self.b.push_int(v);
        self.above += 1;
        self
    }
    /// x -> x mod 8 (x a nibble).
    fn mod8(mut self) -> Self {
        self.b = self.b.push_opcode(OP_DUP).push_int(7).push_opcode(OP_GREATERTHAN).push_opcode(OP_IF).push_int(8).push_opcode(OP_SUB).push_opcode(OP_ENDIF);
        self
    }
    /// x -> x · 2^k.
    fn shl(mut self, k: u32) -> Self {
        for _ in 0..k {
            self.b = self.b.push_opcode(OP_DUP).push_opcode(OP_ADD);
        }
        self
    }
    /// Push (input i == v).
    fn eq(self, i: usize, v: i64) -> Self {
        self.pick(i).int(v).op(OP_EQUAL, 2, 1)
    }
}

/// The guard in Script: consumes `[o0 .. o7, micro]` and fails unless the
/// opcode and micro-step belong to `key`'s class.
pub fn class_guard_script(key: &str) -> ScriptBuf {
    let mut g = G { b: Builder::new(), above: 0 };
    // major = o7 + 16·(o6 mod 8)
    g = g.pick(6).mod8().shl(4).pick(7).op(OP_ADD, 2, 1);
    // + 128·(o4 mod 8)
    g = g.pick(4).mod8().shl(7).op(OP_ADD, 2, 1);
    // + 1024·f7 class: 3 - 3·[o0 = 0, o1 < 2] - 2·[o0 = 4, o1 < 2] - [o0 = 0, o1 in 2..4]
    g = g.int(3);
    g = g.eq(0, 0).pick(1).int(2).op(OP_LESSTHAN, 2, 1).op(OP_BOOLAND, 2, 1).op(OP_DUP, 0, 1).op(OP_DUP, 0, 1).op(OP_ADD, 2, 1).op(OP_ADD, 2, 1).op(OP_SUB, 2, 1);
    g = g.eq(0, 4).pick(1).int(2).op(OP_LESSTHAN, 2, 1).op(OP_BOOLAND, 2, 1).op(OP_DUP, 0, 1).op(OP_ADD, 2, 1).op(OP_SUB, 2, 1);
    g = g.eq(0, 0).pick(1).int(2).int(4).op(OP_WITHIN, 3, 1).op(OP_BOOLAND, 2, 1).op(OP_SUB, 2, 1);
    g = g.shl(10).op(OP_ADD, 2, 1);
    // + 4096·[rd = 0]: o5 = 0 and o6 < 8
    g = g.eq(5, 0).pick(6).int(8).op(OP_LESSTHAN, 2, 1).op(OP_BOOLAND, 2, 1).shl(12).op(OP_ADD, 2, 1);
    // + 8192·micro
    g = g.pick(8).shl(13).op(OP_ADD, 2, 1);
    // membership
    g = g.int(0);
    for v in allowed(key) {
        g = g.op(OP_OVER, 0, 1).int(v as i64).op(OP_EQUAL, 2, 1).op(OP_BOOLOR, 2, 1);
    }
    g = g.op(OP_NIP, 2, 1);
    // SYSTEM: exact opcodes, micro 0
    for (op, k) in [(ECALL, "ecall"), (EBREAK, "nop")] {
        if k != key {
            continue;
        }
        g = g.eq(8, 0);
        for i in 0..8 {
            g = g.eq(i, ((op >> (28 - 4 * i)) & 15) as i64).op(OP_BOOLAND, 2, 1);
        }
        g = g.op(OP_BOOLOR, 2, 1);
    }
    let mut b = g.b.push_opcode(OP_VERIFY);
    for _ in 0..4 {
        b = b.push_opcode(OP_2DROP);
    }
    b.push_opcode(OP_DROP).into_script()
}
