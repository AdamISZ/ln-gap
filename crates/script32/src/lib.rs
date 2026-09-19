//! 32-bit word arithmetic in Bitcoin Script over 4-bit digits, for the
//! SHA-256 round and message-schedule leaves of the bisection dispute path.
//!
//! Conventions:
//! * A word is 8 stack elements, one nibble each (script numbers 0..=15),
//!   most-significant nibble deepest, least-significant on top. This is the
//!   order a Winternitz-verified 32-bit value leaves on the stack.
//! * Lookup tables (XOR, AND, per-shift-amount splits) are pushed once at
//!   the start of a leaf and dropped at the end. [`Stack`] tracks how many
//!   elements sit above the tables so every `OP_PICK` depth is right.
//! * Everything is unrolled; there are no loops in Script.

pub mod sha;
pub mod sim;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;

/// Which tables a leaf pushes, in push order (deepest first).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tables {
    pub xor: bool,
    pub and: bool,
    /// Bit-shift split tables for these shift amounts (1..=3), each two
    /// 16-entry tables: `lo_s(x) = x >> s` and `hi_s(x) = (x << (4-s)) & 15`.
    pub shifts: [bool; 4],
}

impl Tables {
    pub const NONE: Tables = Tables { xor: false, and: false, shifts: [false; 4] };
    pub fn size(&self) -> usize {
        usize::from(self.xor) * 256 + usize::from(self.and) * 256 + self.shifts.iter().filter(|s| **s).count() * 32
    }
}

/// A builder that knows how many elements sit above the tables.
pub struct Stack {
    pub b: Builder,
    pub tables: Tables,
    /// Elements above the tables (i.e. pushed after them).
    pub above: usize,
    // depth from the *top of the tables region* to each table's entry 0,
    // measured when nothing is above the tables
    xor_base: usize,
    and_base: usize,
    shift_base: [Option<(usize, usize)>; 4],
}

fn num(b: Builder, v: i64) -> Builder {
    if v == 0 { b.push_opcode(OP_PUSHBYTES_0) } else { b.push_int(v) }
}

impl Stack {
    /// Start a leaf body with `above` elements already on the stack (e.g. the
    /// inputs), then push the tables *under* nothing: tables go on top, so
    /// the inputs end up below them and must be rolled up with [`Stack::roll_inputs_above`].
    pub fn new(b: Builder, tables: Tables) -> Stack {
        let mut s = Stack { b, tables, above: 0, xor_base: 0, and_base: 0, shift_base: [None; 4] };
        // Push order and resulting depths (from the top of the table region):
        // the last table pushed is nearest the top.
        let mut pushed = 0usize;
        // XOR: entry k = 16a+b, pushed k = 255..0 so entry 0 is on top of its block
        if tables.xor {
            for k in (0..256u32).rev() {
                s.b = num(s.b, i64::from((k >> 4) ^ (k & 15)));
            }
            pushed += 256;
            s.xor_base = pushed; // will be adjusted below
        }
        if tables.and {
            for k in (0..256u32).rev() {
                s.b = num(s.b, i64::from((k >> 4) & (k & 15)));
            }
            pushed += 256;
            s.and_base = pushed;
        }
        for sh in 1..4usize {
            if tables.shifts[sh] {
                for x in (0..16i64).rev() {
                    s.b = num(s.b, x >> sh);
                }
                let lo = pushed + 16;
                for x in (0..16i64).rev() {
                    s.b = num(s.b, (x << (4 - sh)) & 15);
                }
                pushed += 32;
                s.shift_base[sh] = Some((lo, pushed));
            }
        }
        // convert "elements pushed up to and including this table" into
        // "depth of entry 0 from the table region's top"
        let total = pushed;
        if tables.xor {
            s.xor_base = total - s.xor_base;
        }
        if tables.and {
            s.and_base = total - s.and_base;
        }
        for sh in 1..4usize {
            if let Some((lo, hi)) = s.shift_base[sh] {
                s.shift_base[sh] = Some((total - lo, total - hi));
            }
        }
        s
    }

    /// Bring `n` input elements that were pushed before the tables above them.
    pub fn roll_inputs_above(&mut self, n: usize) {
        let t = self.tables.size();
        for _ in 0..n {
            self.b = num(std::mem::replace(&mut self.b, Builder::new()), (t + n - 1) as i64).push_opcode(OP_ROLL);
            self.above += 1;
        }
    }

    /// Apply an arbitrary builder transformation (e.g. a signature check)
    /// that leaves `delta` more elements above the tables.
    pub fn map(&mut self, delta: isize, f: impl FnOnce(Builder) -> Builder) {
        self.b = f(std::mem::replace(&mut self.b, Builder::new()));
        self.above = (self.above as isize + delta) as usize;
    }
    /// Push constant nibbles (first pushed deepest).
    pub fn push_nibbles(&mut self, nibbles: &[u8]) {
        for n in nibbles {
            self.int(i64::from(*n));
        }
    }
    pub fn op(&mut self, op: bitcoin::opcodes::Opcode) {
        self.b = std::mem::replace(&mut self.b, Builder::new()).push_opcode(op);
    }
    pub fn int(&mut self, v: i64) {
        self.b = num(std::mem::replace(&mut self.b, Builder::new()), v);
        self.above += 1;
    }
    /// Copy the element at depth `d` (0 = top) to the top.
    pub fn pick(&mut self, d: usize) {
        self.int(d as i64);
        self.above -= 1;
        self.op(OP_PICK);
        self.above += 1;
    }
    /// Move the element at depth `d` to the top.
    pub fn roll(&mut self, d: usize) {
        if d == 0 {
            return;
        }
        if d == 1 {
            self.op(OP_SWAP);
            return;
        }
        if d == 2 {
            self.op(OP_ROT);
            return;
        }
        self.int(d as i64);
        self.above -= 1;
        self.op(OP_ROLL);
    }
    pub fn drop(&mut self) {
        self.op(OP_DROP);
        self.above -= 1;
    }
    pub fn to_alt(&mut self) {
        self.op(OP_TOALTSTACK);
        self.above -= 1;
    }
    pub fn from_alt(&mut self) {
        self.op(OP_FROMALTSTACK);
        self.above += 1;
    }

    /// Consume the top two nibbles `a` (below) and `b` (top), push `a XOR b`.
    pub fn xor_nibble(&mut self) {
        self.two_operand(self.xor_base);
    }
    /// Consume the top two nibbles, push `a AND b`.
    pub fn and_nibble(&mut self) {
        self.two_operand(self.and_base);
    }
    fn two_operand(&mut self, base: usize) {
        // index = 16a + b; the entry sits at depth base + (above after popping the index) + index
        self.op(OP_SWAP);
        for _ in 0..4 {
            self.op(OP_DUP);
            self.op(OP_ADD);
        }
        self.op(OP_ADD); // now one element (index) replaces the two operands
        self.above -= 1;
        let d = base + (self.above - 1);
        self.int(d as i64);
        self.above -= 1;
        self.op(OP_ADD);
        self.op(OP_PICK);
    }
    /// Consume the top nibble, push `x >> s`.
    pub fn lo_shift(&mut self, s: usize) {
        let (lo, _) = self.shift_base[s].expect("shift table pushed");
        self.one_operand(lo);
    }
    /// Consume the top nibble, push `(x << (4-s)) & 15`.
    pub fn hi_shift(&mut self, s: usize) {
        let (_, hi) = self.shift_base[s].expect("shift table pushed");
        self.one_operand(hi);
    }
    fn one_operand(&mut self, base: usize) {
        let d = base + (self.above - 1);
        self.int(d as i64);
        self.above -= 1;
        self.op(OP_ADD);
        self.op(OP_PICK);
    }
    /// Consume the top nibble, push `15 - x`.
    pub fn not_nibble(&mut self) {
        self.int(15);
        self.op(OP_SWAP);
        self.op(OP_SUB);
        self.above -= 1;
    }

    // ----- words (8 nibbles, least significant on top) -----

    /// Push a constant word.
    pub fn push_word(&mut self, w: u32) {
        for i in (0..8).rev() {
            self.int(i64::from((w >> (4 * i)) & 15));
        }
    }
    /// Copy the word whose *top* nibble is at depth `d` (so the word occupies depths d..d+7).
    pub fn pick_word(&mut self, d: usize) {
        for _ in 0..8 {
            self.pick(d + 7);
        }
    }
    /// Move the word at depths d..d+7 to the top.
    pub fn roll_word(&mut self, d: usize) {
        for _ in 0..8 {
            self.roll(d + 7);
        }
    }
    pub fn drop_word(&mut self) {
        for _ in 0..4 {
            self.op(OP_2DROP);
        }
        self.above -= 8;
    }
    pub fn word_to_alt(&mut self) {
        for _ in 0..8 {
            self.to_alt();
        }
    }
    /// Restore a word parked with `word_to_alt` (order preserved).
    pub fn word_from_alt(&mut self) {
        for _ in 0..8 {
            self.from_alt();
        }
    }

    /// Consume the top two words, push their sum mod 2^32.
    pub fn add_word(&mut self) {
        // words: A at depths 8..15, B at 0..7 (LS nibbles on top). Process LS first.
        // Result nibbles are produced LS-first and parked on the altstack, then restored MS-first.
        // carry starts at 0
        self.int(0);
        for i in 0..8 {
            // stack: A(8-i nibbles left) B(8-i left) carry
            // bring B's current LS nibble (depth 1) and A's (depth 8-i+1 ... ) 
            // layout: [A_ms..A_i][B_ms..B_i][carry]  with B_i at depth 1, A_i at depth 1 + (8-i)
            self.roll(1); // B_i
            self.roll(1 + (8 - i)); // A_i  (after moving B_i up, A_i is at 1 + (8-i))
            self.op(OP_ADD);
            self.op(OP_ADD);
            self.above -= 2;
            // sum in 0..=31: nibble = sum mod 16, carry = sum >= 16
            self.op(OP_DUP);
            self.above += 1;
            self.int(16);
            self.op(OP_GREATERTHANOREQUAL);
            self.above -= 1;
            // [.., sum, carry]
            self.op(OP_TUCK); // [.., carry, sum, carry]
            self.above += 1;
            self.op(OP_IF);
            self.int(16);
            self.op(OP_SUB);
            self.above -= 1;
            self.op(OP_ENDIF);
            self.above -= 1; // OP_IF consumed the carry copy
            // [.., carry, nibble] -> park nibble, keep carry on top
            self.to_alt();
        }
        self.drop(); // final carry
        // restore: nibbles were parked LS first, so they come back MS... no: LIFO gives MS last.
        // parked order: n0 (LS), n1, ..., n7 (MS); popping yields n7 first -> deepest = MS. Correct.
        self.word_from_alt();
    }

    /// Consume the top two words, push their bitwise XOR.
    pub fn xor_word(&mut self) {
        self.binary_word(|s| s.xor_nibble());
    }
    /// Consume the top two words, push their bitwise AND.
    pub fn and_word(&mut self) {
        self.binary_word(|s| s.and_nibble());
    }
    fn binary_word(&mut self, f: impl Fn(&mut Stack)) {
        // stack: [A7..Ai][B7..Bi] with Bi on top and Ai at depth 8-i
        for i in 0..8 {
            self.roll(8 - i); // Ai to the top
            self.roll(1); // Bi to the top: [.., Ai, Bi]
            f(self);
            self.to_alt();
        }
        self.word_from_alt();
    }
    /// Consume the top word, push its bitwise NOT.
    pub fn not_word(&mut self) {
        for _ in 0..8 {
            self.not_nibble();
            self.to_alt();
        }
        self.word_from_alt();
    }

    /// Consume the top word, push it rotated right by `n` bits.
    pub fn rotr_word(&mut self, n: u32) {
        self.shift_word(n, true);
    }
    /// Consume the top word, push it shifted right by `n` bits (zero fill).
    pub fn shr_word(&mut self, n: u32) {
        self.shift_word(n, false);
    }
    fn shift_word(&mut self, n: u32, rotate: bool) {
        let q = (n / 4) as usize;
        let s = (n % 4) as usize;
        // Nibble-level: output nibble j (0 = MS) takes input nibble j - q (rotate) or 0 if j < q (shift).
        // Then bit-level by s: out_j = lo_s(in'_j) | hi_s(in'_{j-1}), with in'_{-1} = in'_7 (rotate) or 0 (shift).
        // Work with a copy laid out MS..LS (depths 7..0); build outputs MS-first onto the altstack.
        // First produce the nibble-rotated word x' as 8 elements (MS deepest) on the stack.
        // input word occupies depths 0..7 (LS on top): nibble j (0=MS) is at depth 7 - j.
        for j in 0..8usize {
            // push x'_j = x_{(j - q) mod 8} (rotate) or 0 (shift with j < q)
            let src = (j + 8 - q) % 8;
            if !rotate && j < q {
                self.int(0);
            } else {
                // depth of x_src: 7 - src, plus j elements pushed so far
                self.pick(7 - src + j);
            }
        }
        // drop the original word: its shallowest remaining nibble is always at depth 8
        for _ in 0..8 {
            self.roll(8);
            self.drop();
        }
        if s == 0 {
            return;
        }
        // now x' on the stack (MS deepest). out_j = lo_s(x'_j) | hi_s(x'_{j-1}).
        // Produce the LS nibble first so that restoring from the altstack yields MS deepest.
        for j in (0..8usize).rev() {
            // lo part: x'_j is at depth 7-j (outputs go to the altstack, so nothing accumulates)
            self.pick(7 - j);
            self.lo_shift(s);
            // hi part from x'_{j-1}
            if j == 0 {
                if rotate {
                    self.pick(1); // x'_7 at depth 0, plus the lo value on top -> depth 1
                    self.hi_shift(s);
                } else {
                    self.int(0);
                }
            } else {
                self.pick(7 - (j - 1) + 1);
                self.hi_shift(s);
            }
            self.op(OP_ADD); // disjoint bits: OR == ADD
            self.above -= 1;
            self.to_alt();
        }
        self.drop_word();
        self.word_from_alt();
    }

    /// Drop the tables (the stack must have exactly `keep` elements above them; they are preserved).
    pub fn drop_tables(&mut self, keep: usize) {
        for _ in 0..keep {
            self.to_alt();
        }
        let t = self.tables.size();
        for _ in 0..t / 2 {
            self.op(OP_2DROP);
        }
        if t % 2 == 1 {
            self.op(OP_DROP);
        }
        for _ in 0..keep {
            self.from_alt();
        }
    }

    pub fn into_builder(self) -> Builder {
        self.b
    }
}
