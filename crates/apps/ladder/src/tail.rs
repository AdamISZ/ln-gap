//! The read and jump challenges after Alice's final move, under a jump
//! list (JUMPLIST_PLAN.md, J4).
//!
//! The hub shows a fact about the history both sides agree on (up to the
//! agreed step `t`, whose hash is Alice's `h(t)`) by a path of hops from
//! step `t` back to a step `y`: each hop to the previous step or to the
//! long jump. It posts, signed: the hops' count `n`, their types (a nibble
//! each: 0 short, else long), the hashes `h(x_1) .. h(x_{n-1})` along the
//! way in hop fields (hop `k`'s field holds `h(x_{k+1})`), and the end
//! `h(x_n) = h(y)` in a field of its own. A genuine hash commits to its
//! step number, so a genuine `h(x_k)`'s back-links are the genuine hashes
//! of `x_k - 1` and `jump(x_k)`: the path needs no step numbers.
//!
//! Then:
//! - Alice may challenge one hop `k` (her one-time signature on `k`): the
//!   hub must reveal `h(x_k)`'s preimage (57 bytes: the hash before, the
//!   long jump's, the write, the step), which must hash to `h(x_k)` and
//!   whose back-link (by hop `k`'s type) must be `h(x_{k+1})` (or the end,
//!   at the last hop); or she loses nothing by waiting.
//! - After her window, the hub's verdict, with the end's preimage (`y`, the
//!   write at `y`):
//!   - `jump`: `y = jump(t + 1)` and `h(y)` isn't the long jump's hash Alice's
//!     disputed step commits to;
//!   - `read_<r>`: `y <= t` and the write at `y` contradicts Alice's read
//!     `r`: she names `y` as the last write but `y` wrote another address
//!     or value, or she names an earlier step (or none) but `y` wrote her
//!     address.
//!
//! With no hops (`n = 0`, `y = t`) the end must be Alice's `h(t)`.
//!
//! The path is posted in up to two links of `C` hops each; the first
//! carries `n`, the types and the end.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_functions::hash::blake3;
use bitcoin_script_stack::stack::StackTracker;

use crate::jhash::PREIMAGE_BYTES;
use crate::jump::{Hop, JumpList};
use crate::rules::Rule;
use crate::script::{ms, In, Msg};
use crate::{digits, Schedule, FIELD_JUMP_HASH, FIELD_RECORD, FIELD_STEP_HASH, FIELD_SUCC};
use lngap_zk::game::{R_LS1, R_LS2, R_R1A, R_R1V, R_R2A, R_R2V, R_STEP};

/// Hops a path link carries.
pub const CHUNK: usize = 43;
/// The most hops a path has (two links).
pub const MAX_HOPS: usize = 2 * CHUNK;

/// The first path link's fields: `n` (1 byte), the types (a nibble per
/// hop, `MAX_HOPS / 2` bytes), the end (20 bytes), then `CHUNK` hop
/// hashes; the second link's: `CHUNK` hop hashes.
pub const P_N: usize = 0;
pub const P_TYPES: usize = 1;
pub const P_END: usize = 2;
pub const P_HOPS: usize = 3;
pub const TYPES_BYTES: usize = MAX_HOPS / 2;

/// The first link's field sizes.
pub fn first_fields() -> Vec<usize> {
    [vec![1, TYPES_BYTES, 20], vec![20; CHUNK]].concat()
}

/// The second link's field sizes.
pub fn second_fields() -> Vec<usize> {
    vec![20; CHUNK]
}

/// Where hop `k`'s field (`h(x_{k+1})`) sits: (link 0 or 1, its field).
pub fn hop_field(k: usize) -> (usize, usize) {
    assert!(k < MAX_HOPS);
    if k < CHUNK {
        (0, P_HOPS + k)
    } else {
        (1, k - CHUNK)
    }
}

/// A path as posted: its hops' types and the hashes they reach (the last
/// is the end).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Path {
    pub types: Vec<Hop>,
    pub hashes: Vec<[u8; 20]>,
}

impl Path {
    /// The path from step `t` back to `y` over a chain (`hash(x)` the hash
    /// after step `x`).
    pub fn build(j: &JumpList, t: u64, y: u64, hash: &dyn Fn(u64) -> [u8; 20]) -> Path {
        let hops = j.path(t, y);
        Path { types: hops.iter().map(|h| h.0).collect(), hashes: hops.iter().map(|h| hash(h.1)).collect() }
    }
    pub fn n(&self) -> usize {
        self.types.len()
    }
    /// The end, `h(x_n)` (`h(t)`, given, if there are no hops).
    pub fn end(&self, h_t: &[u8; 20]) -> [u8; 20] {
        self.hashes.last().copied().unwrap_or(*h_t)
    }
    /// The two links' messages (the second empty if the path fits the
    /// first): unused hop fields are zeros.
    pub fn messages(&self, h_t: &[u8; 20]) -> (Vec<u8>, Vec<u8>) {
        assert!(self.n() <= MAX_HOPS, "a path of {} hops", self.n());
        let mut first = vec![self.n() as u8];
        let mut types = vec![0u8; TYPES_BYTES];
        for (k, t) in self.types.iter().enumerate() {
            if *t == Hop::Long {
                types[k / 2] |= if k % 2 == 0 { 0x10 } else { 0x01 };
            }
        }
        first.extend(types);
        first.extend(self.end(h_t));
        let hop = |k: usize| -> [u8; 20] {
            // hop k's field: h(x_{k+1}) for the hops before the last
            if k + 1 < self.n() {
                self.hashes[k]
            } else {
                [0; 20]
            }
        };
        for k in 0..CHUNK {
            first.extend(hop(k));
        }
        let mut second = vec![];
        if self.n() > CHUNK {
            for k in CHUNK..MAX_HOPS {
                second.extend(hop(k));
            }
        }
        (first, second)
    }
    /// Read back from the messages.
    pub fn parse(first: &[u8], second: &[u8]) -> (usize, Vec<Hop>, [u8; 20], Vec<[u8; 20]>) {
        let n = usize::from(first[0]);
        let types = (0..n).map(|k| if (first[1 + k / 2] >> if k % 2 == 0 { 4 } else { 0 }) & 15 != 0 { Hop::Long } else { Hop::Short }).collect();
        let end: [u8; 20] = first[1 + TYPES_BYTES..1 + TYPES_BYTES + 20].try_into().unwrap();
        let at = |k: usize| -> [u8; 20] {
            let (l, f) = hop_field(k);
            if l == 0 {
                let o = 1 + TYPES_BYTES + 20 + 20 * (f - P_HOPS);
                first[o..o + 20].try_into().unwrap()
            } else {
                second.get(20 * f..20 * f + 20).map(|b| b.try_into().unwrap()).unwrap_or([0; 20])
            }
        };
        let hops = (0..n.saturating_sub(1)).map(at).collect();
        (n, types, end, hops)
    }
}

// ----- scripts -----

/// `[a 40, b 40]` -> `[a == b]`.
pub fn eq_hash(mut b: Builder) -> Builder {
    b = b.push_int(1).push_opcode(OP_TOALTSTACK);
    for i in 0..40 {
        b = b.push_int(40 - i).push_opcode(OP_ROLL).push_opcode(OP_EQUAL).push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLAND).push_opcode(OP_TOALTSTACK);
    }
    b.push_opcode(OP_FROMALTSTACK)
}

/// `[hi, lo]` -> the byte they spell.
pub fn byte_number(b: Builder) -> Builder {
    b.push_opcode(OP_SWAP).push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_ADD)
}

/// `[pre 114, h 40]`: fails unless BLAKE3 of the 57-byte preimage is `h`.
/// The inputs must be alone on the main stack.
pub fn preimage_hash_script() -> ScriptBuf {
    static S: std::sync::OnceLock<ScriptBuf> = std::sync::OnceLock::new();
    S.get_or_init(|| {
        let mut st = StackTracker::new();
        let pre = st.define(2 * PREIMAGE_BYTES as u32, "preimage");
        let hash = st.define(40, "hash");
        st.move_var(hash);
        st.to_altstack();
        st.explode(pre);
        let result = blake3::blake3(&mut st, PREIMAGE_BYTES as u32, 5);
        let claimed = st.from_altstack();
        st.equals(result, true, claimed, true);
        st.get_script()
    })
    .clone()
}

/// The verdicts' common prefix checks, consuming from the top:
/// `[n_hi, n_lo]` within the link's range; then `[n_hi, n_lo, end 40,
/// h_t 40]`: some hops, or the end is `h(t)`.
fn n_checks(b: Builder, link: usize) -> Builder {
    // range: link 0 holds paths of 0..=CHUNK hops, link 1 longer ones
    let (lo, hi) = if link == 0 { (0, CHUNK) } else { (CHUNK + 1, MAX_HOPS) };
    let b = byte_number(b).push_int(lo as i64).push_int(hi as i64 + 1).push_opcode(OP_WITHIN).push_opcode(OP_VERIFY);
    // [n_hi, n_lo, end, h_t] -> end == h_t, then n != 0
    let b = eq_hash(b).push_opcode(OP_TOALTSTACK);
    byte_number(b).push_opcode(OP_0NOTEQUAL).push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLOR).push_opcode(OP_VERIFY)
}

/// The `jump` verdict's check. Inputs, bottom to top: the end's preimage
/// (114) and the end (40) [hashed last]; `s` (8) and `y` (8, the
/// preimage's step); the end and Alice's long-jump hash `J`; `n` (2), the
/// end and Alice's `h(t)`; `n` (2).
pub fn jump_verdict_script(j: &JumpList, link: usize) -> ScriptBuf {
    let mut b = n_checks(Builder::new(), link);
    // the end isn't J
    b = eq_hash(b).push_opcode(OP_NOT).push_opcode(OP_VERIFY);
    // y = jump(s)
    b = crate::jscript::verify_jump(b, j);
    let mut s = b.into_script().into_bytes();
    s.extend_from_slice(preimage_hash_script().as_bytes());
    ScriptBuf::from_bytes(s)
}

/// `[a 8, b 8]` -> `[a == b]` (words, nibble by nibble).
pub fn eq_word(mut b: Builder) -> Builder {
    b = b.push_int(1).push_opcode(OP_TOALTSTACK);
    for i in 0..8 {
        b = b.push_int(8 - i).push_opcode(OP_ROLL).push_opcode(OP_EQUAL).push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLAND).push_opcode(OP_TOALTSTACK);
    }
    b.push_opcode(OP_FROMALTSTACK)
}

/// The `read_<r>` verdict's check. Inputs, bottom to top: the end's
/// preimage (114) and the end (40) [hashed last]; the write at `y`'s
/// address (8), Alice's read address (8), the write's value (8), Alice's
/// read value (8), `y` (8), Alice's last-write step (16) and `t` (8); `n`
/// (2), the end and Alice's `h(t)`; `n` (2).
pub fn read_verdict_script(link: usize) -> ScriptBuf {
    use crate::jscript::word_to_number;
    let mut b = n_checks(Builder::new(), link);
    b = word_to_number(b).push_opcode(OP_TOALTSTACK); // t
    // the last-write step: never written if its high word isn't zero (then
    // its words may not fit a number)
    for _ in 0..8 {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.push_int(0);
    for _ in 0..8 {
        b = b.push_opcode(OP_SWAP).push_opcode(OP_0NOTEQUAL).push_opcode(OP_BOOLOR);
    }
    for _ in 0..8 {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    // [never, ls 8]
    b = b.push_int(8).push_opcode(OP_PICK).push_opcode(OP_IF).push_opcode(OP_2DROP).push_opcode(OP_2DROP).push_opcode(OP_2DROP).push_opcode(OP_2DROP).push_int(0).push_opcode(OP_ELSE);
    b = word_to_number(b).push_opcode(OP_ENDIF);
    b = b.push_opcode(OP_TOALTSTACK).push_opcode(OP_TOALTSTACK); // ls, never
    b = word_to_number(b).push_opcode(OP_TOALTSTACK); // y
    b = eq_word(b).push_opcode(OP_TOALTSTACK); // the values equal
    b = eq_word(b); // the addresses equal
    for _ in 0..5 {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    // [eq_a, eq_v, y, never, ls, t]: y <= t
    b = b.push_int(3).push_opcode(OP_PICK).push_opcode(OP_OVER).push_opcode(OP_LESSTHANOREQUAL).push_opcode(OP_TOALTSTACK).push_opcode(OP_DROP);
    // [eq_a, eq_v, y, never, ls]: she names y (ls == y, not never)
    b = b.push_opcode(OP_DUP).push_int(3).push_opcode(OP_PICK).push_opcode(OP_NUMEQUAL).push_int(2).push_opcode(OP_PICK).push_opcode(OP_NOT).push_opcode(OP_BOOLAND).push_opcode(OP_TOALTSTACK);
    // she names an earlier step, or none: (ls < y and not never) or never
    b = b.push_int(2).push_opcode(OP_PICK).push_opcode(OP_LESSTHAN).push_opcode(OP_OVER).push_opcode(OP_NOT).push_opcode(OP_BOOLAND).push_opcode(OP_BOOLOR);
    // [eq_a, eq_v, y, earlier]
    b = b.push_opcode(OP_NIP);
    // [eq_a, eq_v, earlier]: stale = earlier and y wrote her address
    b = b.push_int(2).push_opcode(OP_PICK).push_opcode(OP_BOOLAND);
    // [eq_a, eq_v, stale]: differs = she names y but y wrote elsewhere or else
    b = b.push_opcode(OP_ROT).push_opcode(OP_ROT).push_opcode(OP_BOOLAND).push_opcode(OP_NOT).push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLAND);
    b = b.push_opcode(OP_BOOLOR).push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLAND).push_opcode(OP_VERIFY);
    let mut s = b.into_script().into_bytes();
    s.extend_from_slice(preimage_hash_script().as_bytes());
    ScriptBuf::from_bytes(s)
}

/// Native mirror of the read verdict's condition.
pub fn read_contradicts(addr: u32, value: u32, last_write: u64, t: u32, y: u32, wa: u32, wv: u32) -> bool {
    let never = last_write >> 32 != 0;
    let ls = last_write as u32;
    let names_y = !never && ls == y;
    let earlier = never || ls < y;
    y <= t && ((names_y && !(wa == addr && wv == value)) || (earlier && wa == addr))
}

/// Hop `k`'s reveal check. Inputs, bottom to top: `h(x_k)`'s preimage
/// (114) and `h(x_k)` (40) [hashed last]; the preimage's hash before (40)
/// and long jump's (40), hop `k`'s type (a nibble), hop `k`'s field (40),
/// the end (40), `n` (2); Alice's choice (2).
pub fn hop_script(k: usize) -> ScriptBuf {
    // her choice is k
    let mut b = byte_number(Builder::new()).push_int(k as i64).push_opcode(OP_NUMEQUALVERIFY);
    // the next hash: the end at the last hop, else hop k's field
    b = byte_number(b).push_int(k as i64 + 1).push_opcode(OP_NUMEQUAL);
    b = b.push_opcode(OP_IF);
    for _ in 0..40 {
        b = b.push_int(40).push_opcode(OP_ROLL).push_opcode(OP_DROP);
    }
    b = b.push_opcode(OP_ELSE);
    for _ in 0..20 {
        b = b.push_opcode(OP_2DROP);
    }
    b = b.push_opcode(OP_ENDIF);
    // [before, jump, type, next]: the back-link by the type
    b = b.push_int(40).push_opcode(OP_ROLL).push_opcode(OP_IF);
    for _ in 0..40 {
        b = b.push_int(80).push_opcode(OP_ROLL).push_opcode(OP_DROP);
    }
    b = b.push_opcode(OP_ELSE);
    for _ in 0..40 {
        b = b.push_int(40).push_opcode(OP_ROLL).push_opcode(OP_DROP);
    }
    b = b.push_opcode(OP_ENDIF);
    b = eq_hash(b).push_opcode(OP_VERIFY);
    let mut s = b.into_script().into_bytes();
    s.extend_from_slice(preimage_hash_script().as_bytes());
    ScriptBuf::from_bytes(s)
}

/// `hop_range`: `[n 2, choice 2]`: fails unless Alice chose a hop beyond
/// the path.
pub fn hop_range_script() -> ScriptBuf {
    let b = byte_number(Builder::new()).push_opcode(OP_TOALTSTACK);
    byte_number(b).push_opcode(OP_FROMALTSTACK).push_opcode(OP_LESSTHANOREQUAL).push_opcode(OP_VERIFY).into_script()
}

/// The tail's keys: the hub's, one per field of each path link; Alice's,
/// one per choice (after either link).
#[derive(Clone, Debug)]
pub struct TailKeys {
    pub path: [Vec<lngap_lamport::winternitz::WotsPublic>; 2],
    pub hop: [lngap_lamport::winternitz::WotsPublic; 2],
}

// ----- the rules -----

fn w(r: std::ops::Range<usize>) -> Vec<In> {
    r.map(In::W).collect()
}

/// The end's preimage's parts (nibbles of the 57 bytes).
const PRE_ALL: std::ops::Range<usize> = 0..114;
const PRE_BEFORE: std::ops::Range<usize> = 0..40;
const PRE_JUMP: std::ops::Range<usize> = 40..80;
const PRE_WADDR: std::ops::Range<usize> = 80..88;
const PRE_WVALUE: std::ops::Range<usize> = 88..96;
const PRE_STEP: std::ops::Range<usize> = 106..114;

fn fin(s: &Schedule, f: usize) -> Msg {
    Msg::Field(s.depths(), f)
}

/// `jump` on path link `link`'s output (the hub's, after Alice's window):
/// the end is `h(jump(t + 1))` and isn't the long jump's hash Alice's
/// disputed step commits to. The hub's witness: the end's preimage.
pub fn jump_verdict(s: &Schedule, link: usize) -> Rule {
    let j = s.jump.expect("a jump list");
    // m0 the end, m1 n, m2 Alice's h(t), m3 her J, m4 her t + 1
    let msgs = vec![Msg::Path(0, P_END), Msg::Path(0, P_N), fin(s, FIELD_STEP_HASH), fin(s, FIELD_JUMP_HASH), fin(s, FIELD_SUCC)];
    let inputs = [w(PRE_ALL), ms(0, 0..40), ms(4, 0..8), w(PRE_STEP), ms(0, 0..40), ms(3, 0..40), ms(1, 0..2), ms(0, 0..40), ms(2, 0..40), ms(1, 0..2)].concat();
    Rule { name: "jump".into(), msgs, wit: 114, inputs, check: jump_verdict_script(&j, link) }
}

/// `read_<r>` on path link `link`'s output: the write at the end's step
/// contradicts Alice's read `r`.
pub fn read_verdict(s: &Schedule, link: usize, r: u8) -> Rule {
    let rec = |off: usize, len: usize| ms(3, digits(off, len));
    let (ra, rv, ls) = if r == 1 { (R_R1A, R_R1V, R_LS1) } else { (R_R2A, R_R2V, R_LS2) };
    // m0 the end, m1 n, m2 Alice's h(t), m3 her record
    let msgs = vec![Msg::Path(0, P_END), Msg::Path(0, P_N), fin(s, FIELD_STEP_HASH), fin(s, FIELD_RECORD)];
    let inputs = [
        w(PRE_ALL),
        ms(0, 0..40),
        w(PRE_WADDR),
        rec(ra, 4),
        w(PRE_WVALUE),
        rec(rv, 4),
        w(PRE_STEP),
        rec(ls, 8),
        rec(R_STEP, 4),
        ms(1, 0..2),
        ms(0, 0..40),
        ms(2, 0..40),
        ms(1, 0..2),
    ]
    .concat();
    Rule { name: format!("read_{r}"), msgs, wit: 114, inputs, check: read_verdict_script(link) }
}

/// The verdicts on path link `link`'s output.
pub fn verdicts(s: &Schedule, link: usize) -> Vec<Rule> {
    vec![jump_verdict(s, link), read_verdict(s, link, 1), read_verdict(s, link, 2)]
}

/// `hop_<k>` after Alice's choice on path link `link`'s output: the hub
/// reveals `h(x_k)`'s preimage, which hashes to it and links back (by hop
/// `k`'s type) to the next hash.
pub fn hop_rule(s: &Schedule, link: usize, k: usize) -> Rule {
    let xk = if k == 0 { fin(s, FIELD_STEP_HASH) } else { let (l, f) = hop_field(k - 1); Msg::Path(l, f) };
    let (l, f) = hop_field(k);
    // m0 her choice, m1 n, m2 the types, m3 the end, m4 h(x_k), m5 hop k's field
    let msgs = vec![Msg::Hop(link), Msg::Path(0, P_N), Msg::Path(0, P_TYPES), Msg::Path(0, P_END), xk, Msg::Path(l, f)];
    let inputs = [w(PRE_ALL), ms(4, 0..40), w(PRE_BEFORE), w(PRE_JUMP), vec![In::M(2, k)], ms(5, 0..40), ms(3, 0..40), ms(1, 0..2), ms(0, 0..2)].concat();
    Rule { name: format!("hop_{k}"), msgs, wit: 114, inputs, check: hop_script(k) }
}

/// The hop rules after Alice's choice on path link `link`'s output (only
/// the posted hops), and `hop_range`.
pub fn hop_rules(s: &Schedule, link: usize) -> Vec<Rule> {
    let n = if link == 0 { CHUNK } else { MAX_HOPS };
    let mut v: Vec<Rule> = (0..n).map(|k| hop_rule(s, link, k)).collect();
    v.push(Rule { name: "hop_range".into(), msgs: vec![Msg::Path(0, P_N), Msg::Hop(link)], wit: 0, inputs: [ms(0, 0..2), ms(1, 0..2)].concat(), check: hop_range_script() });
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_path_round_trips() {
        let j = JumpList::new(11);
        let h = |x: u64| -> [u8; 20] {
            let mut b = [0u8; 20];
            b[..8].copy_from_slice(&x.to_be_bytes());
            b
        };
        for (t, y) in [(1500u64, 3u64), (1500, 1499), (1500, 1500), (2000, 1)] {
            let p = Path::build(&j, t, y, &h);
            let (a, b) = p.messages(&h(t));
            assert_eq!(a.len(), first_fields().iter().sum::<usize>());
            let (n, types, end, hops) = Path::parse(&a, &b);
            assert_eq!((n, &types, end), (p.n(), &p.types, p.end(&h(t))));
            assert_eq!(hops, p.hashes[..p.n().saturating_sub(1)].to_vec());
        }
    }
}
