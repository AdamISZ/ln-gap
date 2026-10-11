//! The jump list's arithmetic in Script, over step numbers as 8 nibbles
//! (a 32-bit word, big-endian, the most significant nibble deepest).
//!
//! Script numbers hold 31 bits plus a sign, enough for step numbers below
//! `2^29`; a word's nibbles are folded into a number by Horner's rule with
//! doublings, and split into bits by comparisons.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;

use crate::jump::JumpList;

/// `[n_0 .. n_7]` (n_7 on top) -> the number they spell.
pub fn word_to_number(b: Builder) -> Builder {
    let mut b = b;
    for k in 0..8 {
        if k == 0 {
            b = b.push_int(7).push_opcode(OP_ROLL);
            continue;
        }
        for _ in 0..4 {
            b = b.push_opcode(OP_DUP).push_opcode(OP_ADD);
        }
        b = b.push_int((8 - k) as i64).push_opcode(OP_ROLL).push_opcode(OP_ADD);
    }
    b
}

/// `[x]` -> `[b_{n-1} .. b_0]` (b_0, the least significant, on top), for
/// `0 <= x < 2^n`: by comparisons, from the top bit down.
pub fn number_to_bits(b: Builder, n: u32) -> Builder {
    let mut b = b;
    for k in (0..n).rev() {
        // [.., x] -> [.., bit, x - bit 2^k]
        let p = 1i64 << k;
        b = b
            .push_opcode(OP_DUP)
            .push_int(p)
            .push_opcode(OP_GREATERTHANOREQUAL)
            .push_opcode(OP_DUP)
            .push_opcode(OP_TOALTSTACK)
            .push_opcode(OP_IF)
            .push_int(p)
            .push_opcode(OP_SUB)
            .push_opcode(OP_ENDIF)
            .push_opcode(OP_FROMALTSTACK)
            .push_opcode(OP_SWAP);
    }
    // [.., b_{n-1}, .., b_0, 0]
    b.push_opcode(OP_DROP)
}

/// `[s]` (a number) -> `[jump(s)]`, for `1 <= s < 2^bits`.
pub fn jump_number(b: Builder, j: &JumpList) -> Builder {
    let (n, l) = (j.bits, j.counter);
    // [s] -> [s, b_{n-1} .. b_0]
    let mut b = b.push_opcode(OP_DUP);
    b = number_to_bits(b, n);
    // c = sum of b_k 2^k, k < l; b_k at depth k
    b = b.push_int(0);
    for k in 0..l {
        // b_k is at depth k + 1 (the sum on top)
        b = b.push_int(i64::from(k) + 1).push_opcode(OP_PICK).push_opcode(OP_IF).push_int(1i64 << k).push_opcode(OP_ADD).push_opcode(OP_ENDIF);
    }
    // [s, bits.., c]: low = sum of b_k 2^k for k <= c; pow = 2^c
    b = b.push_int(0).push_int(0);
    // [s, bits.., c, low, pow]
    for k in 0..n {
        // b_k at depth k + 3
        b = b
            .push_int(i64::from(k))
            .push_int(3)
            .push_opcode(OP_PICK) // c
            .push_opcode(OP_LESSTHANOREQUAL) // k <= c
            .push_int(i64::from(k) + 4)
            .push_opcode(OP_PICK) // b_k
            .push_opcode(OP_BOOLAND)
            .push_opcode(OP_IF)
            .push_opcode(OP_SWAP)
            .push_int(1i64 << k)
            .push_opcode(OP_ADD)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_ENDIF)
            .push_int(i64::from(k))
            .push_int(3)
            .push_opcode(OP_PICK) // c
            .push_opcode(OP_NUMEQUAL)
            .push_opcode(OP_IF)
            .push_opcode(OP_DROP)
            .push_int(1i64 << k)
            .push_opcode(OP_ENDIF);
    }
    // the selected bit: b_c, when c is a data bit (else 0)
    // [s, bits.., c, low, pow] -> long = c >= l && c < n && b_c
    b = b.push_int(2).push_opcode(OP_PICK); // c
    b = b.push_opcode(OP_DUP).push_int(i64::from(l)).push_opcode(OP_GREATERTHANOREQUAL).push_opcode(OP_SWAP).push_int(i64::from(n)).push_opcode(OP_LESSTHAN).push_opcode(OP_BOOLAND);
    b = b.push_opcode(OP_IF).push_int(2).push_opcode(OP_PICK).push_int(3).push_opcode(OP_ADD).push_opcode(OP_PICK).push_opcode(OP_ELSE).push_int(0).push_opcode(OP_ENDIF);
    // [s, bits.., c, low, pow, long]
    b = b.push_opcode(OP_TOALTSTACK).push_opcode(OP_TOALTSTACK).push_opcode(OP_TOALTSTACK).push_opcode(OP_TOALTSTACK);
    // drop the bits
    for _ in 0..n / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    if n % 2 == 1 {
        b = b.push_opcode(OP_DROP);
    }
    // [s]; alt: long, pow, low, c (c on top)
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_FROMALTSTACK).push_opcode(OP_FROMALTSTACK).push_opcode(OP_FROMALTSTACK);
    // [s, c, low, pow, long]
    b = b
        .push_opcode(OP_IF)
        // s - low + pow - 2^l + c - 1
        .push_int(1i64 << l)
        .push_opcode(OP_SUB)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_SUB)
        .push_opcode(OP_ADD)
        .push_opcode(OP_ADD)
        .push_opcode(OP_1SUB)
        .push_opcode(OP_ELSE)
        .push_opcode(OP_2DROP)
        .push_opcode(OP_DROP)
        .push_opcode(OP_1SUB)
        .push_opcode(OP_ENDIF);
    b
}

/// `[s_word 8, y_word 8]` -> fails unless `y == jump(s)` (consumes both).
pub fn verify_jump(b: Builder, j: &JumpList) -> Builder {
    let b = word_to_number(b).push_opcode(OP_TOALTSTACK);
    let b = jump_number(word_to_number(b), j);
    b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_NUMEQUALVERIFY)
}

/// `[t_word 8, s_word 8]` -> fails unless `s != t + 1` (a disprove).
pub fn verify_not_succ(b: Builder) -> Builder {
    let b = word_to_number(b).push_opcode(OP_TOALTSTACK);
    word_to_number(b).push_opcode(OP_1ADD).push_opcode(OP_FROMALTSTACK).push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_VERIFY)
}

/// `[t_word 8, s_word 8]` -> fails unless `s == t + 1`.
pub fn verify_succ(b: Builder) -> Builder {
    let b = word_to_number(b).push_opcode(OP_TOALTSTACK);
    word_to_number(b).push_opcode(OP_1ADD).push_opcode(OP_FROMALTSTACK).push_opcode(OP_NUMEQUALVERIFY)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nib(x: u32) -> Vec<Vec<u8>> {
        x.to_be_bytes().iter().flat_map(|b| [b >> 4, b & 15]).map(|d| if d == 0 { vec![] } else { vec![d] }).collect()
    }

    fn run(b: Builder, stack: Vec<Vec<u8>>) -> bool {
        let s = b.push_opcode(OP_PUSHNUM_1).into_script();
        matches!(lngap_script32::sim::run(s.as_script(), stack), Ok(st) if st.len() == 1 && st[0] == [1])
    }

    #[test]
    fn the_jump_in_script() {
        for bits in [11u32, 29] {
            let j = JumpList::new(bits);
            let script = verify_jump(Builder::new(), &j);
            let mut cases: Vec<u64> = if bits == 11 { (1..(1 << 11)).collect() } else { vec![] };
            let mut x: u64 = 0x2545f4914f6cdd1d;
            for _ in 0..3000 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                cases.push(x % ((1 << bits) - 1) + 1);
            }
            for s in cases {
                let y = j.jump(s);
                let ok = run(Builder::from(script.clone().into_script().into_bytes()), [nib(s as u32), nib(y as u32)].concat());
                assert!(ok, "{bits} bits: jump({s}) = {y}");
                let bad = run(Builder::from(script.clone().into_script().into_bytes()), [nib(s as u32), nib(y as u32 ^ 1)].concat());
                assert!(!bad, "{bits} bits: jump({s}) isn't {}", y ^ 1);
            }
            println!("JSCRIPT the jump check for {bits}-bit steps: {} bytes", script.clone().into_script().len());
        }
    }

    #[test]
    fn the_successor_in_script() {
        for t in [0u32, 1, 15, 16, 255, 0xffff, 0x1fff_fffe] {
            assert!(run(verify_succ(Builder::new()), [nib(t), nib(t + 1)].concat()), "{t} + 1");
            assert!(!run(verify_succ(Builder::new()), [nib(t), nib(t + 2)].concat()), "{t} + 2");
        }
    }
}
