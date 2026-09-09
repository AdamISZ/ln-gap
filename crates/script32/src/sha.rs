//! SHA-256 pieces as Script: the round function and the message-schedule
//! step, plus native references for tests.

use crate::{Stack, Tables};

pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Tables the round and schedule leaves need.
pub const TABLES: Tables = Tables { xor: true, and: true, shifts: [false, true, true, true] };

// ----- native references -----

pub fn round_native(state: &[u32; 8], w: u32, k: u32) -> [u32; 8] {
    let [a, b, c, d, e, f, g, h] = *state;
    let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
    let ch = (e & f) ^ (!e & g);
    let t1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(k).wrapping_add(w);
    let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
    let maj = (a & b) ^ (a & c) ^ (b & c);
    let t2 = s0.wrapping_add(maj);
    [t1.wrapping_add(t2), a, b, c, d.wrapping_add(t1), e, f, g]
}

pub fn schedule_native(w2: u32, w7: u32, w15: u32, w16: u32) -> u32 {
    let s0 = w15.rotate_right(7) ^ w15.rotate_right(18) ^ (w15 >> 3);
    let s1 = w2.rotate_right(17) ^ w2.rotate_right(19) ^ (w2 >> 10);
    w16.wrapping_add(s0).wrapping_add(w7).wrapping_add(s1)
}

// ----- Script -----

/// `Σ`-style function of the top word: rotr a ⊕ rotr b ⊕ (rotr | shr) c. Consumes the word.
fn sigma(s: &mut Stack, a: u32, b: u32, c: u32, last_is_shift: bool) {
    s.pick_word(0);
    s.rotr_word(a);
    s.word_to_alt();
    s.pick_word(0);
    s.rotr_word(b);
    s.word_to_alt();
    if last_is_shift {
        s.shr_word(c);
    } else {
        s.rotr_word(c);
    }
    s.word_from_alt();
    s.xor_word();
    s.word_from_alt();
    s.xor_word();
}

/// Round body. Stack in (top first): `W_i` word, then the 8 state words with
/// `h` on top and `a` deepest... precisely: inputs are pushed `a, b, …, h, W`
/// so `W` is on top and `a` deepest. Stack out: the new state `a'..h'` with
/// `h'` on top. Tables must already be pushed and the inputs rolled above.
pub fn round_body(s: &mut Stack, k: u32) {
    // depths (word index from the top): W=0, h=1, g=2, f=3, e=4, d=5, c=6, b=7, a=8
    // t1 = h + S1(e) + ch(e,f,g) + K + W
    s.pick_word(8 * 4); // e
    sigma(s, 6, 11, 25, false); // S1(e)
    // ch = (e & f) ^ (!e & g)
    s.pick_word(8 * 5); // e (S1 now on top: e is one word deeper)
    s.pick_word(8 * 5); // f
    s.and_word(); // e&f
    s.pick_word(8 * 6); // e
    s.not_word();
    s.pick_word(8 * 5); // g
    s.and_word();
    s.xor_word(); // ch
    s.add_word(); // S1 + ch
    s.pick_word(8 * 2); // h
    s.add_word();
    s.push_word(k);
    s.add_word();
    s.pick_word(8 * 1); // W
    s.add_word(); // t1 on top; below: W h g f e d c b a
    // t2 = S0(a) + maj(a,b,c)
    s.pick_word(8 * 9); // a
    sigma(s, 2, 13, 22, false);
    s.pick_word(8 * 10); // a
    s.pick_word(8 * 10); // b
    s.and_word();
    s.pick_word(8 * 11); // a
    s.pick_word(8 * 10); // c
    s.and_word();
    s.xor_word(); // (a&b)^(a&c) on top; below: S0 t1 W h g f e d c b a
    s.pick_word(8 * 10); // b
    s.pick_word(8 * 10); // c
    s.and_word();
    s.xor_word(); // maj
    s.add_word(); // t2 on top; below: t1 W h g f e d c b a
    // new state: a' = t1 + t2, b' = a, c' = b, d' = c, e' = d + t1, f' = e, g' = f, h' = g
    s.pick_word(8 * 1); // t1
    s.add_word(); // a'   ; stack: a' t1 W h g f e d c b a  (a' on top)
    // Park the outputs h', g', ..., b', a' in that order so that popping restores a' first (deepest)
    // and h' last (on top).
    // h' = g, g' = f, f' = e, e' = d + t1, d' = c, c' = b, b' = a, a' (on top)
    // h' = g : g at word depth 4 -> park
    s.pick_word(8 * 4);
    s.word_to_alt();
    s.pick_word(8 * 5); // f -> g'
    s.word_to_alt();
    s.pick_word(8 * 6); // e -> f'
    s.word_to_alt();
    s.pick_word(8 * 7); // d
    s.pick_word(8 * 2); // t1
    s.add_word(); // e'
    s.word_to_alt();
    s.pick_word(8 * 8); // c -> d'
    s.word_to_alt();
    s.pick_word(8 * 9); // b -> c'
    s.word_to_alt();
    s.pick_word(8 * 10); // a -> b'
    s.word_to_alt();
    s.word_to_alt(); // a' (on top of the stack) -> parked last
    // drop everything else: t1 W h g f e d c b a = 10 words
    for _ in 0..10 {
        s.drop_word();
    }
    // restore a'..h' (a' pops first -> deepest; h' last -> top)
    for _ in 0..8 {
        s.word_from_alt();
    }
}

/// Schedule step body. Stack in (top first): `W[i-16]`, `W[i-15]`, `W[i-7]`, `W[i-2]`
/// (i.e. pushed in the order w2, w7, w15, w16 so w16 is on top). Stack out: `W[i]`.
pub fn schedule_body(s: &mut Stack) {
    // depths: w16=0, w15=1, w7=2, w2=3
    s.pick_word(8 * 1); // w15
    sigma(s, 7, 18, 3, true); // s0
    s.add_word(); // w16 + s0 ; stack: sum w15 w7 w2
    s.roll_word(8 * 2); // w7 to top
    s.add_word(); // sum ; stack: sum w15 w2
    s.roll_word(8 * 2); // w2 to top
    sigma(s, 17, 19, 10, true); // s1
    s.add_word(); // W_i ; stack: W_i w15
    s.roll_word(8 * 1);
    s.drop_word();
}
