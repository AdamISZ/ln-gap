//! The check chain: once level 1 has isolated a *simple* step (predicates,
//! copies, loads), the prover re-commits the step's input and output states
//! and the challenger disproves the step with one leaf:
//!
//! ```text
//! R_R   ─ q_round_R_check (Q's last index, simple-step variant)   → C_0  | timeout: P
//! C_0   ─ c_re_cur        (P re-commits cur)                      → C_0' | timeout: Q
//! C_0'  ─ c_re_next       (P re-commits next)                     → C_1  | timeout: Q
//! C_1   ─ simple_<step>   (Q: a predicate fails, or next is not the expected copy of cur)
//!       ─ re_cur_mismatch_<src> / re_next_mismatch_<src>          | timeout: P
//! ```

use anyhow::Result;
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_lamport::winternitz::WotsExt;

use crate::claim::{cur_sources, next_sources, park, timeout_leaf, unpark, ClaimKeys, ClaimSpec, Cmp, Pred, Stage, Step};
use crate::inner::{mismatch_leaf, wait_re_cur_tree, wait_re_next_tree};
use crate::script_hash::push_scriptnum;

/// Nibble indices of `D` from least to most significant when the 32 hash
/// bytes are read as a little-endian number.
fn le_order() -> Vec<usize> {
    let mut v = Vec::new();
    for byte in 0..32 {
        let w = byte / 4;
        let k = byte % 4;
        v.push(8 * w + 2 * k + 1); // low nibble
        v.push(8 * w + 2 * k); // high nibble
    }
    v
}

/// Push the big-endian number of the `len` nibbles at `off` (each picked
/// from depth `d(off + k)`, the running number sitting above them).
fn push_number(mut bb: Builder, d: &dyn Fn(usize) -> i64, off: usize, len: usize) -> Builder {
    assert!((1..=7).contains(&len), "a register number is 1..=7 nibbles");
    bb = bb.push_int(d(off)).push_opcode(OP_PICK);
    for k in 1..len {
        for _ in 0..4 {
            bb = bb.push_opcode(OP_DUP).push_opcode(OP_ADD);
        }
        bb = bb.push_int(d(off + k) + 1).push_opcode(OP_PICK).push_opcode(OP_ADD);
    }
    bb
}

/// Emit the predicate checks over a nibble space of `n` elements on the
/// stack (element `i` at depth `n - 1 - i`, nothing else above); each
/// result goes to the altstack. Returns the number of results.
pub(crate) fn preds_script(b: &mut Builder, preds: &[Pred], n: usize) -> usize {
    let d = |i: usize| (n - 1 - i) as i64;
    let mut results = 0;
    let mut bb = std::mem::replace(b, Builder::new());
    for p in preds {
        match p {
            Pred::NeConst { off, nibbles } => {
                // all equal, then negated: one result
                for (k, c) in nibbles.iter().enumerate() {
                    bb = bb.push_int(d(off + k) + k as i64).push_opcode(OP_PICK);
                    bb = push_scriptnum(bb, *c).push_opcode(OP_EQUAL);
                }
                for _ in 1..nibbles.len() {
                    bb = bb.push_opcode(OP_BOOLAND);
                }
                bb = bb.push_opcode(OP_NOT).push_opcode(OP_TOALTSTACK);
                results += 1;
            }
            Pred::NeNibbles { a, b: bo, n: len } => {
                // all equal, then negated: one result
                for k in 0..*len {
                    bb = bb.push_int(d(a + k) + k as i64).push_opcode(OP_PICK).push_int(d(bo + k) + k as i64 + 1).push_opcode(OP_PICK).push_opcode(OP_EQUAL);
                }
                for _ in 1..*len {
                    bb = bb.push_opcode(OP_BOOLAND);
                }
                bb = bb.push_opcode(OP_NOT).push_opcode(OP_TOALTSTACK);
                results += 1;
            }
            Pred::InRange { off, n: len, lo, hi } => {
                bb = push_number(bb, &d, *off, *len);
                bb = bb.push_int(i64::from(*lo)).push_int(i64::from(*hi)).push_opcode(OP_WITHIN).push_opcode(OP_TOALTSTACK);
                results += 1;
            }
            Pred::If { off, n: len, cmp, value, then } => {
                let k = p.n_results();
                bb = push_number(bb, &d, *off, *len);
                bb = bb.push_int(i64::from(*value)).push_opcode(match cmp {
                    Cmp::Eq => OP_NUMEQUAL,
                    Cmp::Ge => OP_GREATERTHANOREQUAL,
                });
                bb = bb.push_opcode(OP_IF);
                let inner = preds_script(&mut bb, then, n);
                assert_eq!(inner, k);
                bb = bb.push_opcode(OP_ELSE);
                for _ in 0..k {
                    bb = bb.push_opcode(OP_PUSHNUM_1).push_opcode(OP_TOALTSTACK);
                }
                bb = bb.push_opcode(OP_ENDIF);
                results += k;
            }
            Pred::EqConst { off, nibbles } => {
                for (k, c) in nibbles.iter().enumerate() {
                    bb = bb.push_int(d(off + k)).push_opcode(OP_PICK);
                    bb = push_scriptnum(bb, *c).push_opcode(OP_EQUAL).push_opcode(OP_TOALTSTACK);
                    results += 1;
                }
            }
            Pred::EqNibbles { a, b: bo, n: len } => {
                for k in 0..*len {
                    bb = bb.push_int(d(a + k)).push_opcode(OP_PICK).push_int(d(bo + k) + 1).push_opcode(OP_PICK).push_opcode(OP_EQUAL).push_opcode(OP_TOALTSTACK);
                    results += 1;
                }
            }
            Pred::LeTarget { target } => {
                // acc = (D <= t) built from the least significant nibble up:
                // acc' = (nib < t) || (nib == t && acc)
                let order = le_order();
                let tn: Vec<u8> = (0..64).map(|k| { let byte = target[k / 2]; if k % 2 == 0 { byte & 15 } else { byte >> 4 } }).collect();
                bb = bb.push_int(d(order[0])).push_opcode(OP_PICK);
                bb = push_scriptnum(bb, tn[0]).push_opcode(OP_LESSTHANOREQUAL);
                for k in 1..64 {
                    bb = bb.push_int(d(order[k]) + 1).push_opcode(OP_PICK).push_opcode(OP_DUP);
                    bb = push_scriptnum(bb, tn[k]).push_opcode(OP_LESSTHAN).push_opcode(OP_SWAP);
                    bb = push_scriptnum(bb, tn[k]).push_opcode(OP_EQUAL).push_opcode(OP_ROT).push_opcode(OP_BOOLAND).push_opcode(OP_BOOLOR);
                }
                bb = bb.push_opcode(OP_TOALTSTACK);
                results += 1;
            }
            Pred::LeTargetBe { off, target } => {
                // big-endian: the last nibble is least significant; fold from it up
                let len = target.len();
                bb = bb.push_int(d(off + len - 1)).push_opcode(OP_PICK);
                bb = push_scriptnum(bb, target[len - 1]).push_opcode(OP_LESSTHANOREQUAL);
                for k in (0..len - 1).rev() {
                    bb = bb.push_int(d(off + k) + 1).push_opcode(OP_PICK).push_opcode(OP_DUP);
                    bb = push_scriptnum(bb, target[k]).push_opcode(OP_LESSTHAN).push_opcode(OP_SWAP);
                    bb = push_scriptnum(bb, target[k]).push_opcode(OP_EQUAL).push_opcode(OP_ROT).push_opcode(OP_BOOLAND).push_opcode(OP_BOOLOR);
                }
                bb = bb.push_opcode(OP_TOALTSTACK);
                results += 1;
            }
            Pred::EqConstBit { nib, bit, off, if0, if1 } => {
                assert_eq!(if0.len(), if1.len());
                // the selector bit: the nibble lies in one of the ranges where bit `bit` is set
                let step = 1usize << (bit + 1);
                let half = 1usize << bit;
                let ranges: Vec<(i64, i64)> = (0..16 / step).map(|m| ((m * step + half) as i64, (m * step + step) as i64)).collect();
                bb = bb.push_int(d(*nib)).push_opcode(OP_PICK);
                for (k, (lo, hi)) in ranges.iter().enumerate() {
                    if k + 1 < ranges.len() {
                        bb = bb.push_opcode(OP_DUP);
                    }
                    bb = bb.push_int(*lo).push_int(*hi).push_opcode(OP_WITHIN);
                    if k + 1 < ranges.len() {
                        bb = bb.push_opcode(OP_TOALTSTACK);
                    }
                }
                for _ in 1..ranges.len() {
                    bb = bb.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLOR);
                }
                // both branches push the same number of results
                bb = bb.push_opcode(OP_IF);
                for (k, c) in if1.iter().enumerate() {
                    bb = bb.push_int(d(off + k)).push_opcode(OP_PICK);
                    bb = push_scriptnum(bb, *c).push_opcode(OP_EQUAL).push_opcode(OP_TOALTSTACK);
                }
                bb = bb.push_opcode(OP_ELSE);
                for (k, c) in if0.iter().enumerate() {
                    bb = bb.push_int(d(off + k)).push_opcode(OP_PICK);
                    bb = push_scriptnum(bb, *c).push_opcode(OP_EQUAL).push_opcode(OP_TOALTSTACK);
                }
                bb = bb.push_opcode(OP_ENDIF);
                results += if0.len();
            }
        }
    }
    *b = bb;
    results
}

/// Pop `results` booleans from the altstack, AND them, and negate: true iff any check failed.
pub(crate) fn finish_results(mut b: Builder, results: usize) -> Builder {
    assert!(results > 0, "a disprove leaf needs at least one check");
    b = b.push_opcode(OP_FROMALTSTACK);
    for _ in 1..results {
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLAND);
    }
    b.push_opcode(OP_NOT)
}

/// The `simple_<step>` disprove leaf. Stack after the signature checks:
/// next's nibbles (deeper), cur's nibbles (top), each `8 n_words` with the
/// last nibble on top. True iff a predicate fails on cur or next is not
/// the expected transform of cur.
///
/// Witness (after Q's signature): `re_cur`'s signature, then `re_next`'s.
pub fn simple_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, n_words: usize, step: &Step) -> (String, ScriptBuf) {
    let Step::Simple { name, preds, copies } = step else { panic!("not a simple step") };
    let q = ctx.key(prover.other()).payment;
    let ik = keys.inner.as_ref().expect("inner keys");
    let n = 8 * n_words;
    let mut b = Builder::new().checksigverify(&q).wots_verify(&ik.re_cur);
    b = park(b, n);
    b = b.wots_verify(&ik.re_next);
    b = unpark(b, n);
    // depths: cur nibble j at n-1-j; next nibble i at 2n-1-i (nothing else is pushed between picks)
    let cur_d = |j: usize| (n - 1 - j) as i64;
    let next_d = |i: usize| (2 * n - 1 - i) as i64;
    let mut results = 0;
    for i in 0..n {
        let src = copies.iter().find(|c| i >= c.dst && i < c.dst + c.n).map(|c| c.src + (i - c.dst)).unwrap_or(i);
        b = b.push_int(next_d(i)).push_opcode(OP_PICK).push_int(cur_d(src) + 1).push_opcode(OP_PICK).push_opcode(OP_EQUAL).push_opcode(OP_TOALTSTACK);
        results += 1;
    }
    results += preds_script(&mut b, preds, n);
    for _ in 0..n {
        b = b.push_opcode(OP_2DROP);
    }
    let script = finish_results(b, results).into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("simple_{}_{}", name, hex::encode(&h[..4])), script)
}

/// `C_1`: the challenger disproves the isolated simple step, or the prover times out.
pub fn check_terminal_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec) -> Result<TapTree> {
    let mut leaves: Vec<Leaf> = Vec::new();
    let mut push = |name: String, script: ScriptBuf| {
        if !leaves.iter().any(|l| l.name == name) {
            leaves.push(Leaf::new(name, script, Timelock::NONE));
        }
    };
    for s in &spec.steps {
        if matches!(s, Step::Simple { .. }) {
            let (name, script) = simple_leaf(ctx, prover, keys, spec.n_words, s);
            push(name, script);
        }
    }
    for src in cur_sources(spec) {
        let (name, script) = mismatch_leaf(ctx, prover, keys, spec.n_words, false, &src);
        push(name, script);
    }
    for src in next_sources(spec) {
        let (name, script) = mismatch_leaf(ctx, prover, keys, spec.n_words, true, &src);
        push(name, script);
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// The check chain's stages (starting with `q_round_R_check` spending `R_R`)
/// and its output trees `C_0, C_0', C_1`.
pub fn check_chain(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec) -> Result<(Vec<Stage>, Vec<TapTree>)> {
    let q = prover.other();
    let rr = spec.rounds();
    let trees = vec![wait_re_cur_tree(ctx, prover, keys, false)?, wait_re_next_tree(ctx, prover, keys, false)?, check_terminal_tree(ctx, prover, keys, spec)?];
    let leaves = [format!("q_round_{rr}_check"), "c_re_cur".into(), "c_re_next".into()];
    let whats = [format!("{q} picks a segment in round {rr} (a simple step)"), format!("{prover} re-commits the step's input state"), format!("{prover} re-commits the step's output state")];
    let stages = leaves.into_iter().zip(trees.iter().cloned()).zip(whats).map(|((leaf, next), what)| Stage { leaf, next, what }).collect();
    Ok((stages, trees))
}

#[cfg(test)]
mod pred_tests {
    //! Every predicate kind's script against its native evaluation, through
    //! the interpreter, on random nibble spaces.
    use super::*;
    use crate::claim::nibbles_number;
    use lngap_script32::sim;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// Run the predicates over `space` and return whether the leaf would
    /// accept, i.e. whether some predicate fails (the disprove verdict).
    fn disproves(preds: &[Pred], space: &[u8]) -> bool {
        let mut b = Builder::new();
        let results = preds_script(&mut b, preds, space.len());
        let script = finish_results(b, results).into_script();
        let stack: Vec<i64> = space.iter().map(|&x| i64::from(x)).collect();
        let out = sim::run_nums(&script, stack).unwrap_or_else(|e| panic!("script error: {e}"));
        *out.last().unwrap() != 0
    }

    #[test]
    fn gates_ranges_and_not_equal_match_native() {
        let mut rng = Rng(0xabcdef1234567);
        let n = 40;
        for round in 0..400 {
            let mut space: Vec<u8> = (0..n).map(|_| rng.below(16) as u8).collect();
            // keep small numbers likely: the gate register is nibbles 30..32
            if round % 2 == 0 {
                space[30] = 0;
                space[31] = rng.below(12) as u8;
            }
            let value = rng.below(12) as u32;
            let c: Vec<u8> = (0..4).map(|_| rng.below(16) as u8).collect();
            let preds = vec![
                Pred::If { off: 30, n: 2, cmp: Cmp::Eq, value, then: vec![Pred::EqConst { off: 0, nibbles: c.clone() }, Pred::EqNibbles { a: 4, b: 8, n: 3 }] },
                Pred::If { off: 30, n: 2, cmp: Cmp::Ge, value, then: vec![Pred::NeConst { off: 12, nibbles: c.clone() }] },
                Pred::InRange { off: 30, n: 2, lo: 1, hi: 9 },
                Pred::NeConst { off: 16, nibbles: vec![space[16], space[17]] },
                Pred::NeNibbles { a: 4, b: 8, n: 3 },
                Pred::NeNibbles { a: 24, b: 26, n: 2 },
                Pred::If { off: 20, n: 1, cmp: Cmp::Eq, value: u32::from(space[20]), then: vec![Pred::If { off: 21, n: 1, cmp: Cmp::Ge, value: 8, then: vec![Pred::EqConst { off: 22, nibbles: vec![space[22]] }] }] },
            ];
            // sometimes force predicates to hold, so both verdicts are exercised
            if round % 3 == 0 {
                space[0..4].copy_from_slice(&c);
                let tmp = space[4..7].to_vec();
                space[8..11].copy_from_slice(&tmp);
                space[31] = 3;
                space[30] = 0;
            }
            for p in &preds {
                let native = !p.holds(&space);
                let script = disproves(std::slice::from_ref(p), &space);
                assert_eq!(script, native, "{} on {:?}", p.name(), &space[..32]);
            }
            let native_all = preds.iter().any(|p| !p.holds(&space));
            assert_eq!(disproves(&preds, &space), native_all);
            assert_eq!(nibbles_number(&space, 30, 2), u32::from(space[30]) * 16 + u32::from(space[31]));
        }
    }
}
