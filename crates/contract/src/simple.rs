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

use crate::claim::{cur_sources, next_sources, park, timeout_leaf, unpark, ClaimKeys, ClaimSpec, Pred, Stage, Step};
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

/// Emit the predicate checks over a nibble space of `n` elements on the
/// stack (element `i` at depth `n - 1 - i`, nothing else above); each
/// result goes to the altstack. Returns the number of results.
pub(crate) fn preds_script(b: &mut Builder, preds: &[Pred], n: usize) -> usize {
    let d = |i: usize| (n - 1 - i) as i64;
    let mut results = 0;
    let mut bb = std::mem::replace(b, Builder::new());
    for p in preds {
        match p {
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
