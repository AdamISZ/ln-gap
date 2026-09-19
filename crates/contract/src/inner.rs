//! The inner chain: once level 1 has isolated a *compression* step, the
//! prover re-commits the step's input and output states under
//! path-independent keys and the block words as 32-bit keys, publishes the
//! 48 schedule words, and the search continues over the 64 rounds (k = 8):
//!
//! ```text
//! R_R   ─ q_round_R  (Q's last index)                                      → S_0  | timeout: P
//! S_0   ─ p_re_cur   (P re-commits cur: n_words × 32-bit, + 16 block words) → S_0' | timeout: Q
//! S_0'  ─ p_re_next  (P re-commits next)                                    → S_1  | timeout: Q
//! S_1   ─ p_sched    (P commits W[16..64], 48 × 32-bit Winternitz)          → S_2  | timeout: Q
//! S_2   ─ p_inner_1  (P commits s_8, s_16, …, s_56)                         → I_1  | timeout: Q
//! I_1   ─ q_inner_1  (Q commits a 3-bit segment index)                      → S_3  | timeout: P
//!       ─ sched_i / block_j / re_cur_mismatch / re_next_mismatch / compress_copy (Q disproves)
//! S_3   ─ p_inner_2  (P commits the 7 states inside the chosen segment)     → I_2  | timeout: Q
//! I_2   ─ q_inner_2  (Q commits a 3-bit round index)                        → T    | timeout: P
//! T     ─ round_r    (Q disproves one SHA-256 round; r = 63 adds the feed-forward) | timeout: P
//! ```
//!
//! Inner states: `s_0 = init` (the IV or `D` of the re-committed cur),
//! `s_{r+1} = round(s_r, W[r])`, `s_64 = init + round(s_63, W[63])`, which
//! must equal `D` of the re-committed next.

use anyhow::Result;
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_lamport::gadgets::LamportExt;
use lngap_lamport::winternitz::{WotsExt, WotsPublic, WotsSig};
use lngap_lamport::PublicKey;
use lngap_n4bit::script;
use lngap_script32::sha::{add_states, differs_and_finish, round_body, round_native, schedule_body, schedule_native, K, TABLES};
use lngap_script32::Stack;
use serde::{Deserialize, Serialize};

use crate::claim::{all_paths, cur_sources, load_source, next_sources, park, state_nibbles, step_sources, timeout_leaf, unpark, wots_verify_drop, ChallengerKeys, ClaimKeys, ClaimSpec, HashKind, Init, Search, Src, Stage, StateSource, Step, IV};
use crate::instance::key_label;
use crate::script_hash::{nibbles, push_scriptnum};

pub const ROUNDS: u32 = 64;
pub const INNER_K: u32 = 8;
/// The inner search: 64 rounds, branching 8, two index rounds.
pub const SEARCH: Search = Search { n: ROUNDS, k: INNER_K };

/// The prover's inner-level keys for one depth.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InnerKeys {
    /// Re-commitments of the isolated step's input and output states (`n_words` words).
    pub re_cur: WotsPublic,
    pub re_next: WotsPublic,
    /// `block[j]`: block word `j` of the isolated compression (32-bit).
    pub block: Vec<WotsPublic>,
    /// `sched[i - 16]`: schedule word `W[i]`, `i` in 16..64 (32-bit).
    pub sched: Vec<WotsPublic>,
    /// `states[r - 1][t]`: inner round `r`, commitment `t` (256-bit).
    pub states: Vec<Vec<WotsPublic>>,
}

pub fn re_cur_label(id: u32, seq: u64, depth: u32) -> String {
    key_label(id, seq, depth, "claim/re/cur")
}
pub fn re_next_label(id: u32, seq: u64, depth: u32) -> String {
    key_label(id, seq, depth, "claim/re/next")
}
pub fn block_label(id: u32, seq: u64, depth: u32, j: u32) -> String {
    key_label(id, seq, depth, &format!("claim/re/block{j}"))
}
pub fn sched_label(id: u32, seq: u64, depth: u32, i: u32) -> String {
    key_label(id, seq, depth, &format!("claim/sched{i}"))
}
pub fn inner_state_label(id: u32, seq: u64, depth: u32, r: u32, t: u32) -> String {
    key_label(id, seq, depth, &format!("claim/inner{r}/state{t}"))
}
pub fn inner_index_label(id: u32, seq: u64, depth: u32, r: u32) -> String {
    key_label(id, seq, depth, &format!("claim/inner{r}/index"))
}

fn ik(keys: &ClaimKeys) -> &InnerKeys {
    keys.inner.as_ref().expect("inner keys")
}

// ----- native -----

/// The 64 schedule words of a block.
pub fn schedule(block: &[u8; 64]) -> [u32; 64] {
    let mut w = [0u32; 64];
    for i in 0..16 {
        w[i] = u32::from_be_bytes(block[4 * i..4 * i + 4].try_into().unwrap());
    }
    for i in 16..64 {
        w[i] = schedule_native(w[i - 2], w[i - 7], w[i - 15], w[i - 16]);
    }
    w
}

/// Inner states `s_0 … s_64` from `init` and a schedule; `cheat(r, s_r)`
/// may alter a state, and the alteration propagates.
pub fn round_states(init: &[u32; 8], w: &[u32; 64], cheat: Option<&dyn Fn(u32, &[u32; 8]) -> [u32; 8]>) -> Vec<[u32; 8]> {
    let mut v = vec![*init];
    for r in 0..64usize {
        let mut s = round_native(&v[r], w[r], K[r]);
        if r == 63 {
            for i in 0..8 {
                s[i] = s[i].wrapping_add(init[i]);
            }
        }
        if let Some(c) = cheat {
            s = c(r as u32 + 1, &s);
        }
        v.push(s);
    }
    v
}

/// Where a round leaf gets an inner state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InnerSource {
    /// `s_0`: the compression's init (`IV`, or `D` of the re-committed cur).
    Init(Init),
    /// `s_64`: `D` of the re-committed next.
    ReNext,
    /// The prover's commitment `t` (0-based) in inner round `r` (1-based).
    Inner(u32, u32),
}

/// Sources of the isolated round's input and claimed output, and the round index.
pub fn round_sources(init: Init, inner_path: &[u32], search: Search) -> (InnerSource, InnerSource, u32) {
    assert_eq!(inner_path.len() as u32, search.rounds());
    let mut lo_src = InnerSource::Init(init);
    let mut hi_src = InnerSource::ReNext;
    for (r, &j) in inner_path.iter().enumerate() {
        let r1 = r as u32 + 1;
        let new_lo = if j == 0 { lo_src.clone() } else { InnerSource::Inner(r1, j - 1) };
        let new_hi = if j == search.k - 1 { hi_src.clone() } else { InnerSource::Inner(r1, j) };
        lo_src = new_lo;
        hi_src = new_hi;
    }
    let (lo, len) = search.segment(inner_path);
    assert_eq!(len, 1);
    (lo_src, hi_src, lo)
}

// ----- leaf bodies -----

/// Verify an `n_words` re-commitment and keep only its `D` (words 0..`d_words`):
/// `8 * d_words` nibbles, parked.
fn load_d_of(b: Builder, pk: &WotsPublic, n_words: usize, d_words: usize) -> Builder {
    let mut b = b.wots_verify(pk);
    for _ in 0..(8 * n_words - 8 * d_words) / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    park(b, 8 * d_words)
}

/// Push a state (constant nibbles) or verify its commitment, then park the
/// `8 * d_words` D nibbles.
fn load_inner(b: Builder, src: &InnerSource, keys: &ClaimKeys, n_words: usize, d_words: usize) -> Builder {
    match src {
        InnerSource::Init(Init::Iv) => park(nibbles(&crate::script_hash::state_bytes(&IV)).into_iter().fold(b, push_scriptnum), 8 * d_words),
        InnerSource::Init(Init::D) => load_d_of(b, &ik(keys).re_cur, n_words, d_words),
        InnerSource::ReNext => load_d_of(b, &ik(keys).re_next, n_words, d_words),
        InnerSource::Inner(r, t) => park(b.wots_verify(&ik(keys).states[*r as usize - 1][*t as usize]), 8 * d_words),
    }
}

/// Verify schedule word `i` (a block key below 16) and park its 8 nibbles.
fn load_word(b: Builder, i: u32, keys: &ClaimKeys) -> Builder {
    let pk = if i < 16 { &ik(keys).block[i as usize] } else { &ik(keys).sched[i as usize - 16] };
    park(b.wots_verify(pk), 8)
}

/// Push the tables, then restore `n` parked nibbles above them (the last parked is deepest).
fn restore(b: Builder, n: usize) -> Stack {
    let mut s = Stack::new(b, TABLES);
    s.map(n as isize, |b| unpark(b, n));
    s
}

/// The `round_r` disprove leaf for a compression with init kind `init`:
/// true iff the prover's claimed `s_{r+1}` differs from `round(s_r, W[r])`
/// (plus `init` for `r = 63`). Path-independent.
///
/// Witness (consumption order, after Q's signature): `W[r]`, `s_r`, `init`
/// (if `r = 63` and `init = D`), `s_{r+1}` signatures (constants omitted).
pub fn round_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec, init: Init, r: u32) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let search = spec.inner_search();
    let n_words = spec.n_words;
    let d_words = spec.d_words();
    let d_nibbles = spec.d_nibbles();
    // Compute the inner path for round r (most-significant digit first).
    let inner_path: Vec<u32> = {
        let rounds = search.rounds();
        let mut path = Vec::with_capacity(rounds as usize);
        let mut divisor = search.n / search.k;
        let mut idx = r;
        for _ in 0..rounds {
            path.push(idx / divisor);
            idx %= divisor;
            divisor /= search.k;
        }
        path
    };
    let (in_src, out_src, rr) = round_sources(init, &inner_path, search);
    assert_eq!(rr, r);
    match spec.hash {
        HashKind::Sha256 => {
            let mut b = Builder::new().checksigverify(&q);
            // parked last comes back deepest: final layout is out, [init], in, W (top)
            b = load_word(b, r, keys);
            b = load_inner(b, &in_src, keys, n_words, d_words);
            let mut n = 72;
            if r == 63 {
                b = load_inner(b, &InnerSource::Init(init), keys, n_words, d_words);
                n += 64;
            }
            b = load_inner(b, &out_src, keys, n_words, d_words);
            n += 64;
            let mut s = restore(b, n);
            round_body(&mut s, K[r as usize]);
            if r == 63 {
                add_states(&mut s);
            }
            differs_and_finish(&mut s, 64);
            let script = s.into_builder().into_script();
            let h = lngap_btc::hash160(script.as_bytes());
            (format!("round_{}", hex::encode(&h[..4])), script)
        }
        HashKind::N4Bit => {
            let mut b = Builder::new().checksigverify(&q);
            // Load and park input state (d_nibbles nibbles)
            b = load_inner(b, &in_src, keys, n_words, d_words);
            // Load and park output state (d_nibbles nibbles)
            b = load_inner(b, &out_src, keys, n_words, d_words);
            // Push S-box table on main stack
            b = script::push_sbox_table(b);
            // Unpark input state onto table
            b = unpark(b, d_nibbles);
            // Run one SPN round: input → computed output
            b = script::spn_round_script(b, r as usize);
            // Stack: [table(16), computed(d_nibbles)]
            // Park computed, drop table, unpark computed
            b = park(b, d_nibbles);
            for _ in 0..script::SBOX_TABLE_SIZE {
                b = b.push_opcode(OP_DROP);
            }
            b = unpark(b, d_nibbles);
            // Stack: [computed(d_nibbles)]
            // Unpark output state
            b = unpark(b, d_nibbles);
            // Stack: [computed(d_nibbles), output(d_nibbles)] with output on top
            // Compare: true iff any pair differs
            b = differs_masked(b, d_nibbles, &vec![true; d_nibbles]);
            let script = b.into_script();
            let h = lngap_btc::hash160(script.as_bytes());
            (format!("round_{}", hex::encode(&h[..4])), script)
        }
    }
}

/// Witness args for [`round_leaf`] (after Q's signature).
pub fn round_witness(w_sig: &WotsSig, in_sig: Option<&WotsSig>, init_sig: Option<&WotsSig>, out_sig: &WotsSig) -> Vec<Vec<u8>> {
    let mut v = w_sig.consumption_order();
    for sig in [in_sig, init_sig].into_iter().flatten() {
        v.extend(sig.consumption_order());
    }
    v.extend(out_sig.consumption_order());
    v
}

/// The `sched_i` disprove leaf (`i` in 16..64): true iff the prover's `W[i]`
/// differs from the recurrence over its committed inputs. Path-independent.
///
/// Witness (consumption order, after Q's signature): signatures for the
/// inputs in [`sched_inputs`] order, then `W[i]`'s signature.
pub fn sched_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, i: u32) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let mut b = Builder::new().checksigverify(&q);
    for j in sched_inputs(i) {
        b = load_word(b, j, keys);
    }
    b = load_word(b, i, keys);
    let mut s = restore(b, 40);
    schedule_body(&mut s);
    differs_and_finish(&mut s, 8);
    let script = s.into_builder().into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("sched_{}", hex::encode(&h[..4])), script)
}

/// The recurrence inputs of `W[i]` in the order the leaf verifies them.
pub fn sched_inputs(i: u32) -> [u32; 4] {
    [i - 16, i - 15, i - 7, i - 2]
}

pub fn sched_witness(input_sigs: &[&WotsSig], w_sig: &WotsSig) -> Vec<Vec<u8>> {
    let mut v = Vec::new();
    for sig in input_sigs {
        v.extend(sig.consumption_order());
    }
    v.extend(w_sig.consumption_order());
    v
}

/// Compare two runs of `n` nibbles on the stack (the top run against the
/// one below it), dropping pairs where `mask` is false; leave true iff any
/// compared pair differs.
pub(crate) fn differs_masked(mut b: Builder, n: usize, mask: &[bool]) -> Builder {
    let mut compared = 0;
    for i in 0..n {
        b = b.push_int((2 * n - 1 - 2 * i) as i64).push_opcode(OP_ROLL).push_int((n - i) as i64).push_opcode(OP_ROLL);
        if mask[i] {
            b = b.push_opcode(OP_EQUAL).push_opcode(OP_TOALTSTACK);
            compared += 1;
        } else {
            b = b.push_opcode(OP_2DROP);
        }
    }
    b = b.push_opcode(OP_FROMALTSTACK);
    for _ in 1..compared {
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLAND);
    }
    b.push_opcode(OP_NOT)
}

/// `block_j`: block word `j` (fresh key) differs from its source in the
/// re-committed cur (or a constant). Witness: `block[j]` signature, then
/// `re_cur`'s (for a register source). Data sources have no leaf.
pub fn block_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, n_words: usize, j: usize, src: Src) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let mut b = Builder::new().checksigverify(&q).wots_verify(&ik(keys).block[j]);
    b = park(b, 8);
    match src {
        Src::Data(_) => panic!("data words have no block leaf"),
        Src::Const(c) => {
            b = nibbles(&c.to_be_bytes()).into_iter().fold(b, push_scriptnum);
        }
        Src::Reg(i) => {
            // verify re_cur, keep word i: drop the nibbles above it, park it, drop those below
            b = b.wots_verify(&ik(keys).re_cur);
            for _ in 0..(8 * n_words - 8 * (i + 1)) / 2 {
                b = b.push_opcode(OP_2DROP);
            }
            b = park(b, 8);
            for _ in 0..(8 * i) / 2 {
                b = b.push_opcode(OP_2DROP);
            }
            b = unpark(b, 8);
        }
    }
    b = unpark(b, 8);
    let script = differs_masked(b, 8, &[true; 8]).into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("block_{}", hex::encode(&h[..4])), script)
}

/// `re_cur_mismatch_<src>` / `re_next_mismatch_<src>`: the re-commitment
/// differs from the path's source. Witness: the re-commitment's signature,
/// then the source's (none for a constant).
pub fn mismatch_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, n_words: usize, which_next: bool, src: &StateSource) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let pk = if which_next { &ik(keys).re_next } else { &ik(keys).re_cur };
    let mut b = Builder::new().checksigverify(&q).wots_verify(pk);
    b = park(b, 8 * n_words);
    b = load_source(b, src, keys, n_words);
    b = unpark(b, 16 * n_words);
    let script = differs_masked(b, 8 * n_words, &vec![true; 8 * n_words]).into_script();
    (format!("re_{}_mismatch_{}", if which_next { "next" } else { "cur" }, src.name()), script)
}

/// `ckeep_<step>`: a compression changed a register it should not have
/// (anything but `D` and its copy destinations). Witness: `re_cur`'s
/// signature, then `re_next`'s.
pub fn ckeep_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec, step: &Step) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let n_words = spec.n_words;
    let mut b = Builder::new().checksigverify(&q).wots_verify(&ik(keys).re_cur);
    b = park(b, 8 * n_words);
    b = b.wots_verify(&ik(keys).re_next);
    b = unpark(b, 8 * n_words);
    let copy = step.copy_mask(n_words);
    let mask: Vec<bool> = (0..8 * n_words).map(|i| i >= spec.d_nibbles() && !copy[i]).collect();
    let script = differs_masked(b, 8 * n_words, &mask).into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("ckeep_{}", hex::encode(&h[..4])), script)
}

/// Verify the block words (word last first) and a state, parking each run,
/// then restore everything: the state ends deepest, the last block word's
/// last nibble on top. Witness order: `block[last] … block[0]`, then the state.
fn load_block_and_state(mut b: Builder, keys: &ClaimKeys, state_pk: &WotsPublic, n_words: usize, block_nibbles: usize) -> Builder {
    for pk in ik(keys).block.iter().rev() {
        b = park(b.wots_verify(pk), 8);
    }
    b = park(b.wots_verify(state_pk), 8 * n_words);
    unpark(b, 8 * n_words + block_nibbles)
}

/// `cpred_<step>`: a compression step's predicate fails over (re_cur,
/// block words). Witness: `block[last] … block[0]`, then `re_cur`'s signature.
pub fn cpred_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec, step: &Step) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let n_words = spec.n_words;
    let block_nibbles = spec.block_nibbles();
    let mut b = load_block_and_state(Builder::new().checksigverify(&q), keys, &ik(keys).re_cur, n_words, block_nibbles);
    let n = 8 * n_words + block_nibbles;
    let results = crate::simple::preds_script(&mut b, step.preds(), n);
    for _ in 0..n / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    let script = crate::simple::finish_results(b, results).into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("cpred_{}_{}", step.name(), hex::encode(&h[..4])), script)
}

/// `ccopy_<step>`: a compression's copy destination in re_next differs from
/// the block nibbles it should copy. Witness: `block[last] … block[0]`, then
/// `re_next`'s signature.
pub fn ccopy_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec, step: &Step) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let n_words = spec.n_words;
    let block_nibbles = spec.block_nibbles();
    let mut b = load_block_and_state(Builder::new().checksigverify(&q), keys, &ik(keys).re_next, n_words, block_nibbles);
    // depths: next nibble i at (n_next - 1 - i) + block_nibbles; block nibble k at block_nibbles - 1 - k
    let nn = 8 * n_words;
    let mut results = 0;
    for c in step.copies() {
        assert!(c.src >= nn, "compression copies read block nibbles");
        for k in 0..c.n {
            let next_d = (nn - 1 - (c.dst + k)) + block_nibbles;
            let blk_d = (block_nibbles - 1) as i64 - (c.src - nn + k) as i64;
            b = b.push_int(next_d as i64).push_opcode(OP_PICK).push_int(blk_d + 1).push_opcode(OP_PICK).push_opcode(OP_EQUAL).push_opcode(OP_TOALTSTACK);
            results += 1;
        }
    }
    for _ in 0..(nn + block_nibbles) / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    let script = crate::simple::finish_results(b, results).into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("ccopy_{}_{}", step.name(), hex::encode(&h[..4])), script)
}

// ----- trees and stages -----

fn wait_tree(ctx: &CommitCtx, prover: Role, leaf: &str, body: Builder) -> Result<TapTree> {
    let leaf = Leaf::new(leaf, body.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE);
    TapTree::new(vec![leaf, timeout_leaf(ctx, prover.other())])
}

/// `S_0`: waiting for the prover's re-commitment of cur and the block words.
pub fn wait_re_cur_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, with_blocks: bool) -> Result<TapTree> {
    let mut b = wots_verify_drop(ctx.two_of_two_verify(Builder::new()), &ik(keys).re_cur);
    if with_blocks {
        for pk in &ik(keys).block {
            b = wots_verify_drop(b, pk);
        }
    }
    wait_tree(ctx, prover, if with_blocks { "p_re_cur" } else { "c_re_cur" }, b)
}

/// `S_0'`: waiting for the prover's re-commitment of next.
pub fn wait_re_next_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, compress: bool) -> Result<TapTree> {
    let b = wots_verify_drop(ctx.two_of_two_verify(Builder::new()), &ik(keys).re_next);
    wait_tree(ctx, prover, if compress { "p_re_next" } else { "c_re_next" }, b)
}

/// `S_1`: waiting for the prover's schedule.
pub fn wait_sched_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys) -> Result<TapTree> {
    let mut b = ctx.two_of_two_verify(Builder::new());
    for pk in &ik(keys).sched {
        b = wots_verify_drop(b, pk);
    }
    wait_tree(ctx, prover, "p_sched", b)
}

/// `S_2` / `S_3`: waiting for the prover's inner round `r` states.
pub fn wait_inner_p_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, r: u32) -> Result<TapTree> {
    let mut b = ctx.two_of_two_verify(Builder::new());
    for pk in &ik(keys).states[r as usize - 1] {
        b = wots_verify_drop(b, pk);
    }
    wait_tree(ctx, prover, &format!("p_inner_{r}"), b)
}

/// Distinct `(j, source)` pairs among the spec's compression steps (data sources excluded).
pub fn block_sources(spec: &ClaimSpec) -> Vec<(usize, Src)> {
    let mut v: Vec<(usize, Src)> = Vec::new();
    for s in &spec.steps {
        if let Step::Compress { block, .. } = s {
            for (j, src) in block.iter().enumerate() {
                if !matches!(src, Src::Data(_)) && !v.contains(&(j, *src)) {
                    v.push((j, *src));
                }
            }
        }
    }
    v
}

/// Distinct init kinds among the spec's compression steps.
pub fn init_kinds(spec: &ClaimSpec) -> Vec<Init> {
    let mut v = Vec::new();
    for s in &spec.steps {
        if let Step::Compress { init, .. } = s {
            if !v.contains(init) {
                v.push(*init);
            }
        }
    }
    v
}

fn push_unique(leaves: &mut Vec<Leaf>, name: String, script: ScriptBuf) {
    if !leaves.iter().any(|l| l.name == name) {
        leaves.push(Leaf::new(name, script, Timelock::NONE));
    }
}

/// `I_r`: waiting for the challenger's inner index `r`; in round 1 the
/// challenger may instead disprove a schedule word, a block word, a
/// re-commitment, or a register the compression should not have changed.
pub fn wait_inner_q_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, ck: &ChallengerKeys, spec: &ClaimSpec, r: u32) -> Result<TapTree> {
    let pk = &ck.inner_indices[r as usize - 1];
    let mut b = ctx.two_of_two_verify(Builder::new());
    for i in (0..pk.n_bits()).rev() {
        b = b.bit_decode(&pk.bits[i]).push_opcode(OP_DROP);
    }
    let mut leaves = vec![Leaf::new(format!("q_inner_{r}"), b.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE)];
    if r == 1 {
        let n = spec.n_words;
        let bw = spec.hash.block_words();
        if spec.has_schedule() {
            for i in (bw as u32)..spec.inner_rounds() {
                let (name, script) = sched_leaf(ctx, prover, keys, i);
                push_unique(&mut leaves, name, script);
            }
        }
        for (j, src) in block_sources(spec) {
            let (name, script) = block_leaf(ctx, prover, keys, n, j, src);
            push_unique(&mut leaves, name, script);
        }
        for src in cur_sources(spec) {
            let (name, script) = mismatch_leaf(ctx, prover, keys, n, false, &src);
            push_unique(&mut leaves, name, script);
        }
        for src in next_sources(spec) {
            let (name, script) = mismatch_leaf(ctx, prover, keys, n, true, &src);
            push_unique(&mut leaves, name, script);
        }
        for step in &spec.steps {
            if !matches!(step, Step::Compress { .. }) {
                continue;
            }
            if n > spec.d_words() {
                let (name, script) = ckeep_leaf(ctx, prover, keys, spec, step);
                push_unique(&mut leaves, name, script);
            }
            if !step.preds().is_empty() {
                let (name, script) = cpred_leaf(ctx, prover, keys, spec, step);
                push_unique(&mut leaves, name, script);
            }
            if !step.copies().is_empty() {
                let (name, script) = ccopy_leaf(ctx, prover, keys, spec, step);
                push_unique(&mut leaves, name, script);
            }
        }
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// `T`: the challenger disproves one round, or the prover times out.
pub fn round_terminal_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec) -> Result<TapTree> {
    let mut leaves: Vec<Leaf> = Vec::new();
    let kinds = init_kinds(spec);
    for r in 0..spec.inner_rounds() {
        for init in &kinds {
            let (name, script) = round_leaf(ctx, prover, keys, spec, *init, r);
            push_unique(&mut leaves, name, script);
        }
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// The inner chain's stages (starting with `q_round_R` spending `R_R`) and
/// its output trees. For SHA-256 (with schedule): `S_0, S_0', S_1, S_2, I_1,
/// S_3, I_2, T`. For n4bit (no schedule): `S_0, S_0', I_1, S_3, I_2, T`.
pub fn compress_chain(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, ck: &ChallengerKeys, spec: &ClaimSpec) -> Result<(Vec<Stage>, Vec<TapTree>)> {
    let q = prover.other();
    let rr = spec.rounds();
    let has_sched = spec.has_schedule();
    let inner_search = spec.inner_search();
    let inner_rounds = inner_search.rounds();
    // Build trees dynamically depending on whether the hash has a schedule.
    let mut trees: Vec<TapTree> = Vec::new();
    let mut leaves: Vec<String> = Vec::new();
    let mut whats: Vec<String> = Vec::new();
    // S_0: re-commit cur + block words
    trees.push(wait_re_cur_tree(ctx, prover, keys, true)?);
    leaves.push("p_re_cur".into());
    whats.push(format!("{prover} re-commits the step's input state and block words"));
    // S_0': re-commit next
    trees.push(wait_re_next_tree(ctx, prover, keys, true)?);
    leaves.push("p_re_next".into());
    whats.push(format!("{prover} re-commits the step's output state"));
    if spec.flat_inner {
        // Flat inner: skip schedule + inner rounds, go directly to flat terminal
        trees.push(flat_terminal_tree(ctx, prover, keys, spec)?);
        leaves.push("flat_terminal".into());
        whats.push(format!("{} disproves the compression in one leaf", q));
    } else {
        // S_1: schedule (only if the hash has a schedule)
        if has_sched {
            trees.push(wait_sched_tree(ctx, prover, keys)?);
            leaves.push("p_sched".into());
            whats.push(format!("{prover} publishes the schedule words"));
        }
        // Inner bisection rounds
        for r in 1..=inner_rounds {
            trees.push(wait_inner_p_tree(ctx, prover, keys, r)?);
            leaves.push(format!("p_inner_{r}"));
            whats.push(format!("{prover} commits inner round {r} states"));
            trees.push(wait_inner_q_tree(ctx, prover, keys, ck, spec, r)?);
            leaves.push(format!("q_inner_{r}"));
            whats.push(format!("{q} picks a segment in inner round {r}"));
        }
        // T: terminal
        trees.push(round_terminal_tree(ctx, prover, keys, spec)?);
    }
    // The first leaf (spending R_R) is always q_round_{rr}
    let mut all_leaves = vec![format!("q_round_{rr}")];
    all_leaves.extend(leaves);
    let mut all_whats = vec![format!("{q} picks a segment in round {rr} (a compression step)")];
    all_whats.extend(whats);
    let stages = all_leaves.into_iter().zip(trees.iter().cloned()).zip(all_whats).map(|((leaf, next), what)| Stage { leaf, next, what }).collect();
    Ok((stages, trees))
}

/// The flat terminal for n4bit: one leaf recomputing all SPN rounds of
/// one compression step, using the re-committed input/output/block words.
/// Only used when `spec.flat_inner` is true. Replaces the entire inner
/// bisection (schedule + inner rounds + round terminal) with one leaf.
pub fn flat_terminal_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec) -> Result<TapTree> {
    let mut leaves: Vec<Leaf> = Vec::new();
    for path in crate::claim::all_paths(spec) {
        let (_, _, step_idx) = step_sources(spec, &path);
        let step = &spec.steps[step_idx as usize];
        if !matches!(step, Step::Compress { .. }) {
            continue;
        }
        let (name, script) = flat_round_leaf(ctx, prover, keys, spec, step_idx as usize);
        push_unique(&mut leaves, name, script);
    }
    // everything else a compression step asserts (as `I_1` does for the
    // round-level chain): block words against their sources, the
    // re-commitments against the path's commitments, untouched registers,
    // predicates and copies
    let n = spec.n_words;
    for (j, src) in block_sources(spec) {
        let (name, script) = block_leaf(ctx, prover, keys, n, j, src);
        push_unique(&mut leaves, name, script);
    }
    for src in cur_sources(spec) {
        let (name, script) = mismatch_leaf(ctx, prover, keys, n, false, &src);
        push_unique(&mut leaves, name, script);
    }
    for src in next_sources(spec) {
        let (name, script) = mismatch_leaf(ctx, prover, keys, n, true, &src);
        push_unique(&mut leaves, name, script);
    }
    for step in &spec.steps {
        if !matches!(step, Step::Compress { .. }) {
            continue;
        }
        if n > spec.d_words() {
            let (name, script) = ckeep_leaf(ctx, prover, keys, spec, step);
            push_unique(&mut leaves, name, script);
        }
        if !step.preds().is_empty() {
            let (name, script) = cpred_leaf(ctx, prover, keys, spec, step);
            push_unique(&mut leaves, name, script);
        }
        if !step.copies().is_empty() {
            let (name, script) = ccopy_leaf(ctx, prover, keys, spec, step);
            push_unique(&mut leaves, name, script);
        }
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// Build a flat terminal leaf that recomputes all n4bit SPN rounds for
/// compression step `step_idx`. Verifies input state, block words, and
/// output state via WOTS, absorbs the block, runs all rounds in Script,
/// and compares the computed output against the committed output.
pub fn flat_round_leaf(
    ctx: &CommitCtx,
    prover: Role,
    keys: &ClaimKeys,
    spec: &ClaimSpec,
    step_idx: usize,
) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let ik = keys.inner.as_ref().expect("inner keys for flat terminal");
    let n_words = spec.n_words;
    let d_words = spec.d_words();
    let d_nibbles = spec.d_nibbles();
    let bw = spec.hash.block_words();
    let n_rounds = spec.hash.n_rounds() as usize;
    let round_counter = spec.round_counter(step_idx);
    let step = &spec.steps[step_idx];
    let init = match step { Step::Compress { init, .. } => *init, _ => unreachable!() };

    let mut b = Builder::new().checksigverify(&q);
    let bn = bw * 8;
    let non_rate = d_nibbles - bn;

    // 1. The claimed output: verify re_next, keep its D, park it.
    b = load_d_of(b, &ik.re_next, n_words, d_words);
    // 2. The input: verify re_cur and park its D (alt: next, cur).
    if init == Init::D {
        b = load_d_of(b, &ik.re_cur, n_words, d_words);
    }
    // 3. The block words, last word first (the witness carries them in that
    //    order), each verified and parked, so that unparking them all lands
    //    word 0's nibble 0 deepest and word 1's nibble 7 on top.
    for j in (0..bw).rev() {
        b = park(b.wots_verify(&ik.block[j]), 8);
    }
    b = unpark(b, bn);
    // 4. The input state on top of them: unparked, or the hash's initial
    //    state (SHA-256's IV, all zeros for n4bit).
    b = match init {
        Init::Iv => match spec.hash {
            HashKind::Sha256 => nibbles(&crate::script_hash::state_bytes(&IV)).into_iter().fold(b, push_scriptnum),
            HashKind::N4Bit => (0..d_nibbles).fold(b, |b, _| push_scriptnum(b, 0)),
        },
        Init::D => unpark(b, d_nibbles),
    };
    // 5. Park the non-rate part (alt: next, non-rate). Main: block(16), rate(16).
    b = park(b, non_rate);
    // 6. Absorb: rate nibble k (on top) plus block nibble k (at depth k+1),
    //    mod 16, parked; from k = 15 down to 0, so that r_0 ends on top of
    //    the altstack.
    for k in (0..bn).rev() {
        b = b.push_int(k as i64 + 1).push_opcode(OP_ROLL).push_opcode(OP_ADD);
        b = mod16_leaf(b).push_opcode(OP_TOALTSTACK);
    }
    // 7. The S-box table, then the state above it: rate (r_0 first) then
    //    the non-rate, so nibble 39 ends on top.
    b = script::push_sbox_table(b);
    b = unpark(b, bn);
    b = unpark(b, non_rate);
    // 8. All SPN rounds.
    for r in 0..n_rounds {
        b = script::spn_round_script(b, round_counter + r);
    }
    // 9. Park the computed state, drop the table, bring it back.
    b = park(b, d_nibbles);
    for _ in 0..script::SBOX_TABLE_SIZE {
        b = b.push_opcode(OP_DROP);
    }
    b = unpark(b, d_nibbles);
    // 10. The claimed output under it... on top of it: computed (deeper), claimed (top).
    b = unpark(b, d_nibbles);

    // 12. Compare computed vs output (true iff any differs)
    b = differs_masked(b, d_nibbles, &vec![true; d_nibbles]);

    let script = b.into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("flat_{}", hex::encode(&h[..4])), script)
}

/// mod-16 correction: if top >= 16, subtract 16.
fn mod16_leaf(b: Builder) -> Builder {
    b.push_opcode(OP_DUP)
        .push_int(16)
        .push_opcode(OP_GREATERTHANOREQUAL)
        .push_opcode(OP_IF)
        .push_int(16)
        .push_opcode(OP_SUB)
        .push_opcode(OP_ENDIF)
}

/// Witness args for the flat terminal leaf (after Q's signature):
/// output state sig, then input state sig (if init=D), then the block word
/// sigs, last word first.
pub fn flat_round_witness(
    out_sig: &WotsSig,
    in_sig: Option<&WotsSig>,
    block_sigs: &[WotsSig],
) -> Vec<Vec<u8>> {
    let mut v = out_sig.consumption_order();
    if let Some(s) = in_sig {
        v.extend(s.consumption_order());
    }
    for s in block_sigs.iter().rev() {
        v.extend(s.consumption_order());
    }
    v
}

/// Witness args for `p_re_cur` after the two channel signatures: the state, then the 16 block words.
pub fn p_re_cur_witness(state_sig: &WotsSig, block_sigs: &[WotsSig]) -> Vec<Vec<u8>> {
    let mut v = state_sig.consumption_order();
    for s in block_sigs {
        v.extend(s.consumption_order());
    }
    v
}

/// Witness args for `p_sched` after the two channel signatures: the 48 words in order.
pub fn p_sched_witness(sigs: &[WotsSig]) -> Vec<Vec<u8>> {
    sigs.iter().flat_map(|s| s.consumption_order()).collect()
}

/// Nibbles of a state for a constant source.
pub fn const_nibbles(state: &[u32]) -> Vec<u8> {
    state_nibbles(state)
}

/// Index key for the inner rounds (3 bits).
pub fn inner_index_bits() -> usize {
    SEARCH.index_bits()
}

/// The inner index keys' type, re-exported for the draft phase.
pub type IndexKey = PublicKey;
