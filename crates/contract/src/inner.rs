//! The inner level of the two-level search.
//!
//! Level 1 (`claim.rs`) isolates one compression step: input midstate `cur`
//! (a constant or a prover commitment), a constant 64-byte block, and the
//! prover's claimed output `next`. Instead of recomputing the whole
//! compression in one 383 kWU leaf, the search continues inside it:
//!
//! ```text
//! R_R'  ─ p_sched   (P commits the 48 schedule words W[16..64], 32-bit WOTS) → S_1 | timeout: Q after Δ
//! S_1   ─ p_inner_1 (P commits the round states s_8, s_16, …, s_56)          → I_1 | timeout: Q
//! I_1   ─ q_inner_1 (Q commits a 3-bit segment index)                        → S_2 | timeout: P
//!       ─ sched_i   (Q disproves schedule word i by its recurrence; no timelock)
//! S_2   ─ p_inner_2 (P commits the 7 states inside the chosen 8-round segment) → I_2 | timeout: Q
//! I_2   ─ q_inner_2 (Q commits a 3-bit round index)                          → T   | timeout: P
//! T     ─ round_r   (Q disproves one SHA-256 round; round 63 includes the feed-forward)
//!       | timeout: P after Δ (the claim stood)
//! ```
//!
//! Inner states: `s_0 = cur`, `s_{r+1} = round(s_r, W[r])` for `r < 63`,
//! `s_64 = cur + round(s_63, W[63]) = next`. So every commitment is a plain
//! 8-word state and the level-1 sources supply `s_0` and `s_64`.

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
use lngap_script32::sha::{add_states, differs_and_finish, round_body, round_native, schedule_body, schedule_native, K, TABLES};
use lngap_script32::Stack;
use serde::{Deserialize, Serialize};

use crate::claim::{all_paths, source_key, step_sources, ClaimKeys, ClaimSpec, Search, StateSource};
use crate::instance::key_label;
use crate::script_hash::{nibbles, push_scriptnum, state_bytes};

pub const ROUNDS: u32 = 64;
pub const INNER_K: u32 = 8;
/// The inner search: 64 rounds, branching 8, two index rounds.
pub const SEARCH: Search = Search { n: ROUNDS, k: INNER_K };

/// The prover's inner-level keys for one depth.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InnerKeys {
    /// `sched[i - 16]`: schedule word `W[i]`, `i` in 16..64 (32-bit WOTS).
    pub sched: Vec<WotsPublic>,
    /// `states[r - 1][t]`: inner round `r`, commitment `t` (256-bit WOTS).
    pub states: Vec<Vec<WotsPublic>>,
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

/// Inner states `s_0 … s_64` from `cur` and a schedule; `cheat(r, s_r)`
/// may alter a state, and the alteration propagates (a lying prover's
/// "computation").
pub fn round_states(cur: &[u32; 8], w: &[u32; 64], cheat: Option<&dyn Fn(u32, &[u32; 8]) -> [u32; 8]>) -> Vec<[u32; 8]> {
    let mut v = vec![*cur];
    for r in 0..64usize {
        let mut s = round_native(&v[r], w[r], K[r]);
        if r == 63 {
            for i in 0..8 {
                s[i] = s[i].wrapping_add(cur[i]);
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
    /// `s_0` or `s_64`: the level-1 source of `cur` / `next`.
    Outer(StateSource),
    /// The prover's commitment `t` (0-based) in inner round `r` (1-based).
    Inner(u32, u32),
}

/// Sources of the isolated round's input and claimed output, and the round index.
pub fn round_sources(cur: &StateSource, next: &StateSource, inner_path: &[u32]) -> (InnerSource, InnerSource, u32) {
    assert_eq!(inner_path.len() as u32, SEARCH.rounds());
    let mut lo_src = InnerSource::Outer(cur.clone());
    let mut hi_src = InnerSource::Outer(next.clone());
    for (r, &j) in inner_path.iter().enumerate() {
        let r1 = r as u32 + 1;
        let new_lo = if j == 0 { lo_src.clone() } else { InnerSource::Inner(r1, j - 1) };
        let new_hi = if j == INNER_K - 1 { hi_src.clone() } else { InnerSource::Inner(r1, j) };
        lo_src = new_lo;
        hi_src = new_hi;
    }
    let (lo, len) = SEARCH.segment(inner_path);
    assert_eq!(len, 1);
    (lo_src, hi_src, lo)
}

pub fn inner_source_key<'a>(src: &InnerSource, keys: &'a ClaimKeys) -> Option<&'a WotsPublic> {
    match src {
        InnerSource::Outer(StateSource::Const(_)) => None,
        InnerSource::Outer(s) => Some(source_key(s, keys)),
        InnerSource::Inner(r, t) => Some(&keys.inner.as_ref().expect("inner keys").states[*r as usize - 1][*t as usize]),
    }
}

// ----- leaf bodies -----

/// Verify a WOTS signature and discard the digits.
fn wots_verify_drop(mut b: Builder, pk: &WotsPublic) -> Builder {
    b = b.wots_verify(pk);
    for _ in 0..pk.params.message_digits / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    b
}

fn timeout_leaf(ctx: &CommitCtx, sweeper: Role) -> Leaf {
    Leaf::new("timeout", Builder::new().csv(ctx.params.delta).checksig(&ctx.key(sweeper).payment).into_script(), Timelock::csv(ctx.params.delta))
}

/// Push a state (constant nibbles) or verify its commitment, then park the
/// 64 nibbles on the altstack (the next verifier needs the witness on top).
fn load_state(b: Builder, src: &InnerSource, keys: &ClaimKeys) -> Builder {
    let b = match src {
        InnerSource::Outer(StateSource::Const(st)) => nibbles(&state_bytes(st)).into_iter().fold(b, push_scriptnum),
        _ => b.wots_verify(inner_source_key(src, keys).unwrap()),
    };
    park(b, 64)
}

/// Push schedule word `i` (a block constant for `i < 16`, else verify its
/// commitment) and park its 8 nibbles.
fn load_word(b: Builder, i: u32, block: &[u8; 64], keys: &ClaimKeys) -> Builder {
    let b = if i < 16 {
        let i = i as usize;
        nibbles(&block[4 * i..4 * i + 4]).into_iter().fold(b, push_scriptnum)
    } else {
        b.wots_verify(&keys.inner.as_ref().expect("inner keys").sched[i as usize - 16])
    };
    park(b, 8)
}

fn park(mut b: Builder, n: usize) -> Builder {
    for _ in 0..n {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b
}

/// Push the tables, then restore `n` parked nibbles above them. Runs come
/// back in reverse parking order: the last parked is deepest.
fn restore(b: Builder, n: usize) -> Stack {
    let mut s = Stack::new(b, TABLES);
    s.map(n as isize, |mut b| {
        for _ in 0..n {
            b = b.push_opcode(OP_FROMALTSTACK);
        }
        b
    });
    s
}

/// The `round_r` disprove leaf for one isolated compression `(cur, block) → next`
/// and round `r`: true iff the prover's claimed `s_{r+1}` differs from
/// `round(s_r, W[r])` (plus `cur` for `r = 63`).
///
/// Each commitment is verified with the witness on top of the stack and its
/// digits parked; the tables are pushed last and the runs restored above
/// them. Witness (consumption order, after Q's signature): `W[r]` signature
/// (if `r ≥ 16`), `s_r` signature (if committed), `cur` signature (if
/// `r = 63` and committed), `s_{r+1}` signature.
pub fn round_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, cur: &StateSource, next: &StateSource, block: &[u8; 64], r: u32) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let inner_path = [r / INNER_K, r % INNER_K];
    let (in_src, out_src, rr) = round_sources(cur, next, &inner_path);
    assert_eq!(rr, r);
    let mut b = Builder::new().checksigverify(&q);
    // parked last comes back deepest: final layout is out, [cur], in, W (top)
    b = load_word(b, r, block, keys);
    b = load_state(b, &in_src, keys);
    let mut n = 72;
    if r == 63 {
        b = load_state(b, &InnerSource::Outer(cur.clone()), keys);
        n += 64;
    }
    b = load_state(b, &out_src, keys);
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

/// Witness args for [`round_leaf`] (after Q's signature).
pub fn round_witness(w_sig: Option<&WotsSig>, in_sig: Option<&WotsSig>, cur_sig: Option<&WotsSig>, out_sig: &WotsSig) -> Vec<Vec<u8>> {
    let mut v = Vec::new();
    for sig in [w_sig, in_sig, cur_sig].into_iter().flatten() {
        v.extend(sig.consumption_order());
    }
    v.extend(out_sig.consumption_order());
    v
}

/// The `sched_i` disprove leaf (`i` in 16..64): true iff the prover's `W[i]`
/// differs from the recurrence over `W[i-16], W[i-15], W[i-7], W[i-2]`
/// (block constants or the prover's own commitments).
///
/// Witness (consumption order, after Q's signature): signatures for the
/// committed inputs in [`sched_inputs`] order, then `W[i]`'s signature.
pub fn sched_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, block: &[u8; 64], i: u32) -> (String, ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let mut b = Builder::new().checksigverify(&q);
    // the schedule body wants w2, w7, w15, w16 with w16 on top: park in the reverse order
    for j in sched_inputs(i) {
        b = load_word(b, j, block, keys);
    }
    b = load_word(b, i, block, keys);
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

/// Witness args for [`sched_leaf`] (after Q's signature).
pub fn sched_witness(input_sigs: &[&WotsSig], w_sig: &WotsSig) -> Vec<Vec<u8>> {
    let mut v = Vec::new();
    for sig in input_sigs {
        v.extend(sig.consumption_order());
    }
    v.extend(w_sig.consumption_order());
    v
}

// ----- trees along the inner chain -----

/// `R_R'`: waiting for the prover's schedule.
pub fn wait_sched_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys) -> Result<TapTree> {
    let ik = keys.inner.as_ref().expect("inner keys");
    let mut b = ctx.two_of_two_verify(Builder::new());
    for pk in &ik.sched {
        b = wots_verify_drop(b, pk);
    }
    let leaf = Leaf::new("p_sched", b.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE);
    TapTree::new(vec![leaf, timeout_leaf(ctx, prover.other())])
}

/// `S_r`: waiting for the prover's inner round `r` states.
pub fn wait_inner_p_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, r: u32) -> Result<TapTree> {
    let ik = keys.inner.as_ref().expect("inner keys");
    let mut b = ctx.two_of_two_verify(Builder::new());
    for pk in &ik.states[r as usize - 1] {
        b = wots_verify_drop(b, pk);
    }
    let leaf = Leaf::new(format!("p_inner_{r}"), b.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE);
    TapTree::new(vec![leaf, timeout_leaf(ctx, prover.other())])
}

/// `I_r`: waiting for the challenger's inner index `r`; in round 1 the
/// challenger may instead disprove a schedule word.
pub fn wait_inner_q_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, inner_indices: &[PublicKey], spec: &ClaimSpec, r: u32) -> Result<TapTree> {
    let pk = &inner_indices[r as usize - 1];
    let mut b = ctx.two_of_two_verify(Builder::new());
    for i in (0..pk.n_bits()).rev() {
        b = b.bit_decode(&pk.bits[i]).push_opcode(OP_DROP);
    }
    let mut leaves = vec![Leaf::new(format!("q_inner_{r}"), b.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE)];
    if r == 1 {
        let mut blocks: Vec<&[u8; 64]> = Vec::new();
        for block in &spec.blocks {
            if !blocks.contains(&block) {
                blocks.push(block);
            }
        }
        for block in blocks {
            for i in 16..ROUNDS {
                let (name, script) = sched_leaf(ctx, prover, keys, block, i);
                if !leaves.iter().any(|l| l.name == name) {
                    leaves.push(Leaf::new(name, script, Timelock::NONE));
                }
            }
        }
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// `T`: the challenger disproves one round, or the prover times out.
pub fn round_terminal_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec) -> Result<TapTree> {
    let mut leaves: Vec<Leaf> = Vec::new();
    // dedupe before building: a leaf depends on (r, block) plus the level-1
    // sources only at r = 0 (cur) and r = 63 (cur, next)
    let mut built: Vec<(u32, [u8; 64], Option<StateSource>, Option<StateSource>)> = Vec::new();
    for path in all_paths(spec) {
        let (cur, next, step) = step_sources(spec, &path);
        let block = spec.blocks[step as usize];
        for r in 0..ROUNDS {
            let key = (r, block, (r == 0 || r == 63).then(|| cur.clone()), (r == 63).then(|| next.clone()));
            if built.contains(&key) {
                continue;
            }
            built.push(key);
            let (name, script) = round_leaf(ctx, prover, keys, &cur, &next, &block, r);
            if !leaves.iter().any(|l| l.name == name) {
                leaves.push(Leaf::new(name, script, Timelock::NONE));
            }
        }
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// Witness args for `p_sched` after the two channel signatures: the 48 words in order.
pub fn p_sched_witness(sigs: &[WotsSig]) -> Vec<Vec<u8>> {
    sigs.iter().flat_map(|s| s.consumption_order()).collect()
}
