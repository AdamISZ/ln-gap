//! LN-GAP 2.5's contract graph, tic-tac-toe first (V25_POC_PLAN.md,
//! Phase 4a).
//!
//! A move is dated by members of its window: each puts the move's leaf
//! `BLAKE3-160(contract ‖ depth ‖ choice)` at the slot it assigned to the
//! (contract, depth) in its period tree, and closes its seal with the root
//! (crate `lngap-seal`). For tic-tac-toe the choice is the new state's
//! three bytes, the region the mover's state key signs.
//!
//! Per depth `d` (≥ 2 here), from the contract output:
//!
//! - `absent_d`: the claimant's absence claim after the window (a height),
//!   2-of-2 pre-signed (v1's leaf, with a height for a time);
//! - on its output `A_d`: one `rebut_{i}` per member `i` of the window,
//!   2-of-2 pre-signed, each spending a SECOND input, member `i`'s
//!   connector leaf for this (contract, depth): valid only if member `i`'s
//!   seal closing confirmed. The leaf checks the mover's pair reveal of the
//!   two heads with their authorship (v1, D63), the root's opening under
//!   member `i`'s period key, and the mover's path commitment, whose top
//!   digest must be that root; and the claimant's timeout splits;
//! - on each rebuttal output `P_{d,i}`, the claimant's disproves, all
//!   after `delta`: v1's rule family over the parked heads; `leaf_hash`
//!   (the asserted leaf digest is not BLAKE3 of the leaf preimage);
//!   `node_{l}` (the asserted parent at level `l + 1` is not BLAKE3 of the
//!   ordered child and sibling); `pair_kill` (member `i` opened two
//!   different roots for the period); `empty_kill` (member `i` closed the
//!   period empty); then the mover's checked splits after
//!   `delta + delta'`.
//!
//! The rebuttal commits; it never hashes. The level disproves run
//! BitVMX's BLAKE3 over nibbles, so no `OP_CAT` is needed. Member trees
//! have exactly `Q = 2^L` slots, so a path's length `L` and its left/right
//! orientation (the slot's bits) are fixed at open.

use std::sync::OnceLock;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{OutPoint, ScriptBuf, TxOut};
use bitcoin_script_functions::hash::blake3;
use bitcoin_script_stack::stack::StackTracker;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_btc::Hash160;
use lngap_channel::CommitCtx;
use lngap_contract::leaves::split_leaf;
use lngap_contract::Outcome;
use lngap_lamport::winternitz::{WotsExt, WotsParams, WotsPublic};
use lngap_pos::instance::PosDepthKeys;
use lngap_pos::ttt::{self, Layout};

/// Nibbles per 20-byte digest.
pub const DIGITS: usize = 40;

/// Bytes of a path commitment for `levels` levels: digests `c_0 .. c_L`
/// and siblings `s_0 .. s_{L-1}`.
pub fn path_bytes(levels: usize) -> u32 {
    (20 * (2 * levels + 1)) as u32
}

/// The Winternitz parameters of a mover's path key.
pub fn path_params(levels: usize) -> WotsParams {
    WotsParams::for_bytes(path_bytes(levels))
}

/// The path message a rebuttal signs: `c_0 .. c_L ‖ s_0 .. s_{L-1}`.
pub fn path_message(digests: &[[u8; 20]], siblings: &[[u8; 20]]) -> Vec<u8> {
    assert_eq!(digests.len(), siblings.len() + 1, "one more digest than siblings");
    digests.iter().chain(siblings).flatten().copied().collect()
}

/// The tic-tac-toe choice: the new head's state bytes (head bytes 5..8,
/// the region the state key signs).
pub fn ttt_choice(head: &[u8; 48]) -> Vec<u8> {
    head[5..8].to_vec()
}

/// One member of a depth's window, pinned at open.
#[derive(Clone, Debug)]
pub struct WindowMember {
    /// The member's index in the venue.
    pub member: usize,
    /// The member's period whose closing dates the move.
    pub period: u32,
    /// The slot the member assigned to this (contract, depth): the
    /// move's position in the period tree and its connector leaf.
    pub slot: u32,
    /// `K^root` of that period.
    pub root_key: WotsPublic,
    /// `HASH160(z)` of that period's empty closing.
    pub empty_hash: Hash160,
    /// The connector leaf `ℓ` (outpoint and output, known at open).
    pub leaf: (OutPoint, TxOut),
}

fn drop_n(mut b: Builder, n: usize) -> Builder {
    for _ in 0..n / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    if n % 2 == 1 {
        b = b.push_opcode(OP_DROP);
    }
    b
}

fn concat(parts: &[&[u8]]) -> ScriptBuf {
    ScriptBuf::from_bytes(parts.concat())
}

/// BitVMX's BLAKE3-160 over `data_bytes` bytes of nibbles (deepest) and a
/// 40-nibble digest (on top), alone on the stack: succeeds (and consumes
/// them) only if the hash DIFFERS from the digest.
pub fn blake3_mismatch_script(data_bytes: u32) -> ScriptBuf {
    static C9: OnceLock<ScriptBuf> = OnceLock::new();
    static C40: OnceLock<ScriptBuf> = OnceLock::new();
    let build = || {
        let mut st = StackTracker::new();
        let _ = st.define(data_bytes * 2, "data");
        let _ = st.define(DIGITS as u32, "digest");
        st.to_altstack();
        let h = blake3::blake3(&mut st, data_bytes, 5);
        let dg = st.from_altstack();
        st.not_equal(h, true, dg, true);
        st.get_script()
    };
    match data_bytes {
        9 => C9.get_or_init(build).clone(),
        40 => C40.get_or_init(build).clone(),
        _ => build(),
    }
}

/// The claimant's gate on every disprove: after `delta`, its key.
fn gate(ctx: &CommitCtx, l: &Layout) -> Builder {
    Builder::new().csv(ctx.params.delta).checksigverify(&ctx.key(l.mover.other()).payment)
}

/// `rebut_{name}` on `A_d` for one window member: the pair reveal and its
/// authorship (v1), then the root under the member's period key, then the
/// mover's path commitment, whose top digest `c_L` must equal the root.
///
/// Witness, wire order (bottom first): the path reveal, the root reveal,
/// the prior head's tied authorship block, the new head's, the pair
/// reveal, the hub's signature, the user's (consumed first).
#[allow(clippy::too_many_arguments)]
pub fn rebut_leaf(ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, keys_prev: &PosDepthKeys, w: &WindowMember, path_key: &WotsPublic, levels: usize, name: &str) -> Leaf {
    assert!(l.prior.is_some(), "phase 4a covers depths from 2");
    let mut b = ctx.two_of_two_verify(Builder::new()).wots_verify(&keys.rebut);
    b = ttt::authorship_fragment(b, l.file, l.new, &keys.state);
    b = ttt::authorship_fragment(b, l.file, 0, &keys_prev.state);
    b = drop_n(b, l.file);
    b = b.wots_verify(&w.root_key);
    for _ in 0..DIGITS {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.wots_verify(path_key);
    for _ in 0..DIGITS {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    // [p_0 .. p_{m-1}, r_0 .. r_39]: c_L is p_{40L .. 40L+40}
    let m = path_key.params.message_digits as usize;
    b = b.push_int(0);
    for t in 0..DIGITS {
        b = b
            .push_int((DIGITS - 1 - t + 1) as i64)
            .push_opcode(OP_PICK)
            .push_int((m - 1 - (DIGITS * levels + t) + DIGITS + 2) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SUB)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_ADD);
    }
    b = b.push_opcode(OP_NOT).push_opcode(OP_VERIFY);
    b = drop_n(b, m + DIGITS);
    Leaf::new(name.to_string(), b.push_int(1).into_script(), Timelock::NONE)
}

/// `leaf_hash` on `P_{d,i}`: the asserted leaf digest `c_0` is not
/// BLAKE3-160(contract ‖ depth ‖ the new head's state bytes).
///
/// Witness, wire order: the pair reveal, the path reveal, the claimant's
/// signature.
pub fn leaf_hash_leaf(ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, path_key: &WotsPublic, contract: u32) -> Leaf {
    let m = path_key.params.message_digits as usize;
    let mut b = gate(ctx, l).wots_verify(path_key);
    for t in (0..DIGITS).rev() {
        b = b.push_int((m - 1 - t) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
    }
    b = drop_n(b, m);
    b = b.wots_verify(&keys.rebut);
    for j in (0..6).rev() {
        let dig = l.new + 10 + j;
        b = b.push_int((l.file - 1 - dig) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
    }
    b = drop_n(b, l.file);
    let pre: Vec<u8> = [contract.to_be_bytes().to_vec(), (l.depth as u16).to_be_bytes().to_vec()].concat();
    for byte in pre {
        b = b.push_int(i64::from(byte >> 4)).push_int(i64::from(byte & 15));
    }
    for _ in 0..6 + DIGITS {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    let head = b.into_script();
    let check = blake3_mismatch_script(9);
    let one = Builder::new().push_int(1).into_script();
    Leaf::new("leaf_hash", concat(&[head.as_bytes(), check.as_bytes(), one.as_bytes()]), Timelock::csv(ctx.params.delta))
}

/// `node_{ell}` on `P_{d,i}`: at level `ell` the asserted parent
/// `c_{ell+1}` is not BLAKE3-160 of the child `c_ell` and its sibling
/// `s_ell`, ordered by bit `ell` of the slot (1: the child is the right
/// one).
///
/// Witness, wire order: the path reveal, the claimant's signature.
pub fn node_leaf(ctx: &CommitCtx, l: &Layout, path_key: &WotsPublic, levels: usize, ell: usize, slot: u32) -> Leaf {
    let m = path_key.params.message_digits as usize;
    let c = |j: usize| DIGITS * j;
    let s = |j: usize| DIGITS * (levels + 1 + j);
    let right = (slot >> ell) & 1 == 1;
    let (first, second) = if right { (s(ell), c(ell)) } else { (c(ell), s(ell)) };
    let mut b = gate(ctx, l).wots_verify(path_key);
    for block in [c(ell + 1), second, first] {
        for t in (0..DIGITS).rev() {
            b = b.push_int((m - 1 - (block + t)) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
        }
    }
    b = drop_n(b, m);
    for _ in 0..3 * DIGITS {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    let head = b.into_script();
    let check = blake3_mismatch_script(40);
    let one = Builder::new().push_int(1).into_script();
    Leaf::new(format!("node_{ell}"), concat(&[head.as_bytes(), check.as_bytes(), one.as_bytes()]), Timelock::csv(ctx.params.delta))
}

/// The post body: the pair reveal of heads `d-1 ‖ d` under the depth-`d`
/// rebuttal key and both heads' authorship (v1, D63), the register file
/// then dropped. The same body serves a ladder step, a self-post and (with
/// the dating checks after it) a rebuttal.
fn post_body(b: Builder, l: &Layout, keys: &PosDepthKeys, keys_prev: &PosDepthKeys) -> Builder {
    let mut b = b.wots_verify(&keys.rebut);
    b = ttt::authorship_fragment(b, l.file, l.new, &keys.state);
    b = ttt::authorship_fragment(b, l.file, 0, &keys_prev.state);
    drop_n(b, l.file)
}

/// `post` on a ladder output: the mover of depth `l.depth` posts its move
/// on chain, 2-of-2 pre-signed so that its output is the next ladder
/// output. Witness, wire order: the prior head's tied authorship block,
/// the new head's, the pair reveal, the hub's signature, the user's.
pub fn post_leaf(ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, keys_prev: &PosDepthKeys, name: &str) -> Leaf {
    let b = post_body(ctx.two_of_two_verify(Builder::new()), l, keys, keys_prev);
    Leaf::new(name.to_string(), b.push_int(1).into_script(), Timelock::NONE)
}

/// `self_post_{d}` on the contract output: a censored mover posts its move
/// on chain itself, into the ladder at depth `d`. It races the claimant's
/// `absent_d`, which is valid only after the window. Like every leaf of
/// the contract output the broadcaster can spend, it waits for
/// `to_self_delay` when the mover is the broadcaster.
pub fn self_post_leaf(ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, keys_prev: &PosDepthKeys) -> Leaf {
    let mut b = Builder::new();
    let mut tl = Timelock::NONE;
    if l.mover == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    let b = post_body(ctx.two_of_two_verify(b), l, keys, keys_prev);
    Leaf::new(format!("self_post_{}", l.depth), b.push_int(1).into_script(), tl)
}

/// `pair_continue` on `P_{d,i}`: member `i` opened two different roots for
/// the period, so the dating cannot be trusted either way, and the game
/// continues on chain from depth `d` (a member's fault moves no money).
/// 2-of-2 pre-signed into the ladder output at depth `d`. Witness, wire
/// order: one opening, the other, the hub's signature, the user's.
pub fn pair_continue_leaf(ctx: &CommitCtx, root_key: &WotsPublic) -> Leaf {
    let m = root_key.params.message_digits as usize;
    let mut b = ctx.two_of_two_verify(Builder::new()).wots_verify(root_key);
    for _ in 0..m {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.wots_verify(root_key);
    for _ in 0..m {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    b = b.push_int(0);
    for j in 0..m {
        b = b
            .push_int((m - j) as i64)
            .push_opcode(OP_PICK)
            .push_int((2 * m - j + 1) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SUB)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_ADD);
    }
    b = b.push_opcode(OP_VERIFY);
    b = drop_n(b, 2 * m);
    Leaf::new("pair_continue", b.push_int(1).into_script(), Timelock::NONE)
}

/// `empty_continue` on `P_{d,i}`: member `i` closed the period empty, so a
/// root under its key was made afterwards; continue on chain as for a
/// pair. Witness, wire order: the preimage `z`, the hub's signature, the
/// user's.
pub fn empty_continue_leaf(ctx: &CommitCtx, empty_hash: &Hash160) -> Leaf {
    let b = ctx.two_of_two_verify(Builder::new()).push_opcode(OP_HASH160).push_bytes(empty_hash).push_opcode(OP_EQUAL);
    Leaf::new("empty_continue", b.into_script(), Timelock::NONE)
}

/// `waive` on `A_d`: the claimant has signed its own move at `d + 1`, so it
/// accepted move `d`; the claim is defeated and pays the mover, 2-of-2
/// pre-signed. `claimant_next` is the claimant's state key for `d + 1`.
/// Witness, wire order: that signature, the hub's signature, the user's.
pub fn waive_leaf(ctx: &CommitCtx, claimant_next: &WotsPublic) -> Leaf {
    let b = ctx.two_of_two_verify(Builder::new()).wots_verify(claimant_next);
    let b = drop_n(b, claimant_next.params.message_digits as usize);
    Leaf::new("waive", b.push_int(1).into_script(), Timelock::NONE)
}

/// The tree of the claim output `A_d`: one rebuttal per window member, the
/// waiver (when there is a depth `d + 1`), and the claimant's timeout
/// splits.
#[allow(clippy::too_many_arguments)]
pub fn claim_tree(
    ctx: &CommitCtx,
    l: &Layout,
    keys: &PosDepthKeys,
    keys_prev: &PosDepthKeys,
    keys_next: Option<&PosDepthKeys>,
    window: &[WindowMember],
    path_key: &WotsPublic,
    levels: usize,
    outcomes: &[Outcome],
) -> anyhow::Result<TapTree> {
    let mut leaves: Vec<Leaf> = window
        .iter()
        .map(|w| rebut_leaf(ctx, l, keys, keys_prev, w, path_key, levels, &format!("rebut_{}", w.member)))
        .collect();
    if let Some(next) = keys_next {
        leaves.push(waive_leaf(ctx, &next.state));
    }
    for o in outcomes {
        leaves.push(split_leaf(ctx, o, ctx.params.delta, &keys.claimant_code));
    }
    TapTree::new(leaves)
}

/// The tree of the rebuttal output `P_{d,i}` through window member `w`.
#[allow(clippy::too_many_arguments)]
pub fn rebuttal_tree(
    ctx: &CommitCtx,
    l: &Layout,
    keys: &PosDepthKeys,
    w: &WindowMember,
    path_key: &WotsPublic,
    levels: usize,
    contract: u32,
    outcomes: &[Outcome],
) -> anyhow::Result<TapTree> {
    let mut leaves = disprove_family(ctx, l, keys);
    leaves.push(leaf_hash_leaf(ctx, l, keys, path_key, contract));
    for ell in 0..levels {
        leaves.push(node_leaf(ctx, l, path_key, levels, ell, w.slot));
    }
    leaves.push(pair_continue_leaf(ctx, &w.root_key));
    leaves.push(empty_continue_leaf(ctx, &w.empty_hash));
    leaves.extend(checked_splits(ctx, l, keys, outcomes));
    TapTree::new(leaves)
}

fn disprove_family(ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys) -> Vec<Leaf> {
    ttt::disprove_leaves(l, &keys.rebut)
        .into_iter()
        .map(|pl| {
            let head = gate(ctx, l).into_script();
            Leaf::new(format!("disprove_{}", pl.name), concat(&[head.as_bytes(), pl.script.as_bytes()]), Timelock::csv(ctx.params.delta))
        })
        .collect()
}

fn checked_splits(ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, outcomes: &[Outcome]) -> Vec<Leaf> {
    let window = ctx.params.delta + ctx.params.delta_prime;
    outcomes.iter().map(|o| ttt::checked_split_leaf(ctx, l, o, window, &keys.mover_code, &keys.rebut)).collect()
}

/// The tree of a LADDER output at depth `j`: move `j` is on chain (posted,
/// or parked by a rebuttal). The rule family judges it (after `delta`);
/// the next mover posts move `j + 1` (no delay); failing that, the mover
/// of `j` is paid R(state `j`) by its checked split (after
/// `delta + delta'`), which for an open state with the opponent to move is
/// the opponent's forfeit. `keys[i]` is depth `i + 1`'s key set.
pub fn ladder_tree(ctx: &CommitCtx, game_id: u16, j: u32, keys: &[PosDepthKeys], outcomes: &[Outcome]) -> anyhow::Result<TapTree> {
    let l = Layout::at(j, game_id, keys[(j - 1) as usize].mover);
    let mut leaves = disprove_family(ctx, &l, &keys[(j - 1) as usize]);
    if (j as usize) < keys.len() {
        let next = Layout::at(j + 1, game_id, keys[j as usize].mover);
        leaves.push(post_leaf(ctx, &next, &keys[j as usize], &keys[(j - 1) as usize], "post"));
    }
    leaves.extend(checked_splits(ctx, &l, &keys[(j - 1) as usize], outcomes));
    TapTree::new(leaves)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_message_layout() {
        let d = [[1u8; 20], [2; 20], [3; 20]];
        let s = [[9u8; 20], [8; 20]];
        let m = path_message(&d, &s);
        assert_eq!(m.len() as u32, path_bytes(2));
        assert_eq!(&m[40..60], &[3u8; 20], "c_L at bytes 20L..");
        assert_eq!(&m[60..80], &[9u8; 20], "s_0 after the digests");
    }
}
