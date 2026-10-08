//! LN-GAP 2.5's contract graph: tic-tac-toe, then the search over a verifier
//! (V25_POC_PLAN.md, Phases 4 and 5).
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
//!   member `i`'s period key; the claimant's timeout splits. The rebuttal
//!   also spends one CARRIER per path level (outputs of the claim
//!   transaction), each revealing the mover's level key over
//!   `c_l ‖ s_l`: a whole path does not fit one input's stack;
//! - on each rebuttal output `P_{d,i}`, the claimant's disproves, all
//!   after `delta`: v1's rule family over the parked heads; `leaf_hash`
//!   (the asserted leaf digest is not BLAKE3 of the leaf preimage);
//!   `node_{l}` (the parent, level `l + 1`'s digest or at the top the
//!   member's root, is not BLAKE3 of the ordered child and sibling); and
//!   the continuations into the on-chain ladder, `pair_continue` (member
//!   `i` opened two different roots for the period) and `empty_continue`
//!   (member `i` closed the period empty); then the mover's splits after
//!   `delta + delta'`.
//!
//! The rebuttal commits; it never hashes. The level disproves run
//! BitVMX's BLAKE3 over nibbles, so no `OP_CAT` is needed. Member trees
//! have exactly `Q = 2^L` slots, so a path's length `L` and its left/right
//! orientation (the slot's bits) are fixed at open.

use std::collections::HashMap;
use std::sync::Mutex;

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
use lngap_pos::ttt::{self, Layout, PosLeaf};

/// Nibbles per 20-byte digest.
pub const DIGITS: usize = 40;

/// Bytes a path level commits: the child digest `c_l` and its sibling
/// `s_l`.
pub const LEVEL_BYTES: u32 = 40;

/// The Winternitz parameters of a mover's level key.
pub fn level_params() -> WotsParams {
    WotsParams::for_bytes(LEVEL_BYTES)
}

/// The message a level key signs: `c_l ‖ s_l`.
pub fn level_message(c: &[u8; 20], s: &[u8; 20]) -> Vec<u8> {
    [c.as_slice(), s.as_slice()].concat()
}

/// The value of a carrier output.
pub const CARRIER_SAT: u64 = 330;

/// A CARRIER: one per path level, created by the claim transaction and
/// spent by the rebuttal beside `A_d`. A rebuttal's witness cannot hold a
/// whole path (Bitcoin's 1,000-item stack limit is per input), so each
/// level is revealed by its own input: the mover's signature (so nobody
/// else can spend it once the reveal is public) and its level key's
/// reveal of `c_l ‖ s_l`. Witness, wire order: the reveal, the mover's
/// signature.
pub fn carrier_tree(ctx: &CommitCtx, mover: lngap_channel::Role, key: &WotsPublic) -> anyhow::Result<TapTree> {
    let b = Builder::new().checksigverify(&ctx.key(mover).payment).wots_verify(key);
    let b = drop_n(b, key.params.message_digits as usize);
    TapTree::new(vec![Leaf::new("carry", b.push_int(1).into_script(), Timelock::NONE)])
}

/// The tic-tac-toe choice: the new head's state bytes (head bytes 5..8,
/// the region the state key signs).
pub fn ttt_choice(head: &[u8; 48]) -> Vec<u8> {
    head[5..8].to_vec()
}

/// What the graph needs from a game family to date its moves: the moves'
/// authorship, where the dated choice sits in a head, the claimant's rule
/// family, and the mover's splits on a rebuttal or ladder output.
pub trait Dated: Sync {
    /// The authorship fragment (v1, D41) of the head at file offset `off`.
    fn authorship(&self, b: Builder, file: usize, off: usize, key: &WotsPublic) -> Builder;
    /// The choice: head bytes `from .. from + bytes`.
    fn choice_region(&self) -> (usize, usize);
    /// The claimant's disproves over the parked pair (scripts after the
    /// claimant's gate).
    fn disproves(&self, l: &Layout, rebut: &WotsPublic) -> Vec<PosLeaf>;
    /// The mover's splits on an output that parks move `l.depth` (and, for
    /// a family with a final proof, the proofs and the claimant's split).
    fn mover_splits(&self, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, outcomes: &[Outcome]) -> Vec<Leaf>;
    /// The choice of a head.
    fn choice(&self, head: &[u8; 48]) -> Vec<u8> {
        let (from, n) = self.choice_region();
        head[from..from + n].to_vec()
    }
}

/// Tic-tac-toe: the choice is the new state's three bytes; the splits are
/// v1's checked splits (R of the parked state).
pub struct TttDated;

impl Dated for TttDated {
    fn authorship(&self, b: Builder, file: usize, off: usize, key: &WotsPublic) -> Builder {
        ttt::authorship_fragment(b, file, off, key)
    }
    fn choice_region(&self) -> (usize, usize) {
        (5, 3)
    }
    fn disproves(&self, l: &Layout, rebut: &WotsPublic) -> Vec<PosLeaf> {
        ttt::disprove_leaves(l, rebut)
    }
    fn mover_splits(&self, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, outcomes: &[Outcome]) -> Vec<Leaf> {
        let window = ctx.params.delta + ctx.params.delta_prime;
        outcomes.iter().map(|o| ttt::checked_split_leaf(ctx, l, o, window, &keys.mover_code, &keys.rebut)).collect()
    }
}

/// The search's choice bytes: head bytes 4..48, what its state key signs.
pub const ZK_CHOICE_BYTES: u32 = 44;

/// The search over a verifier (`lngap-zk`, D59-D62), through v1's outside
/// family: the choice is the 44 bytes the state key signs (the state
/// digest and the midpoint or record digest); the mover wins a parked
/// depth after `delta + delta'` unless disproved, except at the final
/// depth, where it must prove the step (D59) and the claimant's split
/// waits a further `delta'`.
pub struct ZkDated<'a>(pub &'a dyn lngap_pos::ext::Family);

impl ZkDated<'_> {
    /// The search's choice of a head (no family needed).
    pub fn choice_of(head: &[u8; 48]) -> Vec<u8> {
        head[4..4 + ZK_CHOICE_BYTES as usize].to_vec()
    }
}

impl Dated for ZkDated<'_> {
    fn authorship(&self, b: Builder, file: usize, off: usize, key: &WotsPublic) -> Builder {
        lngap_pos::blackjack::authorship_fragment(b, file, off, key)
    }
    fn choice_region(&self) -> (usize, usize) {
        (4, ZK_CHOICE_BYTES as usize)
    }
    fn disproves(&self, l: &Layout, rebut: &WotsPublic) -> Vec<PosLeaf> {
        self.0.disprove_leaves(l, rebut)
    }
    fn mover_splits(&self, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, outcomes: &[Outcome]) -> Vec<Leaf> {
        let w = ctx.params.delta + ctx.params.delta_prime;
        let last = self.0.final_depth() == Some(l.depth);
        let mut leaves = Vec::new();
        if last {
            let gate = Builder::new().csv(w).checksigverify(&ctx.key(l.mover).payment).into_script();
            for (name, script) in self.0.prove_leaves(l, &keys.rebut) {
                leaves.push(Leaf::new(name, concat(&[gate.as_bytes(), script.as_bytes()]), Timelock::csv(w)));
            }
        }
        let code = |r: lngap_channel::Role| if r == lngap_channel::Role::User { 0 } else { 1 };
        let (payee, lock) = if last { (l.mover.other(), w + ctx.params.delta_prime) } else { (l.mover, w) };
        for o in outcomes {
            let name = format!("split_{}", o.name);
            if o.code == code(payee) {
                let b = ctx.two_of_two_verify(Builder::new().csv(lock));
                leaves.push(Leaf::new(name, b.push_int(1).into_script(), Timelock::csv(lock)));
            } else {
                leaves.push(Leaf::new(name, Builder::new().push_int(i64::from(o.code)).push_opcode(OP_RETURN).into_script(), Timelock::NONE));
            }
        }
        leaves
    }
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
    static CACHE: Mutex<Option<HashMap<u32, ScriptBuf>>> = Mutex::new(None);
    if let Some(s) = CACHE.lock().unwrap().get_or_insert_with(HashMap::new).get(&data_bytes) {
        return s.clone();
    }
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
    let s = build();
    CACHE.lock().unwrap().get_or_insert_with(HashMap::new).insert(data_bytes, s.clone());
    s
}

/// The claimant's gate on every disprove: after `delta`, its key.
fn gate(ctx: &CommitCtx, l: &Layout) -> Builder {
    Builder::new().csv(ctx.params.delta).checksigverify(&ctx.key(l.mover.other()).payment)
}

/// `rebut_{name}` on `A_d` for one window member: the pair reveal and its
/// authorship (v1), then the root under the member's period key. The path
/// rides in the carriers, the transaction's other inputs (fixed by the
/// pre-signed 2-of-2), its top level checked against this root by
/// `node_{L-1}`.
///
/// Witness, wire order (bottom first): the root reveal, the prior head's
/// tied authorship block, the new head's, the pair reveal, the hub's
/// signature, the user's (consumed first).
pub fn rebut_leaf(g: &dyn Dated, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, keys_prev: Option<&PosDepthKeys>, w: &WindowMember, name: &str) -> Leaf {
    let b = post_body(g, ctx.two_of_two_verify(Builder::new()), l, keys, keys_prev);
    let b = drop_n(b.wots_verify(&w.root_key), DIGITS);
    Leaf::new(name.to_string(), b.push_int(1).into_script(), Timelock::NONE)
}

/// Verify a reveal under `key` (`m` message digits), keep its 40-digit
/// block at digit offset `at` on the altstack (digit 0 deepest when
/// restored), drop the rest.
fn keep_block(b: Builder, key: &WotsPublic, at: usize) -> Builder {
    let m = key.params.message_digits as usize;
    let mut b = b.wots_verify(key);
    for t in (0..DIGITS).rev() {
        b = b.push_int((m - 1 - (at + t)) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
    }
    drop_n(b, m)
}

/// `leaf_hash` on `P_{d,i}`: the leaf digest `c_0` the mover's level-0
/// key signed is not BLAKE3-160(contract ‖ depth ‖ the new head's choice).
///
/// Witness, wire order: the pair reveal, the level-0 reveal, the
/// claimant's signature.
pub fn leaf_hash_leaf(g: &dyn Dated, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, level0: &WotsPublic, contract: u32) -> Leaf {
    let mut b = keep_block(gate(ctx, l), level0, 0);
    b = b.wots_verify(&keys.rebut);
    let (from, n) = g.choice_region();
    for j in (0..2 * n).rev() {
        let dig = l.new + 2 * from + j;
        b = b.push_int((l.file - 1 - dig) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
    }
    b = drop_n(b, l.file);
    let pre: Vec<u8> = [contract.to_be_bytes().to_vec(), (l.depth as u16).to_be_bytes().to_vec()].concat();
    for byte in pre {
        b = b.push_int(i64::from(byte >> 4)).push_int(i64::from(byte & 15));
    }
    for _ in 0..2 * n + DIGITS {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    let head = b.into_script();
    let check = blake3_mismatch_script(6 + n as u32);
    let one = Builder::new().push_int(1).into_script();
    Leaf::new("leaf_hash", concat(&[head.as_bytes(), check.as_bytes(), one.as_bytes()]), Timelock::csv(ctx.params.delta))
}

/// `node_{ell}` on `P_{d,i}`: the parent (level `ell + 1`'s `c`, or at the
/// top the member's root) is not BLAKE3-160 of `c_ell` and `s_ell`,
/// ordered by bit `ell` of the slot (1: the child is the right one).
/// `upper` is level `ell + 1`'s key, or the member's root key at the top.
///
/// Witness, wire order: level `ell`'s reveal, the upper reveal, the
/// claimant's signature.
pub fn node_leaf(ctx: &CommitCtx, l: &Layout, lower: &WotsPublic, upper: &WotsPublic, ell: usize, slot: u32) -> Leaf {
    let right = (slot >> ell) & 1 == 1;
    let (first, second) = if right { (DIGITS, 0) } else { (0, DIGITS) };
    let mut b = keep_block(gate(ctx, l), upper, 0);
    let m = lower.params.message_digits as usize;
    b = b.wots_verify(lower);
    for block in [second, first] {
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
/// then dropped. At depth 1 there is no prior: the reveal is of the head
/// alone (`keys_prev` is `None`). The same body serves a ladder step, a self-post and (with
/// the dating checks after it) a rebuttal.
fn post_body(g: &dyn Dated, b: Builder, l: &Layout, keys: &PosDepthKeys, keys_prev: Option<&PosDepthKeys>) -> Builder {
    let mut b = b.wots_verify(&keys.rebut);
    b = g.authorship(b, l.file, l.new, &keys.state);
    if l.prior.is_some() {
        b = g.authorship(b, l.file, 0, &keys_prev.expect("a pair has a prior").state);
    }
    drop_n(b, l.file)
}

/// `post` on a ladder output: the mover of depth `l.depth` posts its move
/// on chain, 2-of-2 pre-signed so that its output is the next ladder
/// output. Witness, wire order: the prior head's tied authorship block,
/// the new head's, the pair reveal, the hub's signature, the user's.
pub fn post_leaf(g: &dyn Dated, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, keys_prev: Option<&PosDepthKeys>, name: &str) -> Leaf {
    let b = post_body(g, ctx.two_of_two_verify(Builder::new()), l, keys, keys_prev);
    Leaf::new(name.to_string(), b.push_int(1).into_script(), Timelock::NONE)
}

/// `self_post_{d}` on the contract output: a censored mover posts its move
/// on chain itself, into the ladder at depth `d`. It races the claimant's
/// `absent_d`, which is valid only after the window. Like every leaf of
/// the contract output the broadcaster can spend, it waits for
/// `to_self_delay` when the mover is the broadcaster.
pub fn self_post_leaf(g: &dyn Dated, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys, keys_prev: Option<&PosDepthKeys>) -> Leaf {
    let mut b = Builder::new();
    let mut tl = Timelock::NONE;
    if l.mover == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    let b = post_body(g, ctx.two_of_two_verify(b), l, keys, keys_prev);
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
    g: &dyn Dated,
    ctx: &CommitCtx,
    l: &Layout,
    keys: &PosDepthKeys,
    keys_prev: Option<&PosDepthKeys>,
    keys_next: Option<&PosDepthKeys>,
    window: &[WindowMember],
    outcomes: &[Outcome],
) -> anyhow::Result<TapTree> {
    let mut leaves: Vec<Leaf> = window
        .iter()
        .map(|w| rebut_leaf(g, ctx, l, keys, keys_prev, w, &format!("rebut_{}", w.member)))
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
    g: &dyn Dated,
    ctx: &CommitCtx,
    l: &Layout,
    keys: &PosDepthKeys,
    w: &WindowMember,
    level_keys: &[WotsPublic],
    contract: u32,
    outcomes: &[Outcome],
) -> anyhow::Result<TapTree> {
    let mut leaves = disprove_family(g, ctx, l, keys);
    leaves.push(leaf_hash_leaf(g, ctx, l, keys, &level_keys[0], contract));
    for ell in 0..level_keys.len() {
        let upper = level_keys.get(ell + 1).unwrap_or(&w.root_key);
        leaves.push(node_leaf(ctx, l, &level_keys[ell], upper, ell, w.slot));
    }
    leaves.push(pair_continue_leaf(ctx, &w.root_key));
    leaves.push(empty_continue_leaf(ctx, &w.empty_hash));
    leaves.extend(g.mover_splits(ctx, l, keys, outcomes));
    TapTree::new(leaves)
}

fn disprove_family(g: &dyn Dated, ctx: &CommitCtx, l: &Layout, keys: &PosDepthKeys) -> Vec<Leaf> {
    g.disproves(l, &keys.rebut)
        .into_iter()
        .map(|pl| {
            let head = gate(ctx, l).into_script();
            Leaf::new(format!("disprove_{}", pl.name), concat(&[head.as_bytes(), pl.script.as_bytes()]), Timelock::csv(ctx.params.delta))
        })
        .collect()
}

/// The tree of a LADDER output at depth `j`: move `j` is on chain (posted,
/// or parked by a rebuttal). The rule family judges it (after `delta`);
/// the next mover posts move `j + 1` (no delay); failing that, the mover
/// of `j` is paid by its splits (after `delta + delta'`): for tic-tac-toe
/// R(state `j`), which for an open state with the opponent to move is the
/// opponent's forfeit; for the search, the mover of `j` (or, at the final
/// depth, its proof). `keys[i]` is depth `i + 1`'s key set.
pub fn ladder_tree(g: &dyn Dated, ctx: &CommitCtx, game_id: u16, j: u32, keys: &[PosDepthKeys], outcomes: &[Outcome]) -> anyhow::Result<TapTree> {
    let l = Layout::at(j, game_id, keys[(j - 1) as usize].mover);
    let mut leaves = disprove_family(g, ctx, &l, &keys[(j - 1) as usize]);
    if (j as usize) < keys.len() {
        let next = Layout::at(j + 1, game_id, keys[j as usize].mover);
        leaves.push(post_leaf(g, ctx, &next, &keys[j as usize], Some(&keys[(j - 1) as usize]), "post"));
    }
    leaves.extend(g.mover_splits(ctx, &l, &keys[(j - 1) as usize], outcomes));
    TapTree::new(leaves)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn level_message_layout() {
        let m = level_message(&[1u8; 20], &[9u8; 20]);
        assert_eq!(m.len() as u32, LEVEL_BYTES);
        assert_eq!(level_params().message_digits, 80);
    }

    /// The BLAKE3 mismatch checks the level disproves carry: tic-tac-toe's
    /// leaf preimage (9 bytes), the search's (50 bytes, one block still),
    /// an internal node (40 bytes).
    #[test]
    fn blake3_check_sizes() {
        for n in [9u32, 40, 50] {
            println!("V25 BLAKE3 mismatch over {n} bytes: {} B", blake3_mismatch_script(n).len());
        }
        assert_eq!(6 + ZK_CHOICE_BYTES, 50);
    }
}
