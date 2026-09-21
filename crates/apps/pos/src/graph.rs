//! The wired PoS absence-claim graph (POS_FACTCHAIN_PLAN.md step 4b; D34's
//! leaf family, wired per depth, with D35's two-head refutation).
//!
//! Per depth `d` (the slot the mover should have published at), with the
//! claimant the non-mover:
//!
//! - on the contract output: `absent_d`, the claimant's absence claim,
//!   spendable once `claim_from` (the Bitcoin height after the mover's slot
//!   window) has passed (CLTV) — 2-of-2, so the claim transaction is
//!   pre-signed at setup and its output is pinned to the claim tree;
//! - the claim output's tree: the mover's refutation (the D33 leaf at
//!   depth 1, the D35 two-head leaf from depth 2 — the slots' epoch tables
//!   as script constants) racing the claimant's timeout splits (CSV =
//!   `delta`, gated by the claimant's code reveal);
//! - the refutation output's tree: the claimant's disprove family over the
//!   parked tuple (CSV = `delta`), then the mover's self-checking splits by
//!   the revealed outcome code (CSV = `delta + delta'` — "by the code the
//!   victim revealed", the D28 discipline, with `code == R(parked state)`
//!   proven in-leaf).
//!
//! Two wirings the bare leaf family did not have: the refutation leaf is
//! gated by the mover's payment key and pre-signed, so the refutation's
//! output is pinned to the refuted tree (ungated, the mover could skip the
//! disprove stage by spending the claim output elsewhere — safe for a legal
//! move, theft for an illegal one); and the splits on the refuted output
//! check the code against the parked state, because a PoS refutation
//! carries no code reveal for a `code_mismatch` leaf to judge.

use anyhow::Result;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_contract::leaves::split_leaf;
use lngap_contract::Outcome;
use lngap_ec_wots::EpochTable;
use lngap_lamport::gadgets::LamportExt;
use lngap_lamport::winternitz::WotsPublic;
use lngap_lamport::BitCommit;

use crate::chess;
use crate::instance::{Game, PosDepthKeys};
use crate::refute;
use crate::ttt::{self, Layout};

/// The authorship fragment of the instance's game (D41; the chess mapping
/// is chess.rs's).
fn authorship(b: Builder, game: Game, file: usize, head_off: usize, key: &lngap_lamport::PublicKey) -> Builder {
    match game {
        Game::Ttt => ttt::authorship_fragment(b, file, head_off, key),
        Game::Chess => chess::authorship_fragment(b, file, head_off, key),
    }
}

/// The absence-claim leaf for one depth on the contract output.
pub fn absent_leaf(ctx: &CommitCtx, name: &str, claimant: Role, claim_from: u32) -> Leaf {
    let mut b = Builder::new().cltv(claim_from);
    let mut tl = Timelock::cltv(claim_from);
    if claimant == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    b = ctx.two_of_two_verify(b);
    Leaf::new(name.to_string(), b.push_int(1).into_script(), tl)
}

/// The mover's refutation leaf on the claim output: the mover's payment
/// signature first (the pre-signed skeleton pins the output to the refuted
/// tree), then the readout-and-park. The D41 authorship fragment rides the
/// gate slot: per parked head, the witness's preimages of THAT head's
/// mover's state key must open the head's claimed state bit by bit (21 per
/// head for tic-tac-toe, 336 for chess) — a garbage-signed attested entry
/// admits no refutation.
pub fn refute_leaf(ctx: &CommitCtx, game: Game, l: &Layout, table_prev: Option<&EpochTable>, table: &EpochTable, keys: &PosDepthKeys, keys_prev: Option<&PosDepthKeys>) -> Leaf {
    let body = match table_prev {
        Some(tp) => refute::refute_leaf_pair_gated(tp, table, &keys.refute, |b| {
            // the D41 authorship gate: tic-tac-toe checks BOTH parked heads
            // (21 bits each, cheap); chess checks the NEW head alone — the
            // judged move's — because 2 x 336 preimage blocks do not fit
            // the 1,000-element stack under the readout (D42). The prior
            // head's authenticity is inductive: an unauthored head at d-1
            // is unrefutable at d-1's own claim, so a game never continues
            // past one.
            let b = authorship(b, game, l.file, l.new, &keys.state);
            match game {
                Game::Ttt => authorship(b, game, l.file, 0, &keys_prev.expect("a pair has a prior").state),
                Game::Chess => b,
            }
        }),
        None => refute::refute_leaf(table, &keys.refute, |b| authorship(b, game, l.file, 0, &keys.state)),
    };
    let mut b = Builder::new().checksigverify(&ctx.key(l.mover).payment);
    for ins in body.instructions() {
        b = match ins.expect("valid script") {
            bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
            bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
        };
    }
    Leaf::new("refute", b.into_script(), Timelock::NONE)
}

/// The terminal-exhibit leaf for one depth on the CONTRACT output (D37,
/// the terminal-claim hole's fix): the mover of move `d` — the winner, or
/// the last mover of a draw — exhibits the attested pair
/// `head(d-1) || head(d)` with the status gate on top: the leaf fires only
/// when the parked new state is TERMINAL, and the exhibit output's tree
/// (the refuted tree verbatim) pays R(parked terminal). Without the gate
/// the exhibit would fire on any attested open state, and R(open) pays the
/// mover who just moved — a mid-game self-claim button the disprove family
/// cannot see (the exhibited move is legal).
///
/// The wiring is `absent_d`'s: CLTV to after slot `d`'s window (the
/// attestation must exist) plus 2-of-2, so the exhibit transaction is
/// pre-signed and the exhibit output is pinned to its tree. The key is the
/// depth-`d` refute key — both leaves bind the same two epoch tables, so
/// the signed message is provably the same 96 bytes, and the contexts are
/// mutually exclusive (the contract output is spent once): the WOTS
/// one-time-ness is preserved by construction. The exhibit exists from
/// depth 5 (tic-tac-toe cannot be terminal before move 5 — the
/// never-fire-trim discipline).
pub fn exhibit_leaf(
    ctx: &CommitCtx,
    name: &str,
    l: &Layout,
    table_prev: &EpochTable,
    table: &EpochTable,
    keys: &PosDepthKeys,
    keys_prev: &PosDepthKeys,
    claim_from: u32,
) -> Leaf {
    let mut b = Builder::new().cltv(claim_from);
    let mut tl = Timelock::cltv(claim_from);
    if l.mover == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    b = ctx.two_of_two_verify(b);
    let body = refute::refute_leaf_pair_gated(table_prev, table, &keys.refute, |b| {
        let b = ttt::authorship_fragment(b, l.file, l.new, &keys.state);
        let b = ttt::authorship_fragment(b, l.file, 0, &keys_prev.state);
        ttt::terminal_gate_fragment(b, l.file, l.new)
    });
    for ins in body.instructions() {
        b = match ins.expect("valid script") {
            bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
            bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
        };
    }
    Leaf::new(name.to_string(), b.into_script(), tl)
}

/// The player-equivocation leaf for one (depth, state bit) on the CONTRACT
/// output (POS_FACTCHAIN_PLAN.md step 6; D39): the witness exhibits BOTH
/// preimages of bit `i` of the depth-`d` mover's state key — the 46-byte
/// `LamportExt::equivocation` gadget (`hash160_verify(h1)` then
/// `hash160_verify(h0)`). A venue entry's signature IS the reveal of the
/// state under that key, so both preimages of one bit exist only if the
/// mover signed two conflicting states at that depth (a reorg-aided
/// double-play, GAME_PROTOCOL.md section 5 item 4). The proof is
/// self-authenticating — no venue data, no timelock — and idempotent
/// re-broadcast of the SAME entry after a reorg reveals the same
/// preimages, so an honest re-publication never opens the leaf. The spend
/// is the graph's standard 2-of-2 pre-signed skeleton paying the exhibitor
/// (the depth's non-mover) the pot; the witness carries
/// `p0, p1, sig_hub, sig_user` (sig_user on top: the 2-of-2 checks first).
pub fn equiv_leaf(ctx: &CommitCtx, name: &str, bit: &BitCommit, exhibitor: Role) -> Leaf {
    let mut b = Builder::new();
    let mut tl = Timelock::NONE;
    if exhibitor == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    b = ctx.two_of_two_verify(b).equivocation(bit);
    Leaf::new(name.to_string(), b.push_int(1).into_script(), tl)
}

/// The tree of the claim output A_d: the mover's refutation plus the
/// claimant's timeout splits after the dispute window (`delta`), gated by
/// the claimant's code reveal.
pub fn claim_tree(
    ctx: &CommitCtx,
    game: Game,
    l: &Layout,
    table_prev: Option<&EpochTable>,
    table: &EpochTable,
    keys: &PosDepthKeys,
    keys_prev: Option<&PosDepthKeys>,
    outcomes: &[Outcome],
) -> Result<TapTree> {
    let mut leaves = vec![refute_leaf(ctx, game, l, table_prev, table, keys, keys_prev)];
    for o in outcomes {
        leaves.push(split_leaf(ctx, o, ctx.params.delta, &keys.claimant_code));
    }
    TapTree::new(leaves)
}

/// The tree of the refutation output P_d: the claimant's disprove family
/// over the parked tuple (after `delta`) — the game's own predicate set —
/// then the mover's self-checking splits after `delta + delta'`.
pub fn refuted_tree(ctx: &CommitCtx, game: Game, l: &Layout, keys: &PosDepthKeys, outcomes: &[Outcome]) -> Result<TapTree> {
    let challenger = ctx.key(l.mover.other()).payment;
    let family = match game {
        Game::Ttt => ttt::disprove_leaves(l, &keys.refute),
        Game::Chess => chess::disprove_leaves(l, &keys.refute),
    };
    let mut leaves = vec![];
    for pl in family {
        let mut b = Builder::new().csv(ctx.params.delta).checksigverify(&challenger);
        for ins in pl.script.instructions() {
            b = match ins.expect("valid script") {
                bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
                bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
            };
        }
        leaves.push(Leaf::new(format!("disprove_{}", pl.name), b.into_script(), Timelock::csv(ctx.params.delta)));
    }
    let w = ctx.params.delta + ctx.params.delta_prime;
    for o in outcomes {
        let leaf = match game {
            Game::Ttt => ttt::checked_split_leaf(ctx, l, o, w, &keys.mover_code, &keys.refute),
            Game::Chess => chess::checked_split_leaf(ctx, l, o, w, &keys.mover_code, &keys.refute),
        };
        leaves.push(leaf);
    }
    TapTree::new(leaves)
}
