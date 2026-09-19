//! The PoS absence-claim graph's trees (POS_FACTCHAIN_PLAN.md step 4; D33).
//!
//! Per depth `d` (the slot the mover should have published at), with the
//! claimant the non-mover:
//!
//! - on the contract output: `absent`, the claimant's absence claim,
//!   spendable once `claim_from` (the Bitcoin height after the mover's slot
//!   window) has passed (CLTV);
//! - the claim output's tree: the mover's refutation (the D33 leaf, the
//!   slot's epoch table as script constants) racing the claimant's timeout
//!   splits (CSV = `delta`, gated by the claimant's code reveal);
//! - the refutation output's tree: the claimant's disprove over the parked
//!   tuple (CSV = `delta`), then the mover's splits by the revealed outcome
//!   code (CSV = `delta + delta_prime` — "by the code the victim revealed",
//!   the D28 discipline).
//!
//! This is the leaf family and the tree shapes, proven on regtest in
//! tests/pos_graph.rs. The ContractInstance/draft plumbing (per-depth key
//! sets through the party layer) and the two-head refutation (prior-state
//! predicates; the plan's 5.1) are the follow-up increments.

use anyhow::Result;
use bitcoin::key::XOnlyPublicKey;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::CommitCtx;
use lngap_contract::leaves::split_leaf;
use lngap_contract::Outcome;
use lngap_ec_wots::EpochTable;
use lngap_lamport::winternitz::WotsPublic;
use lngap_lamport::PublicKey as LamportKey;

use crate::refute;

/// The absence-claim leaf on the contract output for one depth: spendable
/// by the claimant once `claim_from` (the Bitcoin height after the mover's
/// slot window) has passed.
pub fn absent_leaf(claimant: &XOnlyPublicKey, claim_from: u32) -> Leaf {
    let b = Builder::new().cltv(claim_from).checksigverify(claimant).push_int(1);
    Leaf::new("absent", b.into_script(), Timelock::cltv(claim_from))
}

/// The tree of the claim output A_d: the mover's refutation plus the
/// claimant's timeout splits after the dispute window (`delta`), gated by
/// the claimant's code reveal.
pub fn claim_tree(
    ctx: &CommitCtx,
    table: &EpochTable,
    refute_key: &WotsPublic,
    outcomes: &[Outcome],
    claimant_code: &LamportKey,
) -> Result<TapTree> {
    let mut leaves = vec![Leaf::new("refute", refute::refute_leaf(table, refute_key), Timelock::NONE)];
    for o in outcomes {
        leaves.push(split_leaf(ctx, o, ctx.params.delta, claimant_code));
    }
    TapTree::new(leaves)
}

/// The tree of the refutation output P_d: the claimant's disprove over the
/// parked tuple (after `delta`), then the mover's splits after
/// `delta + delta_prime`, gated by the mover's code reveal.
pub fn refuted_tree(
    ctx: &CommitCtx,
    refute_key: &WotsPublic,
    challenger: &XOnlyPublicKey,
    outcomes: &[Outcome],
    mover_code: &LamportKey,
) -> Result<TapTree> {
    // the disprove leaf: the parked-tuple predicate, gated to the
    // challenger after `delta` (the leaf_after wrap by hand)
    let mut b = Builder::new().csv(ctx.params.delta).checksigverify(challenger);
    for ins in refute::disprove_leaf_move_range(refute_key).instructions() {
        b = match ins.expect("valid script") {
            bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
            bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
        };
    }
    let mut leaves = vec![Leaf::new("disprove", b.into_script(), Timelock::csv(ctx.params.delta))];
    let w = ctx.params.delta + ctx.params.delta_prime;
    for o in outcomes {
        leaves.push(split_leaf(ctx, o, w, mover_code));
    }
    TapTree::new(leaves)
}
