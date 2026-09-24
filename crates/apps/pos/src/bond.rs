//! The validator bond (POS_FACTCHAIN_PLAN.md step 5; D38, D46, D48): the
//! venue attester's locked UTXO on Bitcoin, script-only (a NUMS internal
//! key, so there is no keyspend).
//!
//! The BASELINE (D48) is a plain lock: one `reclaim` leaf, the validator's
//! key behind `CLTV expiry`. The cost of participating in the venue is the
//! time value of that lock; the benefit is the fee stream
//! (ATTESTATION_FEES.md); misbehaviour — an equivocation, a pair of
//! openings at one (slot, chunk), self-certifying evidence anyone can
//! publish — is punished by EJECTION, the loss of the fee stream while the
//! lock sits out its term. Nothing on-chain executes evidence against the
//! baseline bond, and nothing needs to: the evidence pair is proof on its
//! face (per-value nonces, D47: nothing leaks on equivocation, neither the
//! group key nor a share).
//!
//! The OPTION (`BondSpec::evidence`, D46): capital at risk. Per covered
//! slot and chunk position a `slash_{slot}_{j}` leaf — the witness-
//! parameterized possession-pair gadget (`slash_leaf_any`: two opened
//! points at one (slot, chunk) prove the attester signed two different
//! messages for that slot) — behind `CLTV expiry - race_window`. What the
//! leaf enforces is a RACE, not a burn: Script cannot constrain the
//! spending transaction's outputs without a covenant, and the evidence is
//! held first by the cheater, so the leaf is anyone-can-spend on evidence
//! and the winning spend at the race height is the highest-fee one — a
//! miner's, taking the whole bond as fee via a zero-value OP_RETURN
//! output. The race opens late, just before the reclaim, so the capital
//! stays locked until near `expiry` in every outcome (as under the plain
//! lock) and the race can only take the principal, never hand it back
//! early: with hashpower share `p` the expected loss is `(1 - p)` of the
//! bond. The spends opt into RBF (the `Timelock` sequences are
//! `ENABLE_RBF_NO_LOCKTIME`). A venue may adopt this; it is not the
//! baseline because a quorum-level slash is collective by construction
//! and needs the miner race for want of covenants (D48).
//!
//! What a watcher needs, either way: the two attestations of one slot (the
//! client layer names the event — `PosClient::observe` returns
//! `Observation::Equivocation`). This module builds only the bond itself;
//! tests/pos_bond.rs plays the watcher by hand.

use anyhow::{ensure, Result};
use bitcoin::key::XOnlyPublicKey;
use bitcoin::script::Builder;
use bitcoin::Amount;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_ec_wots::EpochTable;

/// The bond's parameters, fixed at setup.
pub struct BondSpec {
    /// The locked amount.
    pub value: Amount,
    /// The validator's reclaim key (the timelocked refund path).
    pub validator: XOnlyPublicKey,
    /// The reclaim leaf's absolute timelock: the covered slot range's end
    /// plus the challenge window.
    pub expiry: u32,
    /// Capital at risk (the D46 option); `None` is the D48 baseline, a
    /// plain lock.
    pub evidence: Option<Evidence>,
}

/// The capital-at-risk option: evidence leaves behind a late race.
pub struct Evidence {
    /// The evidence race opens `race_window` blocks before `expiry`: every
    /// `slash` leaf is `CLTV expiry - race_window`. Wide enough for
    /// watchers and miners to act on public evidence, narrow enough that
    /// the capital stays locked until near the reclaim in every outcome.
    pub race_window: u32,
}

impl BondSpec {
    /// The height the evidence race opens at (`None` for the plain lock).
    pub fn race_from(&self) -> Option<u32> {
        self.evidence.as_ref().map(|e| self.expiry - e.race_window)
    }
}

/// The bond's taptree over the covered slots' epoch tables (the venue's
/// registry data — the bond must be built against the tables the venue
/// actually attests under, exactly the game graphs' build-time-data
/// discipline).
pub fn bond_tree(spec: &BondSpec, covered: &[(u32, &EpochTable)]) -> Result<TapTree> {
    let mut leaves = vec![Leaf::new(
        "reclaim",
        Builder::new()
            .cltv(spec.expiry)
            .checksigverify(&spec.validator)
            .push_int(1)
            .into_script(),
        Timelock::cltv(spec.expiry),
    )];
    match &spec.evidence {
        None => ensure!(covered.is_empty(), "the plain lock carries no evidence leaves; pass no covered slots"),
        Some(ev) => {
            ensure!(0 < ev.race_window && ev.race_window < spec.expiry, "the evidence race must open before the reclaim");
            let race_from = spec.expiry - ev.race_window;
            let race = Timelock::cltv(race_from);
            for (slot, table) in covered {
                for j in 0..table.chunks {
                    // the evidence gadget, behind the race's CLTV
                    let mut b = Builder::new().cltv(race_from);
                    for ins in lngap_ec_wots::slash_leaf_any(table, j).instructions() {
                        b = match ins.expect("valid script") {
                            bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
                            bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
                        };
                    }
                    leaves.push(Leaf::new(format!("slash_{slot}_{j}"), b.into_script(), race));
                }
            }
        }
    }
    TapTree::new(leaves)
}
