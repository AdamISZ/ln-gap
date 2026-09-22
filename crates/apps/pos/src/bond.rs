//! The validator bond (POS_FACTCHAIN_PLAN.md step 5; D38): the venue
//! attester's staked UTXO on Bitcoin, script-only (a NUMS internal key, so
//! there is no unilateral keyspend to race a slash), with three spend
//! families:
//!
//! - `reclaim`: the validator's refund, CLTV'd to `expiry` — the covered
//!   slot range's end plus the challenge window, so the bond cannot be
//!   yanked before the attestations it secures are final;
//! - `burn`: anyone who reveals the group SECRET may spend the bond. The
//!   mirror (`hash160` of the secret, committed at setup via
//!   `Attester::burn_mirror`) is what Script can check; the secret becomes
//!   known only through an equivocation under the fixed-R nonce discipline
//!   (`Attester::new_fixed_r`), where a second value attested at one chunk
//!   reuses the chunk's nonce and `extract_group_key` recovers the key
//!   (the Schnorr/DLC same-R failure). Consequence on leak: the key is
//!   public, so the group key must rotate — the heavier path, per
//!   EC_WOTS.md section 6;
//! - `slash_{slot}_{j}`: per covered slot and chunk position, the
//!   witness-parameterized possession-pair leaf (`slash_leaf_any`) — two
//!   opened points at one (slot, chunk) prove the attester signed two
//!   different messages for that slot. One leaf per chunk position (the
//!   values arrive in the witness), not 120 hardcoded value pairs.
//!
//! WHAT THE EVIDENCE PATHS ENFORCE (D46). Neither `burn` nor `slash`
//! constrains the spending transaction's outputs — Script cannot, without
//! a covenant — and the evidence (the attested scalars; the leaked key) is
//! held by the cheater first of all. So the paths are anyone-can-spend on
//! evidence, and what makes them a penalty is the RACE: every evidence
//! leaf carries `CLTV race_from`, a height fixed at setup, so the
//! cheater's head start (knowing of its own equivocation first) is
//! useless — the attestations are public data on the venue long before
//! the race opens, anyone can build the spend, and the winning spend is
//! the one paying the most fee. A miner takes the whole bond as fee by
//! including its own spend (one zero-value OP_RETURN output, everything to
//! fee), so the cheater keeps the bond only by mining the first eligible
//! block itself: with hashpower share `p` the expected loss is `(1 - p)`
//! of the bond, the sizing rule of D46. The spends opt into RBF (the
//! `Timelock` sequences are `ENABLE_RBF_NO_LOCKTIME`), so a low-fee
//! self-payment is replaced by any higher-fee competitor. The value is
//! never destroyed by Script; it is destroyed (to miners) by the market.
//! Covenant or deleted-key presigned alternatives are recorded in D46.
//!
//! What a watcher needs (the plumbing is deliberately NOT built here): the
//! two attestations of one slot (the client layer already names the event
//! — `PosClient::observe` returns `Observation::Equivocation`), the
//! slot's epoch table and the chunk's nonce point (venue registry data),
//! and the bond's outpoint and tree. This module builds only the bond
//! itself; the bond-world fixture in tests/pos_bond.rs plays the watcher
//! by hand.

use anyhow::{ensure, Result};
use bitcoin::key::XOnlyPublicKey;
use bitcoin::script::Builder;
use bitcoin::Amount;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_btc::Hash160;
use lngap_ec_wots::EpochTable;

/// The bond's parameters, fixed at setup.
pub struct BondSpec {
    /// The staked amount.
    pub value: Amount,
    /// The validator's reclaim key (the timelocked refund path).
    pub validator: XOnlyPublicKey,
    /// The reclaim leaf's absolute timelock: the covered slot range's end
    /// plus the challenge window.
    pub expiry: u32,
    /// The evidence race opens here (D46): every `slash` and `burn` leaf is
    /// `CLTV race_from`. Must leave a window before `expiry` wide enough
    /// for watchers and miners to act on public evidence — the cheater's
    /// only remaining advantage is mining the first eligible block.
    pub race_from: u32,
    /// The burn-path commitment: `hash160` of the group secret (the
    /// attester computes it at bond setup — `Attester::burn_mirror`).
    pub burn_mirror: Hash160,
}

/// The bond's taptree over the covered slots' epoch tables (the venue's
/// registry data — the bond must be built against the tables the venue
/// actually attests under, exactly the game graphs' build-time-data
/// discipline).
pub fn bond_tree(spec: &BondSpec, covered: &[(u32, &EpochTable)]) -> Result<TapTree> {
    ensure!(spec.race_from < spec.expiry, "the evidence race must open before the reclaim");
    let race = Timelock::cltv(spec.race_from);
    let mut leaves = vec![
        Leaf::new(
            "reclaim",
            Builder::new()
                .cltv(spec.expiry)
                .checksigverify(&spec.validator)
                .push_int(1)
                .into_script(),
            Timelock::cltv(spec.expiry),
        ),
        Leaf::new(
            "burn",
            Builder::new()
                .cltv(spec.race_from)
                .hash160_verify(&spec.burn_mirror)
                .push_int(1)
                .into_script(),
            race,
        ),
    ];
    for (slot, table) in covered {
        for j in 0..table.chunks {
            // the evidence gadget, behind the race's CLTV
            let mut b = Builder::new().cltv(spec.race_from);
            for ins in lngap_ec_wots::slash_leaf_any(table, j).instructions() {
                b = match ins.expect("valid script") {
                    bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
                    bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
                };
            }
            leaves.push(Leaf::new(format!("slash_{slot}_{j}"), b.into_script(), race));
        }
    }
    ensure!(leaves.len() >= 2, "no leaves");
    TapTree::new(leaves)
}
