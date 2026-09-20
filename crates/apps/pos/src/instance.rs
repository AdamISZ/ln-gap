//! The wired PoS absence-claim instance (POS_FACTCHAIN_PLAN.md step 4b):
//! the per-depth key sets derived in the party keystores' label discipline
//! and exchanged at the draft, and the pre-signed graph over the D34/D35
//! leaf family.
//!
//! Per depth `d` (the slot the mover should have published at):
//!
//! - `refute`: the MOVER's Winternitz key — 96 bytes (the two-head pair
//!   `head(d-1) || head(d)`, D35) from depth 2, 48 bytes (the single head)
//!   at depth 1. Its reveal parks the attested tuple on-chain.
//! - `code`: the mover's Lamport outcome-code key, gating the refuted
//!   output's self-checking splits.
//! - `ccode`: the claimant's Lamport outcome-code key, gating the claim
//!   output's timeout splits.
//!
//! The labels are the contract crate's (`key_label(id, seq, depth,
//! field)`); the exchange mirrors the draft's: each side fills its own keys
//! (`gen_pos_keys`), the pubs cross (`collect_keys`), and both parties
//! build the same [`PosInstance`] — the graph's script pubkeys agree iff
//! the merged key sets agree.
//!
//! The disprove spends are NOT pre-signed: they are the claimant's own
//! runtime transactions (their witness is the refutation's reveal, unknown
//! at setup; the claimant signs at dispute time). Everything else is a
//! pre-signed skeleton here — including the refutation, whose pinned output
//! is the whole point (see graph.rs's module docs).
//!
//! Deferred from this wiring (the D34/D36 lists): the PoS signature exhibit
//! (a garbage-signed attested entry is a claim, D31's analogue), the party
//! policies and the S1-S9 scenario port, and the terminal-claim hole (D36).

use anyhow::{bail, ensure, Result};
use bitcoin::{Amount, OutPoint, TxOut};
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::{build_spend, Timelock};
use lngap_channel::{CommitCtx, PresignedTx, Role};
use lngap_contract::instance::key_label;
use lngap_contract::{Contract, Outcome, Payout, CODE_BITS};
use lngap_ec_wots::EpochTable;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsPublic;
use lngap_lamport::PublicKey;
use lngap_tictactoe::{Board, TicTacToe};

use crate::graph;
use crate::ttt::Layout;

/// Tic-tac-toe's mover at depth `d` from the empty board: user at odd
/// depths.
pub fn mover_at(d: u32) -> Role {
    if d % 2 == 1 { Role::User } else { Role::Hub }
}

/// The label of the mover's refute key at depth `d`.
pub fn refute_label(id: u32, seq: u64, d: u32) -> String {
    key_label(id, seq, d, "refute")
}
/// The label of the mover's outcome-code key at depth `d`.
pub fn code_label(id: u32, seq: u64, d: u32) -> String {
    key_label(id, seq, d, "code")
}
/// The label of the claimant's outcome-code key at depth `d`.
pub fn ccode_label(id: u32, seq: u64, d: u32) -> String {
    key_label(id, seq, d, "ccode")
}

/// What one side contributes at one depth (pubs only; the secrets stay in
/// its key store).
#[derive(Clone, Debug, Default)]
pub struct PosKeyOffer {
    pub refute: Option<WotsPublic>,
    pub mover_code: Option<PublicKey>,
    pub claimant_code: Option<PublicKey>,
}

/// Generate `me`'s half of every depth's key set: the refute and code keys
/// where I move, the claimant code key where I don't.
pub fn gen_pos_keys(ks: &mut KeyStore, me: Role, id: u32, seq: u64, max_depth: u32) -> Result<Vec<(u32, PosKeyOffer)>> {
    let mut out = Vec::new();
    for d in 1..=max_depth {
        let mut offer = PosKeyOffer::default();
        if mover_at(d) == me {
            offer.refute = Some(ks.generate_wots(&refute_label(id, seq, d), if d >= 2 { 96 } else { 48 })?);
            offer.mover_code = Some(ks.generate(&code_label(id, seq, d), CODE_BITS)?);
        } else {
            offer.claimant_code = Some(ks.generate(&ccode_label(id, seq, d), CODE_BITS)?);
        }
        out.push((d, offer));
    }
    Ok(out)
}

/// The per-depth key set, merged from both sides' offers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PosDepthKeys {
    pub mover: Role,
    pub refute: WotsPublic,
    pub mover_code: PublicKey,
    pub claimant_code: PublicKey,
}

/// Merge two sides' offers into the per-depth key sets: each field must
/// come from the side that owns it (the mover's from the mover, the
/// claimant code from the claimant) and exactly once.
pub fn collect_keys(mine: &[(u32, PosKeyOffer)], theirs: &[(u32, PosKeyOffer)], max_depth: u32) -> Result<Vec<PosDepthKeys>> {
    let mut out = Vec::new();
    for d in 1..=max_depth {
        let mover = mover_at(d);
        let (a, b) = (mine.get(d as usize - 1), theirs.get(d as usize - 1));
        let (Some((da, a)), Some((db, b))) = (a, b) else {
            bail!("offers missing depth {d}");
        };
        ensure!(*da == d && *db == d, "offers out of order at depth {d}");
        let take = |x: &Option<WotsPublic>, y: &Option<WotsPublic>| -> Result<WotsPublic> {
            Ok(x.clone().or_else(|| y.clone()).ok_or_else(|| anyhow::anyhow!("depth {d}: refute key missing"))?)
        };
        let refute = take(&a.refute, &b.refute)?;
        let take_l = |x: &Option<PublicKey>, y: &Option<PublicKey>, what: &str| -> Result<PublicKey> {
            Ok(x.clone().or_else(|| y.clone()).ok_or_else(|| anyhow::anyhow!("depth {d}: {what} missing"))?)
        };
        let mover_code = take_l(&a.mover_code, &b.mover_code, "mover code")?;
        let claimant_code = take_l(&a.claimant_code, &b.claimant_code, "claimant code")?;
        out.push(PosDepthKeys { mover, refute, mover_code, claimant_code });
    }
    Ok(out)
}

/// A PoS absence-claim game instance: the tuple both parties build after
/// the key exchange.
#[derive(Clone, Debug)]
pub struct PosInstance {
    pub id: u32,
    pub value: Amount,
    pub deadline: u32,
    pub game_id: u16,
    /// The Bitcoin height the venue's slot count starts from: slot `d`
    /// seals at `btc_open + d` (one venue block per Bitcoin block).
    pub btc_open: u32,
    /// Blocks after slot `d`'s seal before a depth-`d` claim may be made.
    pub grace: u32,
    /// Index `d - 1`.
    pub keys: Vec<PosDepthKeys>,
    pub outcomes: Vec<Outcome>,
}

impl PosInstance {
    pub fn new(id: u32, value: Amount, deadline: u32, game_id: u16, btc_open: u32, grace: u32, keys: Vec<PosDepthKeys>) -> Result<PosInstance> {
        ensure!(!keys.is_empty(), "no depths");
        for (i, k) in keys.iter().enumerate() {
            let d = i as u32 + 1;
            ensure!(k.mover == mover_at(d), "depth {d}: mover mismatch");
            let want = if d >= 2 { 192 } else { 96 };
            ensure!(k.refute.params.message_digits == want, "depth {d}: refute key size");
            ensure!(k.mover_code.n_bits() == CODE_BITS && k.claimant_code.n_bits() == CODE_BITS, "depth {d}: code key size");
        }
        let outcomes = Contract::outcomes(&TicTacToe);
        Ok(PosInstance { id, value, deadline, game_id, btc_open, grace, keys, outcomes })
    }

    pub fn max_depth(&self) -> u32 {
        self.keys.len() as u32
    }

    /// The Bitcoin height from which a depth-`d` claim may be made.
    pub fn claim_from(&self, d: u32) -> u32 {
        self.btc_open + d + 1 + self.grace
    }

    pub fn layout(&self, d: u32) -> Layout {
        Layout::at(d, self.game_id, self.keys[(d - 1) as usize].mover)
    }

    pub fn depth_keys(&self, d: u32) -> &PosDepthKeys {
        &self.keys[(d - 1) as usize]
    }

    /// The contract output's tree: `revoke`, `settle`, and `absent_1..=M`.
    pub fn tree(&self, ctx: &CommitCtx) -> Result<TapTree> {
        let mut leaves = vec![ctx.revoke_leaf(), lngap_contract::leaves::settle_leaf(ctx, self.deadline)];
        for d in 1..=self.max_depth() {
            leaves.push(graph::absent_leaf(ctx, &format!("absent_{d}"), mover_at(d).other(), self.claim_from(d)));
        }
        TapTree::new(leaves)
    }

    /// The claim output's tree at depth `d`. `tables` is the venue's epoch
    /// table registry, indexed by slot (the refutation leaf embeds the head
    /// chunks' points of slots `d - 1` and `d`).
    pub fn claim_tree(&self, ctx: &CommitCtx, d: u32, tables: &[EpochTable]) -> Result<TapTree> {
        let l = self.layout(d);
        let (prev, table) = if d >= 2 { (Some(&tables[(d - 1) as usize]), &tables[d as usize]) } else { (None, &tables[1]) };
        graph::claim_tree(ctx, &l, prev, table, self.depth_keys(d), &self.outcomes)
    }

    /// The refutation output's tree at depth `d`.
    pub fn refuted_tree(&self, ctx: &CommitCtx, d: u32) -> Result<TapTree> {
        graph::refuted_tree(ctx, &self.layout(d), self.depth_keys(d), &self.outcomes)
    }

    /// Payout outputs for `payout` of `v` to the parties' payout scripts.
    fn dist_outputs(&self, ctx: &CommitCtx, payout: Payout, v: Amount) -> Vec<TxOut> {
        payout
            .dist(v)
            .iter()
            .zip(Role::BOTH)
            .filter(|(a, _)| **a >= ctx.params.dust)
            .map(|(a, r)| TxOut { value: *a, script_pubkey: ctx.key(r).payout_spk.clone() })
            .collect()
    }

    /// The pre-signed skeletons hanging off the contract output: `settle`,
    /// and per depth the absence claim, the refutation, the timeout splits,
    /// and the self-checking splits (labels `absent_d/…`). The disprove
    /// spends are the claimant's runtime transactions.
    pub fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut, tables: &[EpochTable]) -> Result<Vec<PresignedTx>> {
        let fee = ctx.params.presign_fee;
        let mut out = Vec::new();
        let tree0 = self.tree(ctx)?;
        let r = Contract::resolution(&TicTacToe, &Board::empty());
        let tx = build_spend(outpoint, &tree0.leaf("settle")?.timelock, self.dist_outputs(ctx, r.payout, self.value - fee));
        out.push(PresignedTx::new("settle", tx, vec![prevout.clone()], &tree0, "settle", format!("settle: R(s) = {}", r.name))?);
        for d in 1..=self.max_depth() {
            let a_tree = self.claim_tree(ctx, d, tables)?;
            let p_tree = self.refuted_tree(ctx, d)?;
            let name = format!("absent_{d}");
            let tx = build_spend(outpoint, &tree0.leaf(&name)?.timelock, vec![TxOut { value: self.value - fee, script_pubkey: a_tree.script_pubkey() }]);
            let a_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
            let a_prev = tx.output[0].clone();
            out.push(PresignedTx::new(name.clone(), tx, vec![prevout.clone()], &tree0, &name, format!("absence claim at depth {d}"))?);
            let rtx = build_spend(a_op, &Timelock::NONE, vec![TxOut { value: a_prev.value - fee, script_pubkey: p_tree.script_pubkey() }]);
            let p_op = OutPoint { txid: rtx.compute_txid(), vout: 0 };
            let p_prev = rtx.output[0].clone();
            out.push(PresignedTx::new(format!("{name}/refute"), rtx, vec![a_prev.clone()], &a_tree, "refute", format!("refutation at depth {d}"))?);
            for o in &self.outcomes {
                let leaf = format!("split_{}", o.name);
                let tx = build_spend(a_op, &a_tree.leaf(&leaf)?.timelock, self.dist_outputs(ctx, o.payout, a_prev.value - fee));
                out.push(PresignedTx::new(format!("{name}/{leaf}"), tx, vec![a_prev.clone()], &a_tree, &leaf, format!("timeout split at depth {d}: {}", o.name))?);
            }
            for o in &self.outcomes {
                let leaf = format!("split_{}", o.name);
                let tx = build_spend(p_op, &p_tree.leaf(&leaf)?.timelock, self.dist_outputs(ctx, o.payout, p_prev.value - fee));
                out.push(PresignedTx::new(format!("{name}/refuted/{leaf}"), tx, vec![p_prev.clone()], &p_tree, &leaf, format!("split of the refuted output at depth {d}: {}", o.name))?);
            }
        }
        Ok(out)
    }
}
