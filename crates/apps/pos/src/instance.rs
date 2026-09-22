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
//! - `state`: the MOVER's Winternitz key over the state's signed bytes
//!   (D39, plan step 6; D43's WOTS form — was a per-bit Lamport key). The
//!   venue entry's signature is the reveal of the signed region under this
//!   key; a mover who double-signs at one depth (a reorg-aided double-play)
//!   is convicted by the two full signatures, and the `equiv_d` leaf on the
//!   contract output pays the exhibitor the pot.
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
//! is the whole point (see graph.rs's module docs), and from depth 2 the
//! COUNTER off each claim output (D44): the mover's thin claim one depth
//! back, whose output is the previous depth's claim tree verbatim (with its
//! refutation and splits pre-signed under that depth's keys, in a third
//! mutually exclusive context — the contract output is spent once). The
//! counter is what makes a thin claim's dueness enforceable: a claim at a
//! depth that was not due is countered and cannot be defended.
//!
//! Deferred from this wiring (the D34/D36 lists): the party policies
//! (including actually signing venue entries with the state key) and the
//! S1-S9 scenario port. The terminal-claim hole (D36) is CLOSED here: the
//! `exhibit_d` leaves (D37) let the mover of the last move park the
//! attested terminal pair under a `status != OPEN` gate and split to
//! R(parked terminal), the checked resolution the thin claim dropped. The
//! player-equivocation gap (GAME_PROTOCOL.md section 5 item 4) is CLOSED by
//! the `equiv_{d}_{i}` leaves (D39). The garbage-signed-entry hole (D40's
//! PS9, the deferred "PoS sig exhibit") is CLOSED by the D41 authorship
//! fragment riding the refute/exhibit gate slot (no sig exhibit, no
//! entry-tail binding): every parked head carries the in-script proof that
//! its mover's state key opens the head's claimed state.

use anyhow::{bail, ensure, Result};
use bitcoin::{Amount, OutPoint, TxOut};
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::{build_spend, Timelock};
use lngap_channel::{CommitCtx, PresignedTx, Role};
use lngap_contract::instance::key_label;
use lngap_contract::{Contract, Outcome, Payout, CODE_BITS};
use lngap_ec_wots::EpochTable;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsParams, WotsPublic};
use lngap_lamport::PublicKey;
use lngap_tictactoe::{Board, TicTacToe};

use crate::graph;
use crate::ttt::Layout;

/// Tic-tac-toe's mover at depth `d` from the empty board: user at odd
/// depths. (Chess's too: white = user moves at odd depths, the same parity.)
pub fn mover_at(d: u32) -> Role {
    if d % 2 == 1 { Role::User } else { Role::Hub }
}

/// The game a [`PosInstance`] plays. Selects the disprove family and the
/// authorship bit-mapping (graph.rs's dispatch), the per-depth state key
/// size, and whether the terminal-exhibit family exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Game {
    Ttt,
    Chess,
}

impl Game {
    /// Bytes the per-depth mover state key signs (D43: the Winternitz
    /// message): tic-tac-toe's 3 state bytes; chess's state||move (42).
    pub fn state_bytes(self) -> u32 {
        match self {
            Game::Ttt => 3,
            Game::Chess => 42,
        }
    }
    /// The first depth a terminal exhibit exists at, if the game has the
    /// family at all. Chess has NONE (D42): chess terminality is not a
    /// state field, and none is needed — mate at `t` makes the absence
    /// claim at `t + 1` unanswerable (a mated side has no legal move to
    /// refute with), a dead-depth claim at `t + 2` by the mated side is
    /// countered (D44: "you did not move at `t + 1`" — true, and
    /// unrefutable), the game is assumed to end before `w_max`, and
    /// interior draws do not exist under the PoC's stalemate-loses-by-stall
    /// reading — D37's dual-exhibit note is moot.
    pub fn min_exhibit_depth(self) -> Option<u32> {
        match self {
            Game::Ttt => Some(MIN_EXHIBIT_DEPTH),
            Game::Chess => None,
        }
    }
}

/// The first depth tic-tac-toe can be terminal at (the earliest win is
/// move 5). The terminal-exhibit leaves exist from here to `max_depth`
/// (D37) — shallower exhibits could never pass the status gate, the old
/// graph's never-fire-trim discipline.
pub const MIN_EXHIBIT_DEPTH: u32 = 5;

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
/// The label of the mover's state-signature key at depth `d` (D39).
pub fn state_label(id: u32, seq: u64, d: u32) -> String {
    key_label(id, seq, d, "state")
}

/// What one side contributes at one depth (pubs only; the secrets stay in
/// its key store).
#[derive(Clone, Debug, Default)]
pub struct PosKeyOffer {
    pub refute: Option<WotsPublic>,
    pub mover_code: Option<PublicKey>,
    pub claimant_code: Option<PublicKey>,
    pub state: Option<WotsPublic>,
}

/// Generate `me`'s half of every depth's key set: the refute, code and
/// state keys where I move, the claimant code key where I don't. The state
/// key's size is the game's (`Game::state_bytes`).
pub fn gen_pos_keys(ks: &mut KeyStore, me: Role, id: u32, seq: u64, max_depth: u32, game: Game) -> Result<Vec<(u32, PosKeyOffer)>> {
    let mut out = Vec::new();
    for d in 1..=max_depth {
        let mut offer = PosKeyOffer::default();
        if mover_at(d) == me {
            offer.refute = Some(ks.generate_wots(&refute_label(id, seq, d), if d >= 2 { 96 } else { 48 })?);
            offer.mover_code = Some(ks.generate(&code_label(id, seq, d), CODE_BITS)?);
            offer.state = Some(ks.generate_wots(&state_label(id, seq, d), game.state_bytes())?);
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
    pub state: WotsPublic,
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
        let state = take(&a.state, &b.state)?;
        out.push(PosDepthKeys { mover, refute, mover_code, claimant_code, state });
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
    /// The game whose disprove family and authorship mapping the graph
    /// runs (graph.rs's dispatch).
    pub game: Game,
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
    pub fn new(id: u32, value: Amount, deadline: u32, game_id: u16, game: Game, btc_open: u32, grace: u32, keys: Vec<PosDepthKeys>) -> Result<PosInstance> {
        ensure!(!keys.is_empty(), "no depths");
        for (i, k) in keys.iter().enumerate() {
            let d = i as u32 + 1;
            ensure!(k.mover == mover_at(d), "depth {d}: mover mismatch");
            let want = if d >= 2 { 192 } else { 96 };
            ensure!(k.refute.params.message_digits == want, "depth {d}: refute key size");
            ensure!(k.mover_code.n_bits() == CODE_BITS && k.claimant_code.n_bits() == CODE_BITS, "depth {d}: code key size");
            ensure!(k.state.params == WotsParams::for_bytes(game.state_bytes()), "depth {d}: state key size");
        }
        // the outcome list is the two games' shared one (UserWins 0 /
        // HubWins 1 / Draw 2); chess's Draw split can never fire on this
        // graph (chess.rs's resolution fragment).
        let outcomes = Contract::outcomes(&TicTacToe);
        Ok(PosInstance { id, value, deadline, game_id, game, btc_open, grace, keys, outcomes })
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

    /// The contract output's tree: `revoke`, `settle`, `absent_1..=M`,
    /// `exhibit_5..=M` for tic-tac-toe (D37 — the terminal-claim hole's
    /// fix; chess has no exhibit family, D42), and `equiv_d` for every
    /// depth (D39, D43 — the player-equivocation exhibit, one leaf per
    /// depth: two full state-key signatures over different regions).
    pub fn tree(&self, ctx: &CommitCtx, tables: &[EpochTable]) -> Result<TapTree> {
        let mut leaves = vec![ctx.revoke_leaf(), lngap_contract::leaves::settle_leaf(ctx, self.deadline)];
        for d in 1..=self.max_depth() {
            leaves.push(graph::absent_leaf(ctx, &format!("absent_{d}"), mover_at(d).other(), self.claim_from(d)));
        }
        if let Some(from) = self.game.min_exhibit_depth() {
            for d in from..=self.max_depth() {
                let l = self.layout(d);
                leaves.push(graph::exhibit_leaf(
                    ctx,
                    &format!("exhibit_{d}"),
                    &l,
                    &tables[(d - 1) as usize],
                    &tables[d as usize],
                    self.depth_keys(d),
                    self.depth_keys(d - 1),
                    self.claim_from(d),
                ));
            }
        }
        for d in 1..=self.max_depth() {
            let pk = &self.depth_keys(d).state;
            leaves.push(graph::equiv_leaf(ctx, &format!("equiv_{d}"), pk, mover_at(d).other()));
        }
        TapTree::new(leaves)
    }

    /// The claim output's tree at depth `d`, with the counter leaf from
    /// depth 2 (D44). `tables` is the venue's epoch table registry, indexed
    /// by slot (the refutation leaf embeds the head chunks' points of slots
    /// `d - 1` and `d`).
    pub fn claim_tree(&self, ctx: &CommitCtx, d: u32, tables: &[EpochTable]) -> Result<TapTree> {
        self.claim_tree_with(ctx, d, tables, d >= 2)
    }

    /// The counter output's tree at depth `d` (D44): the depth-`d` claim
    /// tree WITHOUT a counter of its own — one level closes the question
    /// (graph.rs's module docs).
    pub fn counter_tree(&self, ctx: &CommitCtx, d: u32, tables: &[EpochTable]) -> Result<TapTree> {
        self.claim_tree_with(ctx, d, tables, false)
    }

    fn claim_tree_with(&self, ctx: &CommitCtx, d: u32, tables: &[EpochTable], counter: bool) -> Result<TapTree> {
        let l = self.layout(d);
        let (prev, table) = if d >= 2 { (Some(&tables[(d - 1) as usize]), &tables[d as usize]) } else { (None, &tables[1]) };
        graph::claim_tree(ctx, self.game, &l, prev, table, self.depth_keys(d), (d >= 2).then(|| self.depth_keys(d - 1)), &self.outcomes, counter)
    }

    /// The refutation output's tree at depth `d`.
    pub fn refuted_tree(&self, ctx: &CommitCtx, d: u32) -> Result<TapTree> {
        graph::refuted_tree(ctx, self.game, &self.layout(d), self.depth_keys(d), &self.outcomes)
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

    /// The pre-signed children of a claim-shaped output at depth `d`
    /// (labels under `base`): the refutation (its output pinned to the
    /// depth-`d` refuted tree), the claimant's timeout splits, and the
    /// mover's self-checking splits off the refuted output. Shared by the
    /// absence claims (`absent_d`) and the counters (`absent_{d+1}/counter`,
    /// D44), which are claim-shaped outputs at depth `d` under two
    /// mutually exclusive spends of the contract output.
    #[allow(clippy::too_many_arguments)]
    fn claim_children(&self, ctx: &CommitCtx, d: u32, base: &str, a_op: OutPoint, a_prev: &TxOut, a_tree: &TapTree, out: &mut Vec<PresignedTx>) -> Result<()> {
        let fee = ctx.params.presign_fee;
        let p_tree = self.refuted_tree(ctx, d)?;
        let rtx = build_spend(a_op, &Timelock::NONE, vec![TxOut { value: a_prev.value - fee, script_pubkey: p_tree.script_pubkey() }]);
        let p_op = OutPoint { txid: rtx.compute_txid(), vout: 0 };
        let p_prev = rtx.output[0].clone();
        out.push(PresignedTx::new(format!("{base}/refute"), rtx, vec![a_prev.clone()], a_tree, "refute", format!("refutation at depth {d}"))?);
        for o in &self.outcomes {
            let leaf = format!("split_{}", o.name);
            let tx = build_spend(a_op, &a_tree.leaf(&leaf)?.timelock, self.dist_outputs(ctx, o.payout, a_prev.value - fee));
            out.push(PresignedTx::new(format!("{base}/{leaf}"), tx, vec![a_prev.clone()], a_tree, &leaf, format!("timeout split at depth {d}: {}", o.name))?);
        }
        for o in &self.outcomes {
            let leaf = format!("split_{}", o.name);
            let tx = build_spend(p_op, &p_tree.leaf(&leaf)?.timelock, self.dist_outputs(ctx, o.payout, p_prev.value - fee));
            out.push(PresignedTx::new(format!("{base}/refuted/{leaf}"), tx, vec![p_prev.clone()], &p_tree, &leaf, format!("split of the refuted output at depth {d}: {}", o.name))?);
        }
        Ok(())
    }

    /// The pre-signed skeletons hanging off the contract output: `settle`,
    /// and per depth the absence claim, the refutation, the timeout splits,
    /// and the self-checking splits (labels `absent_d/…`); from depth 2 the
    /// counter off the claim output and ITS refutation and splits (labels
    /// `absent_d/counter/…`, D44 — the counter output's tree is the
    /// depth-`d - 1` claim tree without a counter); plus per TERMINAL depth
    /// the exhibit and its self-checking splits (labels `exhibit_d/…`, D37
    /// — the exhibit output's tree IS the refuted tree: the disprove
    /// family, then the splits paying R(parked terminal)). The disprove
    /// spends are the counterparty's runtime transactions.
    pub fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut, tables: &[EpochTable]) -> Result<Vec<PresignedTx>> {
        let fee = ctx.params.presign_fee;
        let mut out = Vec::new();
        let tree0 = self.tree(ctx, tables)?;
        let r = Contract::resolution(&TicTacToe, &Board::empty());
        let tx = build_spend(outpoint, &tree0.leaf("settle")?.timelock, self.dist_outputs(ctx, r.payout, self.value - fee));
        out.push(PresignedTx::new("settle", tx, vec![prevout.clone()], &tree0, "settle", format!("settle: R(s) = {}", r.name))?);
        for d in 1..=self.max_depth() {
            let a_tree = self.claim_tree(ctx, d, tables)?;
            let name = format!("absent_{d}");
            let tx = build_spend(outpoint, &tree0.leaf(&name)?.timelock, vec![TxOut { value: self.value - fee, script_pubkey: a_tree.script_pubkey() }]);
            let a_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
            let a_prev = tx.output[0].clone();
            out.push(PresignedTx::new(name.clone(), tx, vec![prevout.clone()], &tree0, &name, format!("absence claim at depth {d}"))?);
            self.claim_children(ctx, d, &name, a_op, &a_prev, &a_tree, &mut out)?;
            if d >= 2 {
                // the counter (D44): the mover's thin claim one depth back,
                // its output the depth-(d-1) claim tree (no counter of its
                // own), with that depth's refutation and splits pre-signed
                let c_tree = self.counter_tree(ctx, d - 1, tables)?;
                let cname = format!("{name}/counter");
                let ctx_tx = build_spend(a_op, &Timelock::NONE, vec![TxOut { value: a_prev.value - fee, script_pubkey: c_tree.script_pubkey() }]);
                let c_op = OutPoint { txid: ctx_tx.compute_txid(), vout: 0 };
                let c_prev = ctx_tx.output[0].clone();
                out.push(PresignedTx::new(cname.clone(), ctx_tx, vec![a_prev.clone()], &a_tree, "counter", format!("counter off the depth-{d} claim: no move at depth {}", d - 1))?);
                self.claim_children(ctx, d - 1, &cname, c_op, &c_prev, &c_tree, &mut out)?;
            }
        }
        // the terminal exhibits (D37): `exhibit_d` spends the contract
        // output to the refuted tree of depth `d` (the disprove family
        // guards the exhibited move's legality; the splits pay R(parked
        // terminal) — the winner's unilateral terminal claim). Ttt only:
        // chess has no exhibit family (D42).
        if let Some(from) = self.game.min_exhibit_depth() {
            for d in from..=self.max_depth() {
            let e_tree = self.refuted_tree(ctx, d)?;
            let name = format!("exhibit_{d}");
            let tx = build_spend(outpoint, &tree0.leaf(&name)?.timelock, vec![TxOut { value: self.value - fee, script_pubkey: e_tree.script_pubkey() }]);
            let e_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
            let e_prev = tx.output[0].clone();
            out.push(PresignedTx::new(name.clone(), tx, vec![prevout.clone()], &tree0, &name, format!("terminal exhibit at depth {d}"))?);
            for o in &self.outcomes {
                let leaf = format!("split_{}", o.name);
                let tx = build_spend(e_op, &e_tree.leaf(&leaf)?.timelock, self.dist_outputs(ctx, o.payout, e_prev.value - fee));
                out.push(PresignedTx::new(format!("{name}/{leaf}"), tx, vec![e_prev.clone()], &e_tree, &leaf, format!("exhibit split at depth {d}: {}", o.name))?);
            }
            }
        }
        // the player-equivocation leaves (D39, plan step 6; D43's per-depth
        // form): the exhibit of BOTH signatures of the depth-`d` mover's
        // state key over two different signed regions — possible only if
        // the mover double-signed at that depth — pays the exhibitor (the
        // non-mover) the pot. The proof is self-authenticating (no venue
        // data, no timelock); the skeleton is the graph's standard 2-of-2
        // pre-sign with the payout pinned to the victim, so any holder of
        // the two signatures (a watchtower, say) can broadcast it. One leaf
        // per depth (the per-bit family collapsed with the WOTS key).
        for d in 1..=self.max_depth() {
            let exhibitor = mover_at(d).other();
            let name = format!("equiv_{d}");
            let tx = build_spend(
                outpoint,
                &tree0.leaf(&name)?.timelock,
                vec![TxOut { value: self.value - fee, script_pubkey: ctx.key(exhibitor).payout_spk.clone() }],
            );
            out.push(PresignedTx::new(
                name.clone(),
                tx,
                vec![prevout.clone()],
                &tree0,
                &name,
                format!("player equivocation at depth {d}: the mover forfeits"),
            )?);
        }
        Ok(out)
    }
}
