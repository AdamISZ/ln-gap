//! The wired PoS absence-claim instance (POS_FACTCHAIN_PLAN.md step 4b):
//! the per-depth key sets derived in the party keystores' label discipline
//! and exchanged at the draft, and the pre-signed graph over the D34/D35
//! leaf family.
//!
//! Per depth `d` (the mover's move `d`, due at `t0 + d·ell`, D55):
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
//! From D50 the refuted tree also carries `not_timely`: depth `d`'s
//! member flag points, counted against the majority threshold. The
//! instance holds the venue's [`Registry`] for this contract, pinned at
//! open (D51, D53, D55): per depth the shared content table (the refute
//! leaves' constants), every member's proposer point and flag point. The
//! claim windows are median-time-past times (D55): `claim_from(d)` is the
//! move's due time plus the margin.
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
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsParams, WotsPublic};
use lngap_lamport::PublicKey;
use lngap_tictactoe::{Board, TicTacToe};

use crate::graph;
use crate::roster::Registry;
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
    /// D57: the share commitments ride in [`PosInstance::bj`].
    Blackjack,
}

impl Game {
    /// Bytes the per-depth mover state key signs (D43: the Winternitz
    /// message): tic-tac-toe's 3 state bytes; chess's state||move (42).
    pub fn state_bytes(self) -> u32 {
        match self {
            Game::Ttt => 3,
            Game::Chess => 42,
            Game::Blackjack => 44,
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
            Game::Chess | Game::Blackjack => None,
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
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
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

/// A game's clock (D55): move `d` is due at `t0 + d·ell`; its claim is
/// valid from the due time plus `margin`. All unix seconds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct GameClock {
    pub t0: u32,
    pub ell: u32,
    pub margin: u32,
}

/// A PoS absence-claim game instance: the tuple both parties build after
/// the key exchange.
#[derive(Clone, Debug)]
pub struct PosInstance {
    pub id: u32,
    /// The contract output's value `V`: both stakes and both dispute
    /// deposits.
    pub value: Amount,
    /// Each side's dispute deposit `D` (D56): inside `V`, returned to its
    /// owner by cooperative settlement (and by `settle`, where nobody
    /// disputed), paid to the winner of any on-chain dispute with the rest
    /// of `V` — the loser pays the dispute's costs.
    pub deposit: Amount,
    /// The contract's `settle` deadline: a unix time (D55; a median-time-
    /// past CLTV), after every depth's claim window.
    pub deadline: u32,
    pub game_id: u16,
    /// The game whose disprove family and authorship mapping the graph
    /// runs (graph.rs's dispatch).
    pub game: Game,
    /// The game's clock (D55): move `d` is due at `t0 + d·ell` (unix
    /// seconds), judged by the venue's members on their clocks.
    pub t0: u32,
    /// Seconds per move.
    pub ell: u32,
    /// The claim margin `m` (D54): a depth-`d` claim is valid from
    /// `deadline(d) + margin` against median-time-past.
    pub margin: u32,
    /// Index `d - 1`.
    pub keys: Vec<PosDepthKeys>,
    pub outcomes: Vec<Outcome>,
    /// The venue's registry for THIS contract as pinned at open (D51, D53,
    /// D55): per depth the shared content table (the refute leaves'
    /// constants), every member's proposer point (the refute leaves'
    /// proposer fragment) and flag point (the `not_timely` leaf's, D50),
    /// and the flag threshold (the majority, D50 amended).
    pub registry: Registry,
    /// Blackjack's share commitments, both sides', pinned at open (D57).
    pub bj: Option<lngap_blackjack::Commitments>,
}

impl PosInstance {
    #[allow(clippy::too_many_arguments)]
    pub fn new(id: u32, value: Amount, deadline: u32, game_id: u16, game: Game, clock: GameClock, keys: Vec<PosDepthKeys>, registry: Registry) -> Result<PosInstance> {
        ensure!(!keys.is_empty(), "no depths");
        ensure!(registry.contract == id, "the registry is contract {}'s, not {id}'s", registry.contract);
        ensure!(registry.max_depth() as usize >= keys.len(), "the registry covers depths 0..={} but the game has {} depths", registry.max_depth(), keys.len());
        ensure!(clock.t0 >= lngap_btc::tx::LOCK_TIME_THRESHOLD, "t0 {} is not a unix time", clock.t0);
        let GameClock { t0, ell, margin } = clock;
        let last_claim = t0 + keys.len() as u32 * ell + margin;
        ensure!(deadline > last_claim, "the settle deadline {deadline} must follow the last claim time {last_claim}");
        ensure!(1 <= registry.threshold && registry.threshold as usize <= registry.n(), "flag threshold {} must be within 1..={}", registry.threshold, registry.n());
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
        Ok(PosInstance { id, value, deposit: Amount::ZERO, deadline, game_id, game, t0, ell, margin, keys, outcomes, registry, bj: None })
    }

    /// Give each side a dispute deposit `d` inside the contract value
    /// (D56). The value must hold both deposits and a positive stake.
    pub fn with_deposit(mut self, d: Amount) -> Result<PosInstance> {
        ensure!(self.value > d * 2, "the contract value {} must exceed both deposits of {}", self.value, d);
        self.deposit = d;
        Ok(self)
    }

    /// Pin blackjack's share commitments (D57): the disprove leaves and the
    /// venue's registered check read them.
    pub fn with_commitments(mut self, c: lngap_blackjack::Commitments) -> Result<PosInstance> {
        ensure!(self.game == Game::Blackjack, "share commitments are blackjack's");
        self.bj = Some(c);
        Ok(self)
    }

    /// Both stakes together: the value less both deposits.
    pub fn stakes(&self) -> Amount {
        self.value - self.deposit * 2
    }

    /// A cooperative settlement's balances for `payout` (D56): the stakes
    /// follow the result, each deposit returns to its owner. The channel
    /// layer's fold uses this; an on-chain dispute instead pays the winner
    /// the whole output.
    pub fn cooperative_payout(&self, payout: Payout) -> [Amount; 2] {
        let [u, h] = payout.dist(self.stakes());
        [u + self.deposit, h + self.deposit]
    }

    pub fn max_depth(&self) -> u32 {
        self.keys.len() as u32
    }

    /// When move `d` is due (unix seconds): the members flag `(c, d)` if
    /// they hold no signed entry for it by then.
    pub fn due(&self, d: u32) -> u32 {
        self.t0 + d * self.ell
    }

    /// The time (unix seconds, against median-time-past) from which a
    /// depth-`d` claim may be made: the move's due time plus the margin.
    /// A transaction with this lock is final once MTP passes it (BIP113).
    pub fn claim_from(&self, d: u32) -> u32 {
        self.due(d) + self.margin
    }

    /// The venue-side authorship check for this contract (D55): an entry
    /// for depth `d` is sealable iff it carries the depth-`d` mover's
    /// state-key signature over its head's signed region (the same message
    /// the contract's authorship fragment checks). Registered with the
    /// venue; honest members seal nothing else.
    pub fn authorship(&self) -> crate::Authorship {
        let keys: Vec<WotsPublic> = self.keys.iter().map(|k| k.state.clone()).collect();
        let game = self.game;
        let bj = self.bj.clone();
        std::sync::Arc::new(move |d: u32, entry: &[u8]| {
            let Some(pk) = d.checked_sub(1).and_then(|i| keys.get(i as usize)) else { return false };
            if game == Game::Blackjack {
                return bj.as_ref().is_some_and(|c| crate::blackjack::entry_ok(pk, c, d, entry));
            }
            let head = lngap_factchain::entry_head(entry);
            let (msg, sigs) = match game {
                Game::Ttt => match lngap_factchain::slot::SlotEntry::decode(entry) {
                    Some(e) => (crate::ttt::auth_message(&head), e.sigs),
                    None => return false,
                },
                // the signature only, never the state's well-formedness (a
                // malformed signed entry is the mover's, judged by the
                // contract's chess_malformed leaf, D45): 48 content bytes,
                // then the 20-byte elements
                Game::Chess => {
                    if entry.len() < 48 || !(entry.len() - 48).is_multiple_of(20) {
                        return false;
                    }
                    let sigs: Vec<[u8; 20]> = entry[48..].chunks(20).map(|c| c.try_into().expect("20 bytes")).collect();
                    (crate::chess::auth_message(&head), sigs)
                }
                Game::Blackjack => unreachable!("handled above"),
            };
            crate::refute::check_entry_sig(pk, &msg, &sigs)
        })
    }

    /// The clock the instance was built with.
    pub fn clock(&self) -> GameClock {
        GameClock { t0: self.t0, ell: self.ell, margin: self.margin }
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
    pub fn tree(&self, ctx: &CommitCtx) -> Result<TapTree> {
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
                    self.registry.table(d - 1),
                    self.registry.table(d),
                    self.depth_keys(d),
                    self.depth_keys(d - 1),
                    self.claim_from(d),
                    self.registry.proposers(d),
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
    /// depth 2 (D44). The refutation leaf embeds the head chunks' points
    /// of the registry's shared tables for depths `d - 1` and `d`, and
    /// depth `d`'s member proposer points (D53).
    pub fn claim_tree(&self, ctx: &CommitCtx, d: u32) -> Result<TapTree> {
        self.claim_tree_with(ctx, d, d >= 2)
    }

    /// The counter output's tree at depth `d` (D44): the depth-`d` claim
    /// tree WITHOUT a counter of its own — one level closes the question
    /// (graph.rs's module docs).
    pub fn counter_tree(&self, ctx: &CommitCtx, d: u32) -> Result<TapTree> {
        self.claim_tree_with(ctx, d, false)
    }

    fn claim_tree_with(&self, ctx: &CommitCtx, d: u32, counter: bool) -> Result<TapTree> {
        let l = self.layout(d);
        let (prev, table) = if d >= 2 { (Some(self.registry.table(d - 1)), self.registry.table(d)) } else { (None, self.registry.table(1)) };
        graph::claim_tree(ctx, self.game, &l, prev, table, self.depth_keys(d), (d >= 2).then(|| self.depth_keys(d - 1)), &self.outcomes, counter, self.registry.proposers(d))
    }

    /// The refutation output's tree at depth `d`: the disprove family, the
    /// `not_timely` leaf over depth `d`'s flag points (D50), the checked
    /// splits. (The tic-tac-toe exhibit output's tree is this tree too, so
    /// a late terminal exhibit dies the same way.)
    pub fn refuted_tree(&self, ctx: &CommitCtx, d: u32) -> Result<TapTree> {
        graph::refuted_tree(ctx, self.game, &self.layout(d), self.depth_keys(d), &self.outcomes, self.registry.flags(d), self.registry.threshold, self.bj.as_ref())
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
    pub fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>> {
        let fee = ctx.params.presign_fee;
        let mut out = Vec::new();
        let tree0 = self.tree(ctx)?;
        // settle's resolution: tic-tac-toe's and chess's R(initial); for
        // blackjack a refund (D57: the draw)
        let r = match self.game {
            Game::Blackjack => self.outcomes.iter().find(|o| o.code == 2).cloned().expect("the draw outcome"),
            _ => Contract::resolution(&TicTacToe, &Board::empty()),
        };
        // settle is the no-dispute fallback: each deposit returns to its
        // owner (D56), the stakes (less the fee, shared) follow R
        let [su, sh] = r.payout.dist(self.stakes() - fee);
        let settle_outs: Vec<TxOut> = [(su + self.deposit, Role::User), (sh + self.deposit, Role::Hub)]
            .into_iter()
            .filter(|(a, _)| *a >= ctx.params.dust)
            .map(|(a, r)| TxOut { value: a, script_pubkey: ctx.key(r).payout_spk.clone() })
            .collect();
        let tx = build_spend(outpoint, &tree0.leaf("settle")?.timelock, settle_outs);
        out.push(PresignedTx::new("settle", tx, vec![prevout.clone()], &tree0, "settle", format!("settle: R(s) = {}", r.name))?);
        for d in 1..=self.max_depth() {
            let a_tree = self.claim_tree(ctx, d)?;
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
                let c_tree = self.counter_tree(ctx, d - 1)?;
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

/// A PoS game as a channel contract output (the channel's commitments carry
/// it; its pre-signed graph is signed for both commitment versions). The
/// tree and graph are the instance's own: its claim leaves already read
/// the commitment's broadcaster (`to_self_delay`) and its tree carries the
/// commitment's revoke leaf, so a revoked commitment's contract output is
/// swept by the penalty.
impl lngap_channel::ContractOutput for PosInstance {
    fn id(&self) -> u32 {
        self.id
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn value(&self) -> Amount {
        self.value
    }
    fn tree(&self, ctx: &CommitCtx) -> Result<TapTree> {
        PosInstance::tree(self, ctx)
    }
    fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>> {
        PosInstance::graph(self, ctx, outpoint, prevout)
    }
}
