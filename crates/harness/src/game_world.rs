//! One channel (user vs hub), one fact-chain miner, one game of tic-tac-toe
//! played on the fact chain (docs/planning/VENUE.md; `lngap-tictactoe-fc`).
//!
//! The world mines one Bitcoin block and one fact-chain block per step. The
//! fact-chain block mined at step `d` after the game opens is slot `d`: the
//! block move `d` must sit in. Each party's *brain* reads the venue and
//! either publishes its next move into the coming slot, or, when the
//! opponent's slot passed without a valid move, queues a timeout claim in
//! the channel contract (a party reaction; the harness only relays what it
//! sees). Scenario faults live in the brains: stall, publish an invalid
//! move, refuse the fold, ignore a valid move (a spurious timeout claim),
//! or claim a slot never published (fabricated inclusion).

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, ensure, Result};
use bitcoin::Amount;
use lngap_channel::Role;
use lngap_contract::instance::key_label;
use lngap_contract::{Claim, Contract};
use lngap_factchain::slot::SlotEntry;
use lngap_factchain::sig::{levels_for, CommitTree};
use lngap_factchain::{ChainClient, Miner};
use lngap_lamport::{bits_to_uint, uint_to_bits, Reveal};
use lngap_names::ServedData;
use lngap_party::draft::{downcast, Change};
use lngap_party::{ChangeCtx, ClaimKind, MoveCtx, QueuedClaim};
use lngap_n4bit::{hash_claim, Digest};
use lngap_tictactoe::{Board, OPEN};
use lngap_tictactoe_fc::{registry, TicTacToeFc, TttFcParams};
use tracing::info;

use crate::{init_log, Harness};

/// Each side's stake: the winner takes both.
pub const STAKE: Amount = Amount::from_sat(50_000);
/// Each side's fee reserve: returned on a cooperative fold, forfeited to
/// the winner on any on-chain resolution (docs/planning/VENUE.md §2).
pub const RESERVE: Amount = Amount::from_sat(15_000);
pub const ID_GAME: u32 = 30;
pub const GAME_ID: u16 = 1;
pub const GRACE: u32 = 1;

/// A party's game plan and scripted misbehaviour. Honest brains leave the faults unset.
#[derive(Clone, Debug, Default)]
pub struct Brain {
    /// Cells to play, in the order of this party's turns.
    pub moves: Vec<u8>,
    /// Do not publish the move at this depth (a stall).
    pub stall_at: Option<u32>,
    /// Publish an occupied cell at this depth (an invalid move).
    pub invalid_at: Option<u32>,
    /// Do not publish the move at this depth, but claim it on-chain with
    /// fabricated inclusion data (the slot's block is empty).
    pub fabricate_at: Option<u32>,
    /// Treat the opponent's valid move at this depth as absent: a spurious
    /// timeout claim at the depth before.
    pub ignore_at: Option<u32>,
    /// Refuse the cooperative fold at the end of the game.
    pub refuse_fold: bool,
    /// Never claim on-chain (whatever the opponent does).
    pub passive: bool,
    /// Publish the move at this depth with garbage in place of the
    /// signature (the preimages).
    pub garbage_at: Option<u32>,
    /// Answer a timeout claim with a garbage-signed move of mine.
    pub refute_with_garbage: bool,
    /// Stall graphs: exhibit the opponent's soundly signed entry at this
    /// depth as garbage-signed (a baseless signature exhibit).
    pub fabricate_sig_at: Option<u32>,
    /// Stall graphs: after publishing my invalid move, prove a stall against
    /// the opponent once its slot passes (a liar's stall proof).
    pub claim_own_invalid: bool,
    /// Stall graphs: do not exhibit the opponent's invalid move (wait for
    /// its stall proof instead).
    pub no_exhibit: bool,
    /// Stall graphs: exhibit the opponent's valid move at this depth as a
    /// lie (a baseless exhibit).
    pub frame_at: Option<u32>,
}

/// A move published on the venue.
#[derive(Clone, Debug)]
pub struct Published {
    pub entry: SlotEntry,
    pub bytes: Vec<u8>,
    /// The board the mover claimed to leave.
    pub claimed: Board,
    /// Do the entry's preimages open the mover's pinned key?
    pub signed: bool,
    /// The board after it (None if the move was invalid or unsigned).
    pub board: Option<Board>,
}

pub struct GameWorld {
    pub h: Harness,
    pub miner: Miner,
    pub fc: ChainClient,
    pub checkpoint: [u8; 20],
    pub fc_open: u32,
    pub btc_open: u32,
    pub store: ServedData,
    pub program: TicTacToeFc,
    pub brains: [Brain; 2],
    /// Valid moves on the venue so far, and the board they produce.
    pub depth: u32,
    pub board: Board,
    pub published: HashMap<u32, Published>,
    /// What each mined slot's block carries (empty for an empty block).
    pub blocks: HashMap<u32, Vec<u8>>,
    /// The entry for the coming slot.
    pending: Option<Published>,
    /// The agreed cooperative distribution once the game is over (shared
    /// with the parties' fold policies).
    result: Arc<Mutex<Option<[Amount; 2]>>>,
    /// Which brains refuse the fold (shared with the change policies).
    refuse: Arc<Mutex<[bool; 2]>>,
    /// Set once a claim is queued: the venue game is over.
    pub escalated: bool,
    fold_rejected: bool,
    pub log: Vec<String>,
    /// The stall graph (D28) instead of the star graph.
    pub stall: bool,
    /// Stall graphs: each role's per-depth venue keys' claim-native
    /// commitments (index `[role][d - 1]`), what anyone checks a published
    /// entry's signature against.
    venue_commits: [Vec<Vec<[Digest; 2]>>; 2],
}

impl GameWorld {
    /// A funded channel, a fact chain at genesis, and the game contract
    /// opened at the empty board with the given brains.
    pub fn new(label: &str, brains: [Brain; 2]) -> Result<GameWorld> {
        Self::new_with(label, brains, false)
    }
    /// The same on the stall graph (D28).
    pub fn new_stall(label: &str, brains: [Brain; 2]) -> Result<GameWorld> {
        Self::new_with(label, brains, true)
    }
    fn new_with(label: &str, brains: [Brain; 2], stall: bool) -> Result<GameWorld> {
        init_log();
        let store = ServedData::default();
        let h = Harness::new(label, registry(store.clone()))?;
        let g = lngap_factchain::genesis();
        let checkpoint = g.header.digest();
        let miner = Miner::new(checkpoint, 0);
        let fc = ChainClient::from_checkpoint(0, checkpoint);
        let btc_open = h.height();
        let program = TicTacToeFc::new(TttFcParams { game_id: GAME_ID, checkpoint, btc_open, grace: GRACE, stall, w_max: 10 }, store.clone());
        let mut w = GameWorld {
            h,
            miner,
            fc,
            checkpoint,
            fc_open: 0,
            btc_open,
            store,
            program,
            brains,
            depth: 0,
            board: Board::empty(),
            published: HashMap::new(),
            blocks: HashMap::new(),
            pending: None,
            result: Arc::new(Mutex::new(None)),
            refuse: Arc::new(Mutex::new([false; 2])),
            escalated: false,
            fold_rejected: false,
            log: Vec::new(),
            stall,
            venue_commits: [vec![], vec![]],
        };
        *w.refuse.lock().unwrap() = [w.brains[0].refuse_fold, w.brains[1].refuse_fold];
        w.install_policies();
        if stall {
            // the venue keys come first: each role's signature exhibit pins
            // the other's commitment tree roots, constants of the graph
            w.make_venue_keys()?;
        }
        w.open_game()?;
        Ok(w)
    }

    /// Stall graphs: the Bitcoin-side keys are per role, so each party's
    /// per-depth venue signing keys are separate. The harness generates
    /// them in each party's key store and publishes their claim-native
    /// commitments to everyone (in a deployment, exchanged in the draft).
    fn make_venue_keys(&mut self) -> Result<()> {
        let n = lngap_tictactoe::TicTacToe.n_state_bits();
        for r in Role::BOTH {
            let mut commits = Vec::new();
            for d in 1..=9u32 {
                let label = Self::venue_label(d);
                let ks = self.h.party(r).keystore();
                ks.generate(&label, n)?;
                commits.push(ks.commit_with(&label, |p| hash_claim(p))?);
            }
            self.venue_commits[r.idx()] = commits;
        }
        // serve each role's commitment tree roots at the depths it moves
        let levels = levels_for(2 * n);
        for r in Role::BOTH {
            let roots: Vec<Option<Digest>> = (0..10).map(|d| (d >= 1 && TicTacToeFc::mover_at(d as u32) == r).then(|| CommitTree::new(&self.venue_commits[r.idx()][d - 1], levels).root())).collect();
            TicTacToeFc::put_roots(&self.store, GAME_ID, r, &roots);
        }
        Ok(())
    }
    fn venue_label(d: u32) -> String {
        key_label(ID_GAME, 0, d, "venue")
    }

    fn say(&mut self, s: String) {
        info!(world = "game", "{s}");
        self.log.push(format!("[world @ {} / slot {}] {s}", self.h.height(), self.fc.tip_height() - self.fc_open));
    }

    pub fn height(&self) -> u32 {
        self.h.height()
    }
    pub fn fc_height(&self) -> u32 {
        self.fc.tip_height()
    }
    pub fn contracts(&self) -> usize {
        self.h.user.channel.current_state().contracts.len()
    }
    pub fn balances(&self) -> [Amount; 2] {
        self.h.user.channel.current_state().balances
    }
    /// Roles of the transactions the parties broadcast, in order.
    pub fn party_txs(&self) -> Vec<String> {
        self.h.seen.iter().filter(|s| s.by.is_some()).map(|s| s.role.clone()).collect()
    }
    /// Those that touch the contract (not the commitment's balance sweeps).
    pub fn contract_txs(&self) -> Vec<String> {
        self.party_txs().into_iter().filter(|r| !r.starts_with("claim_to_")).collect()
    }
    fn keys_seq(&self) -> u64 {
        downcast(self.h.user.channel.current_state().contract(ID_GAME).expect("game contract")).keys_seq
    }
    fn instance(&self) -> lngap_contract::ContractInstance {
        downcast(self.h.user.channel.current_state().contract(ID_GAME).expect("game contract")).clone()
    }

    // ----- policies -----

    fn install_policies(&mut self) {
        let checkpoint = self.checkpoint;
        let btc_open = self.btc_open;
        let refuse = self.refuse.clone();
        let result = self.result.clone();
        for r in Role::BOTH {
            let refuse = refuse.clone();
            let result = result.clone();
            let party = self.h.party(r);
            party.set_change_policy(Box::new(move |ctx: &ChangeCtx| match ctx.change {
                Change::Open { program, stakes, .. } => {
                    let p = program.strip_prefix("ttt-fc:").ok_or_else(|| anyhow!("unknown program"))?;
                    let params: TttFcParams = serde_json::from_str(p)?;
                    ensure!(params.checkpoint == checkpoint && params.btc_open == btc_open && params.grace == GRACE && params.game_id == GAME_ID, "game terms do not match my view of the venue");
                    ensure!(stakes[0] == STAKE + RESERVE && stakes[1] == STAKE + RESERVE, "stakes must be symmetric");
                    Ok(())
                }
                Change::Fold { id, dist } => {
                    ensure!(*id == ID_GAME, "unknown contract");
                    ensure!(!refuse.lock().unwrap()[r.idx()], "I refuse to fold");
                    let agreed = result.lock().unwrap().ok_or_else(|| anyhow!("the game is not over"))?;
                    ensure!(*dist == agreed, "fold does not match the venue's result");
                    Ok(())
                }
                _ => lngap_party::default_change_policy(ctx),
            }));
            let result = self.result.clone();
            let refuse = self.refuse.clone();
            party.set_fold_policy(ID_GAME, Box::new(move |_ctx: &MoveCtx| {
                if refuse.lock().unwrap()[r.idx()] {
                    return None;
                }
                *result.lock().unwrap()
            }));
        }
    }

    /// Off `C'_d` a party answers a claim with its own next move: the move
    /// it published on the venue from that very state.
    fn install_move_policy(&mut self, r: Role) {
        let with_garbage = self.brains[r.idx()].refute_with_garbage;
        let mine: Vec<(Vec<bool>, Vec<bool>)> = self
            .published
            .iter()
            .filter(|(d, p)| TicTacToeFc::mover_at(**d) == r && (p.board.is_some() || (with_garbage && !p.signed)))
            .filter(|(d, _)| **d == 1 || self.published.get(&(*d - 1)).is_some_and(|q| q.board.is_some()))
            .map(|(d, p)| {
                let prior = if *d == 1 { Board::empty() } else { self.published[&(d - 1)].board.clone().expect("valid prior") };
                (self.program.state_bits(&prior), uint_to_bits(u32::from(p.entry.mv), 4))
            })
            .collect();
        self.h.party(r).set_move_policy(
            ID_GAME,
            Box::new(move |ctx: &MoveCtx| mine.iter().find(|(prior, _)| prior == ctx.state).map(|(_, mv)| mv.clone())),
        );
    }

    fn open_game(&mut self) -> Result<()> {
        let name = lngap_contract::Program::name(&self.program).to_string();
        let deadline = self.btc_open + 9 + 1 + GRACE + 20;
        let msgs = self.h.user.open_contract_with_deadline(ID_GAME, &name, [STAKE + RESERVE, STAKE + RESERVE], deadline)?;
        self.h.bus(msgs)?;
        ensure!(self.contracts() == 1, "game contract not opened");
        let n = self.h.user.channel.record(self.h.user.channel.current_seq()).map(|r| r.graph.len()).unwrap_or(0);
        self.say(format!("game {GAME_ID} opened: stakes {} + {} each, deadline {deadline}, {n} pre-signed transactions", STAKE, RESERVE));
        Ok(())
    }

    // ----- the venue -----

    /// The slot the next fact-chain block will be.
    fn next_slot(&self) -> u32 {
        self.fc_height() + 1 - self.fc_open
    }

    /// The mover's reveal of the state after move `d` (its own Lamport key).
    fn state_reveal(&mut self, r: Role, d: u32, new: &Board) -> Result<Reveal> {
        let seq = self.keys_seq();
        let bits = lngap_tictactoe::TicTacToe.state_bits(new);
        let label = if self.stall { Self::venue_label(d) } else { key_label(ID_GAME, seq, d, "state") };
        self.h.party(r).keystore().reveal_bits(&label, &bits)
    }
    /// The `(move, state)` word of the entry published at depth `d`, or
    /// the initial word at depth 0.
    fn head_word(&self, d: u32) -> u32 {
        if d == 0 {
            let init = self.program.stall_claim_for(Role::User).initial_e2;
            return u32::from_be_bytes(init[..4].try_into().unwrap());
        }
        let e = &self.published[&d].entry;
        SlotEntry::word1(e.mv, e.state)
    }
    fn headers(&self) -> Vec<[u8; lngap_factchain::HEADER_BYTES]> {
        self.fc.chain_headers().iter().map(|h| h.0).collect()
    }
    /// The claim data for slot `d`: the headers to it, the counterparty's
    /// block `d - 1` and my block `d` (or an entry of my choosing).
    fn slot_data(&self, d: u32, own: &[u8]) -> lngap_contract::ClaimData {
        let keys = self.instance().keys.clone();
        let commits = |k: u32| keys[k as usize - 1].state_n4.clone();
        let headers: Vec<[u8; lngap_factchain::HEADER_BYTES]> = self.fc.chain_headers().iter().map(|h| h.0).collect();
        let prev = self.blocks.get(&(d - 1)).map(|b| b.as_slice());
        self.program.slot_claim(d, commits).data(&headers[..d as usize], prev, own)
    }

    /// The brain on turn prepares the coming slot's entry.
    fn publish_step(&mut self) -> Result<()> {
        if self.escalated || self.board.status != OPEN {
            return Ok(());
        }
        let d = self.next_slot();
        if d != self.depth + 1 || d > 9 {
            return Ok(());
        }
        let r = TicTacToeFc::mover_at(d);
        let brain = self.brains[r.idx()].clone();
        if brain.stall_at == Some(d) {
            self.say(format!("{r} STALLS: does not publish move {d}"));
            return Ok(());
        }
        if brain.fabricate_at == Some(d) {
            self.say(format!("{r} does not publish move {d} (will claim it with fabricated data)"));
            return Ok(());
        }
        let my_turn_index = (d as usize - 1) / 2;
        let Some(&cell) = brain.moves.get(my_turn_index) else {
            self.say(format!("{r} has no move {d} scripted"));
            return Ok(());
        };
        let (cell, new, valid) = if brain.invalid_at == Some(d) {
            let occupied = (0..9u8).find(|c| self.board.cells[*c as usize] != 0).expect("an occupied cell");
            // the state the mover *claims*: as if the cell had been free
            let mut b = self.board.clone();
            b.cells[occupied as usize] = lngap_tictactoe::mark(r);
            b.turn = r.other();
            self.say(format!("{r} publishes an INVALID move {d}: cell {occupied} is occupied"));
            (occupied, b, false)
        } else {
            let new = self.program.transition(&self.board, &cell, r).map_err(|e| anyhow!("{r}'s scripted move {d} is invalid: {e}"))?;
            (cell, new, true)
        };
        let st_r = self.state_reveal(r, d, &new)?;
        let mut entry = self.program.entry(d, cell, &new, &st_r);
        if brain.garbage_at == Some(d) {
            entry.sigs = (0..entry.sigs.len()).map(|i| [0xEE ^ i as u8; 20]).collect();
            self.say(format!("{r} publishes move {d} with a GARBAGE signature"));
        } else if valid {
            self.say(format!("{r} publishes move {d}: cell {cell}"));
        }
        let bytes = entry.encode();
        self.pending = Some(Published { entry, bytes, claimed: new.clone(), signed: true, board: valid.then_some(new) });
        Ok(())
    }

    /// Mine the coming slot with the pending entry (or empty), let everyone
    /// verify it against the mover's pinned commitments, and serve the
    /// slot's claim data.
    fn mine_slot(&mut self) -> Result<()> {
        let d = self.next_slot();
        let published = self.pending.take();
        let bytes = published.as_ref().map(|p| p.bytes.clone()).unwrap_or_default();
        self.miner.submit(bytes.clone());
        let block = self.miner.mine_next().expect("mine");
        self.fc.verify_and_append(&block).map_err(|e| anyhow!(e))?;
        self.blocks.insert(d, bytes.clone());
        let Some(mut p) = published else {
            if d <= 9 && !self.escalated && self.board.status == OPEN {
                self.say(format!("slot {d} mined EMPTY"));
            }
            return Ok(());
        };
        // anyone verifies the entry: content, and the signature against the
        // mover's claim-native commitments (what the claim checks on-chain)
        let mover = TicTacToeFc::mover_at(d);
        let commits = if self.stall {
            self.venue_commits[mover.idx()][d as usize - 1].clone()
        } else {
            let inst = self.instance();
            let keys = inst.depth_keys(d);
            ensure!(keys.prover == mover);
            keys.state_n4.clone()
        };
        let decoded = SlotEntry::decode(&bytes).ok_or_else(|| anyhow!("undecodable entry"))?;
        ensure!(decoded.state == bits_to_uint(&self.program.state_bits(&p.claimed)) && decoded.mover == mover.idx() as u8 && decoded.depth == d as u8);
        p.signed = decoded.check_sigs(&commits);
        if !p.signed {
            p.board = None;
        }
        if !self.stall {
            // serve the slot's inclusion data (for the mover's claim at this depth)
            let data = self.slot_data(d, &bytes);
            self.store.put(&TicTacToeFc::slot_key(GAME_ID, d), data);
        }
        let valid = p.board.is_some();
        if valid {
            self.board = p.board.clone().unwrap();
            self.depth = d;
        }
        let what = if valid { self.board.render() } else if !p.signed { "UNSIGNED".into() } else { "invalid".into() };
        self.published.insert(d, p);
        if !self.stall {
            self.install_move_policy(mover);
        }
        self.say(format!("slot {d} mined with {mover}'s move ({what}); inclusion data served"));
        if valid && self.board.status != OPEN {
            let dist = match self.program.resolution(&self.board).payout {
                lngap_contract::Payout::UserAll => [STAKE + STAKE + RESERVE, RESERVE],
                lngap_contract::Payout::HubAll => [RESERVE, STAKE + STAKE + RESERVE],
                lngap_contract::Payout::Even => [STAKE + RESERVE, STAKE + RESERVE],
            };
            *self.result.lock().unwrap() = Some(dist);
            self.say(format!("game over on the venue: {} (fold user {} / hub {})", self.program.describe_state(&self.board), dist[0], dist[1]));
        }
        Ok(())
    }

    /// Serve fabricated inclusion data for a slot never published: the real
    /// headers and the entry the mover would have published.
    fn serve_fabricated(&mut self, r: Role, d: u32, cell: u8) -> Result<()> {
        let new = self.program.transition(&self.board, &cell, r).map_err(|e| anyhow!("{e}"))?;
        let st_r = self.state_reveal(r, d, &new)?;
        let entry = self.program.entry(d, cell, &new, &st_r).encode();
        let data = self.slot_data(d, &entry);
        self.store.put(&TicTacToeFc::slot_key(GAME_ID, d), data);
        self.say(format!("{r} serves FABRICATED inclusion data for slot {d} (the block is empty)"));
        Ok(())
    }

    /// A brain reacts to the venue: a timeout claim when the opponent's slot
    /// passed without a valid move (or is ignored), a result claim when the
    /// fold was refused, a claim of one's own invalid move, a fabricated claim.
    fn react_step(&mut self) -> Result<()> {
        if self.escalated {
            return Ok(());
        }
        if self.stall {
            return self.react_step_stall();
        }
        let last_slot = self.fc_height() - self.fc_open; // slots mined so far
        for r in Role::BOTH {
            let brain = self.brains[r.idx()].clone();
            if brain.passive {
                continue;
            }
            let other = r.other();
            // the game is over on the venue: only a refused fold leads on-chain
            if self.board.status != OPEN {
                if self.fold_rejected && TicTacToeFc::mover_at(self.depth) == r {
                    let d = self.depth;
                    self.say(format!("{r}: the fold was refused; claiming the result on-chain at depth {d}"));
                    return self.queue_claim(r, d, self.published[&d].entry.mv);
                }
                continue;
            }
            // a fabricated claim: my slot passed empty, I claim it anyway
            if let Some(d) = brain.fabricate_at {
                if last_slot >= d + 1 && TicTacToeFc::mover_at(d) == r && self.depth == d - 1 {
                    let cell = brain.moves[(d as usize - 1) / 2];
                    self.serve_fabricated(r, d, cell)?;
                    self.say(format!("{r} claims move {d} on-chain although it never published it"));
                    return self.queue_claim(r, d, cell);
                }
            }
            // my own invalid move, claimed as if it were valid once the opponent's slot passed
            if let Some(d) = brain.invalid_at {
                if let Some(p) = self.published.get(&d).cloned() {
                    if TicTacToeFc::mover_at(d) == r && last_slot >= d + 1 && p.board.is_none() {
                        let mv = p.entry.mv;
                        let new_bits = self.program.state_bits(&p.claimed);
                        let code = self.program.resolution(&p.claimed).code;
                        self.h.party(r).faults.cheat_move = Some(Arc::new(move |c: &Claim| Claim { prior: c.prior.clone(), mv: uint_to_bits(u32::from(mv), 4), new: new_bits.clone(), code, mover: c.mover }));
                        let honest_cell = (0..9u8).find(|c| self.board.cells[*c as usize] == 0).expect("an empty cell");
                        self.say(format!("{r} claims its INVALID move {d} on-chain as a timeout of {other}"));
                        return self.queue_claim(r, d, honest_cell);
                    }
                }
            }
            // a spurious timeout claim: the opponent's valid move k is ignored
            if let Some(k) = brain.ignore_at {
                if k >= 2 && TicTacToeFc::mover_at(k) == other && self.published.get(&k).is_some_and(|p| p.board.is_some()) {
                    self.say(format!("{r} IGNORES {other}'s valid move {k} and claims a timeout at depth {}", k - 1));
                    return self.queue_claim(r, k - 1, self.published[&(k - 1)].entry.mv);
                }
            }
            // the opponent's slot passed without a valid move
            let k = self.depth + 1;
            if k >= 2 && TicTacToeFc::mover_at(k) == other && last_slot >= k && !self.published.get(&k).is_some_and(|p| p.board.is_some()) {
                self.say(format!("{r}: {other} did not publish a valid move {k}; claiming a timeout at depth {}", k - 1));
                return self.queue_claim(r, k - 1, self.published[&(k - 1)].entry.mv);
            }
        }
        Ok(())
    }

    /// Queue `r`'s claim at depth `d` (its own move `d`) in the channel contract.
    fn queue_claim(&mut self, r: Role, d: u32, cell: u8) -> Result<()> {
        let prior = self.board_before(d)?;
        let prior_bits = self.program.state_bits(&prior);
        self.escalated = true;
        self.h.party(r).queue_claim(ID_GAME, QueuedClaim::star(d, prior_bits, uint_to_bits(u32::from(cell), 4)));
        Ok(())
    }

    /// The board move `d` leaves from (the empty board at depth 1).
    fn board_before(&self, d: u32) -> Result<Board> {
        if d == 1 {
            return Ok(Board::empty());
        }
        let p = self.published.get(&(d - 1)).ok_or_else(|| anyhow!("no published move {}", d - 1))?;
        p.board.clone().ok_or_else(|| anyhow!("move {} was invalid", d - 1))
    }

    // ----- the stall graph -----

    /// Brains on the stall graph: a stall proof when the opponent's slot
    /// passed empty (or is ignored, or the game is over and the fold was
    /// refused), a lie exhibit when its move was invalid (or is framed), a
    /// stall proof of one's own invalid or fabricated move.
    fn react_step_stall(&mut self) -> Result<()> {
        let last_slot = self.fc_height() - self.fc_open;
        for r in Role::BOTH {
            let brain = self.brains[r.idx()].clone();
            if brain.passive {
                continue;
            }
            let other = r.other();
            if self.board.status != OPEN {
                if self.fold_rejected && TicTacToeFc::mover_at(self.depth) == r && last_slot >= self.depth + 1 {
                    let d = self.depth;
                    self.say(format!("{r}: the fold was refused; proving on-chain that {other} has no move after {d}"));
                    return self.queue_stall(r, d, None);
                }
                continue;
            }
            if let Some(d) = brain.fabricate_at {
                if last_slot >= d + 1 && TicTacToeFc::mover_at(d) == r && self.depth == d - 1 {
                    let cell = brain.moves[(d as usize - 1) / 2];
                    self.say(format!("{r} proves a stall with move {d} although it never published it (the slot is empty)"));
                    return self.queue_stall(r, d, Some(cell));
                }
            }
            if let (true, Some(d)) = (brain.claim_own_invalid, brain.invalid_at) {
                if TicTacToeFc::mover_at(d) == r && self.published.contains_key(&d) && last_slot >= d + 1 {
                    self.say(format!("{r} proves a stall with its INVALID move {d}: {other} published nothing at {}", d + 1));
                    return self.queue_stall(r, d, None);
                }
            }
            if let Some(k) = brain.frame_at {
                if TicTacToeFc::mover_at(k) == other && self.published.get(&k).is_some_and(|p| p.board.is_some()) {
                    self.say(format!("{r} FRAMES {other}'s valid move {k} as a lie"));
                    return self.queue_lie(r, k);
                }
            }
            if let Some(k) = brain.ignore_at {
                if k >= 2 && TicTacToeFc::mover_at(k) == other && self.published.get(&k).is_some_and(|p| p.board.is_some()) && last_slot >= k {
                    self.say(format!("{r} IGNORES {other}'s valid move {k} and proves a stall at depth {}", k - 1));
                    return self.queue_stall(r, k - 1, None);
                }
            }
            if let Some(k) = brain.fabricate_sig_at {
                if TicTacToeFc::mover_at(k) == other && self.published.get(&k).is_some_and(|p| p.signed) {
                    self.say(format!("{r} exhibits {other}'s soundly signed entry {k} as GARBAGE-SIGNED"));
                    return self.queue_sig(r, k, true);
                }
            }
            let k = self.depth + 1;
            if k >= 2 && TicTacToeFc::mover_at(k) == other && last_slot >= k {
                match self.published.get(&k) {
                    Some(p) if p.board.is_none() && p.signed => {
                        if !brain.no_exhibit {
                            self.say(format!("{r}: {other}'s move {k} is invalid; exhibiting it"));
                            return self.queue_lie(r, k);
                        }
                    }
                    Some(p) if !p.signed => {
                        if !brain.no_exhibit {
                            self.say(format!("{r}: {other}'s entry {k} is garbage-signed; exhibiting it"));
                            return self.queue_sig(r, k, false);
                        }
                    }
                    Some(_) => {}
                    None => {
                        if last_slot >= k {
                            self.say(format!("{r}: {other} published nothing at slot {k}; proving a stall at depth {}", k - 1));
                            return self.queue_stall(r, k - 1, None);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// `r` proves a stall with its move `d` (published, or `fabricated`
    /// with this cell): serves the claim's data and queues it.
    fn queue_stall(&mut self, r: Role, d: u32, fabricated: Option<u8>) -> Result<()> {
        let prior = self.board_before(d)?;
        let (mv, new, e) = match fabricated {
            Some(cell) => {
                let new = self.program.transition(&prior, &cell, r).map_err(|e| anyhow!("{e}"))?;
                let e = SlotEntry::word1(cell, bits_to_uint(&self.program.state_bits(&new)));
                (cell, new, e)
            }
            None => {
                let p = self.published.get(&d).ok_or_else(|| anyhow!("no published move {d}"))?;
                (p.entry.mv, p.claimed.clone(), SlotEntry::word1(p.entry.mv, p.entry.state))
            }
        };
        let e2 = self.head_word(d - 1);
        let data = self.program.stall_claim_for(r).data(d as usize, &self.headers(), &[e], &[e2]);
        self.store.put(&TicTacToeFc::stall_key(GAME_ID, r), data);
        self.escalated = true;
        let q = QueuedClaim { kind: ClaimKind::Stall, depth: d, prior: self.program.state_bits(&prior), mv: uint_to_bits(u32::from(mv), 4), new: Some(self.program.state_bits(&new)), code: None };
        self.h.party(r).queue_claim(ID_GAME, q);
        Ok(())
    }

    /// `r` exhibits the opponent's move `k` as a lie: serves the claim's
    /// data and queues it.
    fn queue_lie(&mut self, r: Role, k: u32) -> Result<()> {
        let prior = self.board_before(k)?;
        let p = self.published.get(&k).ok_or_else(|| anyhow!("no published move {k}"))?.clone();
        let e = SlotEntry::word1(p.entry.mv, p.entry.state);
        let e2 = self.head_word(k - 1);
        let data = self.program.lie_claim_for(r).data(k as usize, &self.headers(), &[e], &[e2]);
        self.store.put(&TicTacToeFc::lie_key(GAME_ID, r), data);
        self.escalated = true;
        let q = QueuedClaim { kind: ClaimKind::Lie, depth: k, prior: self.program.state_bits(&prior), mv: uint_to_bits(u32::from(p.entry.mv), 4), new: Some(self.program.state_bits(&p.claimed)), code: None };
        self.h.party(r).queue_claim(ID_GAME, q);
        Ok(())
    }

    /// `r` exhibits the opponent's entry `k` as garbage-signed (stall
    /// graphs): serves the claim's data (the first bit whose preimage opens
    /// nothing, or, when `fabricated`, bit 0 of a sound entry) and queues it
    /// with `r`'s winning code.
    fn queue_sig(&mut self, r: Role, k: u32, fabricated: bool) -> Result<()> {
        let other = r.other();
        let p = self.published.get(&k).ok_or_else(|| anyhow!("no published entry {k}"))?.clone();
        let n = lngap_tictactoe::TicTacToe.n_state_bits();
        let head_bits: Vec<bool> = (0..n).map(|i| (p.entry.state >> i) & 1 == 1).collect();
        let commits = self.venue_commits[other.idx()][k as usize - 1].clone();
        let sig = self.program.sig_claim_for(r).ok_or_else(|| anyhow!("no commitment roots served"))?;
        let (i, b) = if fabricated { (0, head_bits[0]) } else { sig.find_garbage(&p.bytes, &head_bits, &commits).ok_or_else(|| anyhow!("entry {k} is soundly signed"))? };
        let data = sig.data(k as usize, i, b, &self.headers(), &p.bytes, &commits);
        self.store.put(&TicTacToeFc::sig_key(GAME_ID, r), data);
        self.escalated = true;
        let prior = self.board_before(k)?;
        let code = if r == Role::User { lngap_tictactoe::TicTacToe::USER_WINS } else { lngap_tictactoe::TicTacToe::HUB_WINS };
        let q = QueuedClaim { kind: ClaimKind::Sig, depth: k, prior: self.program.state_bits(&prior), mv: vec![false; 4], new: None, code: Some(code) };
        self.h.party(r).queue_claim(ID_GAME, q);
        Ok(())
    }

    // ----- clock -----

    pub fn step(&mut self) -> Result<u32> {
        self.h.rt.mine(1)?;
        let h = self.h.height();
        let txs = self.h.rt.block_txs(h)?;
        self.h.deliver(h, &txs)?;
        self.react_step()?;
        self.publish_step()?;
        self.mine_slot()?;
        self.h.settle_offchain()?;
        // a refused fold shows up as a rejection in the proposer's log
        if !self.fold_rejected && self.h.user.narrative().iter().chain(self.h.hub.narrative().iter()).any(|l| l.contains("rejected by counterparty: I refuse to fold")) {
            self.fold_rejected = true;
        }
        Ok(h)
    }
    pub fn steps(&mut self, n: u32) -> Result<()> {
        for _ in 0..n {
            self.step()?;
        }
        Ok(())
    }
    pub fn step_until(&mut self, max: u32, mut pred: impl FnMut(&GameWorld) -> bool) -> Result<u32> {
        for i in 0..max {
            if pred(self) {
                return Ok(i);
            }
            self.step()?;
        }
        ensure!(pred(self), "condition not met within {max} blocks");
        Ok(max)
    }

    pub fn narrative(&self) -> String {
        let mut s = String::new();
        s.push_str("--- venue ---\n");
        s.push_str(&self.log.join("\n"));
        s.push('\n');
        s.push_str(&self.h.narrative());
        s
    }
}
