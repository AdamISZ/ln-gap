//! One channel (user vs hub), one fact-chain miner, one game of chess
//! played on the fact chain and settled with the stall graph
//! (`lngap-chess-fc`, docs/DECISIONS.md D28). The user is White and moves
//! at odd depths. As in `game_world`, the world mines one Bitcoin block
//! and one fact-chain block per step; the brains publish moves into their
//! slots and react to the venue by queueing stall proofs and lie exhibits.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, ensure, Result};
use bitcoin::Amount;
use lngap_channel::Role;
use lngap_chess::certificate::mechanical_successor;
use lngap_chess::Move;
use lngap_chess_fc::{registry, ChessEntry, ChessFc, ChessFcParams, ChessState, SIGNED_BITS};
use lngap_contract::claim::words_from_bytes;
use lngap_contract::instance::key_label;
use lngap_contract::Contract;
use lngap_factchain::sig::{levels_for, CommitTree};
use lngap_factchain::{ChainClient, Miner};
use lngap_n4bit::{hash_claim, Digest};
use lngap_names::ServedData;
use lngap_party::draft::{downcast, Change};
use lngap_party::{ChangeCtx, ClaimKind, MoveCtx, QueuedClaim};
use tracing::info;

use crate::{init_log, Harness};

pub const STAKE: Amount = Amount::from_sat(50_000);
pub const RESERVE: Amount = Amount::from_sat(15_000);
pub const ID_CHESS: u32 = 31;
pub const CHESS_ID: u16 = 2;
/// Header slots the claims cover: the game must end before this slot.
pub const W_MAX: usize = 20;

/// A party's game plan and scripted misbehaviour.
#[derive(Clone, Debug, Default)]
pub struct ChessBrain {
    /// Moves in UCI, in the order of this party's turns.
    pub moves: Vec<&'static str>,
    /// Do not publish the move at this depth.
    pub stall_at: Option<u32>,
    /// Publish this illegal move at this depth, with the state it would
    /// mechanically produce.
    pub illegal_at: Option<(u32, &'static str)>,
    /// After publishing my illegal move, prove a stall once the opponent's
    /// slot passes.
    pub claim_own_illegal: bool,
    /// Do not exhibit the opponent's illegal move (wait for its stall proof).
    pub no_exhibit: bool,
    /// Exhibit the opponent's legal move at this depth as a lie.
    pub frame_at: Option<u32>,
    /// Do not publish at this depth, but prove a stall with the move I
    /// meant to publish (the slot is empty).
    pub fabricate_at: Option<u32>,
    /// Refuse the cooperative fold at the end.
    pub refuse_fold: bool,
    /// Never react on the venue.
    pub passive: bool,
    /// Publish the (legal) move at this depth with one garbage preimage in
    /// place of a signed bit's.
    pub garbage_sig_at: Option<u32>,
    /// Exhibit the opponent's soundly signed entry at this depth as
    /// garbage-signed (a baseless signature exhibit).
    pub fabricate_sig_at: Option<u32>,
}

#[derive(Clone, Debug)]
pub struct Published {
    pub entry: ChessEntry,
    pub bytes: Vec<u8>,
    pub signed: bool,
    /// The legal successor, if the move was legal and signed.
    pub state: Option<ChessState>,
}

pub struct ChessWorld {
    pub h: Harness,
    pub miner: Miner,
    pub fc: ChainClient,
    pub checkpoint: [u8; 20],
    pub fc_open: u32,
    pub btc_open: u32,
    pub store: ServedData,
    pub program: ChessFc,
    pub brains: [ChessBrain; 2],
    /// The depth after which the hub resigns and the parties fold.
    pub resign_after: u32,
    pub depth: u32,
    pub state: ChessState,
    pub published: HashMap<u32, Published>,
    pending: Option<Published>,
    result: Arc<Mutex<Option<[Amount; 2]>>>,
    refuse: Arc<Mutex<[bool; 2]>>,
    pub escalated: bool,
    fold_rejected: bool,
    pub log: Vec<String>,
    venue_commits: [Vec<Vec<[Digest; 2]>>; 2],
}

impl ChessWorld {
    pub fn new(label: &str, brains: [ChessBrain; 2], resign_after: u32) -> Result<ChessWorld> {
        init_log();
        let store = ServedData::default();
        let h = Harness::new(label, registry(store.clone()))?;
        let g = lngap_factchain::genesis();
        let checkpoint = g.header.digest();
        let miner = Miner::new(checkpoint, 0);
        let fc = ChainClient::from_checkpoint(0, checkpoint);
        let btc_open = h.height();
        let program = ChessFc::new(ChessFcParams { game_id: CHESS_ID, checkpoint, w_max: W_MAX }, store.clone());
        let mut w = ChessWorld {
            h,
            miner,
            fc,
            checkpoint,
            fc_open: 0,
            btc_open,
            store,
            program,
            brains,
            resign_after,
            depth: 0,
            state: ChessState::initial(),
            published: HashMap::new(),
            pending: None,
            result: Arc::new(Mutex::new(None)),
            refuse: Arc::new(Mutex::new([false; 2])),
            escalated: false,
            fold_rejected: false,
            log: Vec::new(),
            venue_commits: [vec![], vec![]],
        };
        *w.refuse.lock().unwrap() = [w.brains[0].refuse_fold, w.brains[1].refuse_fold];
        w.install_policies();
        // the venue keys come first: each role's signature exhibit pins the
        // other's commitment tree roots, constants of the pre-signed graph
        w.make_venue_keys()?;
        w.open_game()?;
        Ok(w)
    }

    fn say(&mut self, s: String) {
        info!(world = "chess", "{s}");
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
    pub fn party_txs(&self) -> Vec<String> {
        self.h.seen.iter().filter(|s| s.by.is_some()).map(|s| s.role.clone()).collect()
    }
    pub fn contract_txs(&self) -> Vec<String> {
        self.party_txs().into_iter().filter(|r| !r.starts_with("claim_to_")).collect()
    }
    fn venue_label(d: u32) -> String {
        key_label(ID_CHESS, 0, d, "venue")
    }
    fn make_venue_keys(&mut self) -> Result<()> {
        for r in Role::BOTH {
            let mut commits = Vec::new();
            for d in 1..W_MAX as u32 {
                let label = Self::venue_label(d);
                let ks = self.h.party(r).keystore();
                ks.generate(&label, SIGNED_BITS)?;
                commits.push(ks.commit_with(&label, |p| hash_claim(p))?);
            }
            self.venue_commits[r.idx()] = commits;
        }
        // serve each role's commitment tree roots at the depths it moves
        let levels = levels_for(2 * SIGNED_BITS);
        for r in Role::BOTH {
            let roots: Vec<Option<Digest>> = (0..W_MAX).map(|d| (d >= 1 && ChessFc::mover_at(d as u32) == r).then(|| CommitTree::new(&self.venue_commits[r.idx()][d - 1], levels).root())).collect();
            ChessFc::put_roots(&self.store, CHESS_ID, r, &roots);
        }
        Ok(())
    }

    fn install_policies(&mut self) {
        let checkpoint = self.checkpoint;
        for r in Role::BOTH {
            let refuse = self.refuse.clone();
            let result = self.result.clone();
            let party = self.h.party(r);
            party.set_change_policy(Box::new(move |ctx: &ChangeCtx| match ctx.change {
                Change::Open { program, stakes, .. } => {
                    let p = program.strip_prefix("chess-fc:").ok_or_else(|| anyhow!("unknown program"))?;
                    let params: ChessFcParams = serde_json::from_str(p)?;
                    ensure!(params.checkpoint == checkpoint && params.game_id == CHESS_ID && params.w_max == W_MAX, "game terms do not match my view of the venue");
                    ensure!(stakes[0] == STAKE + RESERVE && stakes[1] == STAKE + RESERVE, "stakes must be symmetric");
                    Ok(())
                }
                Change::Fold { id, dist } => {
                    ensure!(*id == ID_CHESS, "unknown contract");
                    ensure!(!refuse.lock().unwrap()[r.idx()], "I refuse to fold");
                    let agreed = result.lock().unwrap().ok_or_else(|| anyhow!("the game is not over"))?;
                    ensure!(*dist == agreed, "fold does not match the venue's result");
                    Ok(())
                }
                _ => lngap_party::default_change_policy(ctx),
            }));
            let result = self.result.clone();
            let refuse = self.refuse.clone();
            party.set_fold_policy(ID_CHESS, Box::new(move |_ctx: &MoveCtx| {
                if refuse.lock().unwrap()[r.idx()] {
                    return None;
                }
                *result.lock().unwrap()
            }));
        }
    }

    fn open_game(&mut self) -> Result<()> {
        let name = lngap_contract::Program::name(&self.program).to_string();
        let deadline = self.btc_open + W_MAX as u32 + 60;
        let msgs = self.h.user.open_contract_with_deadline(ID_CHESS, &name, [STAKE + RESERVE, STAKE + RESERVE], deadline)?;
        self.h.bus(msgs)?;
        ensure!(self.contracts() == 1, "chess contract not opened");
        let n = self.h.user.channel.record(self.h.user.channel.current_seq()).map(|r| r.graph.len()).unwrap_or(0);
        self.say(format!("chess game {CHESS_ID} opened: stakes {} + {} each, deadline {deadline}, {n} pre-signed transactions", STAKE, RESERVE));
        Ok(())
    }

    fn next_slot(&self) -> u32 {
        self.fc_height() + 1 - self.fc_open
    }
    fn headers(&self) -> Vec<[u8; lngap_factchain::HEADER_BYTES]> {
        self.fc.chain_headers().iter().map(|h| h.0).collect()
    }
    /// The state before move `d`.
    fn state_before(&self, d: u32) -> Result<ChessState> {
        if d == 1 {
            return Ok(ChessState::initial());
        }
        let p = self.published.get(&(d - 1)).ok_or_else(|| anyhow!("no published move {}", d - 1))?;
        p.state.clone().ok_or_else(|| anyhow!("move {} was illegal", d - 1))
    }
    fn sign(&mut self, r: Role, d: u32, state: &ChessState) -> Result<Vec<[u8; 20]>> {
        let bits = ChessEntry::signed_bits(state);
        Ok(self.h.party(r).keystore().reveal_bits(&Self::venue_label(d), &bits)?.preimages)
    }

    fn publish_step(&mut self) -> Result<()> {
        if self.escalated || self.depth >= self.resign_after {
            return Ok(());
        }
        let d = self.next_slot();
        if d != self.depth + 1 || d as usize >= W_MAX - 1 {
            return Ok(());
        }
        let r = ChessFc::mover_at(d);
        let brain = self.brains[r.idx()].clone();
        if brain.stall_at == Some(d) {
            self.say(format!("{r} STALLS: does not publish move {d}"));
            return Ok(());
        }
        if brain.fabricate_at == Some(d) {
            self.say(format!("{r} does not publish move {d} (will prove a stall with it anyway)"));
            return Ok(());
        }
        let (mv, claimed, legal) = match brain.illegal_at {
            Some((k, uci)) if k == d => {
                let mv = Move::parse(uci).unwrap();
                let mut pos = mechanical_successor(&self.state.pos, mv);
                pos.fullmove = 0;
                self.say(format!("{r} publishes an ILLEGAL move {d}: {uci}"));
                (mv, ChessState { pos, mv, depth: d as u8 }, false)
            }
            _ => {
                let Some(uci) = brain.moves.get((d as usize - 1) / 2) else {
                    self.say(format!("{r} has no move {d} scripted"));
                    return Ok(());
                };
                let mv = Move::parse(uci).unwrap();
                let new = self.program.transition(&self.state, &mv, r).map_err(|e| anyhow!("{r}'s scripted move {d} ({uci}) is illegal: {e}"))?;
                self.say(format!("{r} publishes move {d}: {uci}"));
                (mv, new, true)
            }
        };
        let _ = mv;
        let mut sigs = self.sign(r, d, &claimed)?;
        if brain.garbage_sig_at == Some(d) {
            sigs[7] = [0xEE; 20];
            self.say(format!("{r} publishes move {d} with a GARBAGE preimage for signed bit 7"));
        }
        let entry = self.program.entry(&claimed, sigs);
        let bytes = entry.encode();
        self.pending = Some(Published { entry, bytes, signed: true, state: legal.then_some(claimed) });
        Ok(())
    }

    fn mine_slot(&mut self) -> Result<()> {
        let d = self.next_slot();
        let published = self.pending.take();
        let bytes = published.as_ref().map(|p| p.bytes.clone()).unwrap_or_default();
        self.miner.submit(bytes.clone());
        let block = self.miner.mine_next().expect("mine");
        self.fc.verify_and_append(&block).map_err(|e| anyhow!(e))?;
        let Some(mut p) = published else {
            if (d as usize) < W_MAX - 1 && !self.escalated && self.depth < self.resign_after {
                self.say(format!("slot {d} mined EMPTY"));
            }
            return Ok(());
        };
        let mover = ChessFc::mover_at(d);
        let decoded = ChessEntry::decode(&bytes)?;
        ensure!(decoded.mover == mover.idx() as u8 && decoded.depth == d as u8);
        p.signed = decoded.check_sigs(&self.venue_commits[mover.idx()][d as usize - 1]);
        if !p.signed {
            p.state = None;
        }
        if let Some(s) = &p.state {
            self.state = s.clone();
            self.depth = d;
        }
        let what = match &p.state {
            Some(s) => s.pos.to_fen(),
            None => "illegal".into(),
        };
        self.published.insert(d, p);
        self.say(format!("slot {d} mined with {mover}'s move ({what})"));
        if self.depth == self.resign_after {
            let dist = [STAKE + STAKE + RESERVE, RESERVE];
            *self.result.lock().unwrap() = Some(dist);
            self.say(format!("the hub resigns after move {}: fold user {} / hub {}", self.depth, dist[0], dist[1]));
        }
        Ok(())
    }

    fn react_step(&mut self) -> Result<()> {
        if self.escalated {
            return Ok(());
        }
        let last_slot = self.fc_height() - self.fc_open;
        for r in Role::BOTH {
            let brain = self.brains[r.idx()].clone();
            if brain.passive {
                continue;
            }
            let other = r.other();
            if self.depth >= self.resign_after {
                if self.fold_rejected && ChessFc::mover_at(self.depth) == r && last_slot >= self.depth + 1 {
                    let d = self.depth;
                    self.say(format!("{r}: the fold was refused; proving on-chain that {other} has no move after {d}"));
                    return self.queue_stall(r, d, None);
                }
                continue;
            }
            if let Some(d) = brain.fabricate_at {
                if last_slot >= d + 1 && ChessFc::mover_at(d) == r && self.depth == d - 1 {
                    let uci = brain.moves[(d as usize - 1) / 2];
                    self.say(format!("{r} proves a stall with move {d} ({uci}) although it never published it"));
                    return self.queue_stall(r, d, Some(uci));
                }
            }
            if let (true, Some((d, _))) = (brain.claim_own_illegal, brain.illegal_at) {
                if ChessFc::mover_at(d) == r && self.published.contains_key(&d) && last_slot >= d + 1 {
                    self.say(format!("{r} proves a stall with its ILLEGAL move {d}: {other} published nothing at {}", d + 1));
                    return self.queue_stall(r, d, None);
                }
            }
            if let Some(k) = brain.frame_at {
                if ChessFc::mover_at(k) == other && self.published.get(&k).is_some_and(|p| p.state.is_some()) {
                    self.say(format!("{r} FRAMES {other}'s legal move {k} as a lie"));
                    return self.queue_lie(r, k);
                }
            }
            if let Some(k) = brain.fabricate_sig_at {
                if ChessFc::mover_at(k) == other && self.published.get(&k).is_some_and(|p| p.signed) {
                    self.say(format!("{r} exhibits {other}'s soundly signed entry {k} as GARBAGE-SIGNED"));
                    return self.queue_sig(r, k, true);
                }
            }
            let k = self.depth + 1;
            if k >= 2 && ChessFc::mover_at(k) == other && last_slot >= k {
                match self.published.get(&k) {
                    Some(p) if p.state.is_none() && p.signed => {
                        if !brain.no_exhibit {
                            self.say(format!("{r}: {other}'s move {k} is illegal; exhibiting it"));
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
                        self.say(format!("{r}: {other} published nothing at slot {k}; proving a stall at depth {}", k - 1));
                        return self.queue_stall(r, k - 1, None);
                    }
                }
            }
        }
        Ok(())
    }

    fn queue_stall(&mut self, r: Role, d: u32, fabricated: Option<&str>) -> Result<()> {
        let prior = self.state_before(d)?;
        let claimed = match fabricated {
            Some(uci) => self.program.transition(&prior, &Move::parse(uci).unwrap(), r).map_err(|e| anyhow!("{e}"))?,
            None => self.published.get(&d).ok_or_else(|| anyhow!("no published move {d}"))?.entry.state.clone(),
        };
        let e = words_from_bytes(&claimed.to_e());
        let e2 = words_from_bytes(&prior.to_e());
        let data = self.program.stall_claim_for(r).data(d as usize, &self.headers(), &e, &e2);
        self.store.put(&ChessFc::stall_key(CHESS_ID, r), data);
        self.escalated = true;
        let q = QueuedClaim { kind: ClaimKind::Stall, depth: d, prior: prior.to_bits(), mv: self.program.move_bits(&claimed.mv), new: Some(claimed.to_bits()), code: None };
        self.h.party(r).queue_claim(ID_CHESS, q);
        Ok(())
    }

    fn queue_lie(&mut self, r: Role, k: u32) -> Result<()> {
        let prior = self.state_before(k)?;
        let claimed = self.published.get(&k).ok_or_else(|| anyhow!("no published move {k}"))?.entry.state.clone();
        let e = words_from_bytes(&claimed.to_e());
        let e2 = words_from_bytes(&prior.to_e());
        let data = self.program.lie_claim_for(r).data(k as usize, &self.headers(), &e, &e2);
        self.store.put(&ChessFc::lie_key(CHESS_ID, r), data);
        self.escalated = true;
        let q = QueuedClaim { kind: ClaimKind::Lie, depth: k, prior: prior.to_bits(), mv: self.program.move_bits(&claimed.mv), new: Some(claimed.to_bits()), code: None };
        self.h.party(r).queue_claim(ID_CHESS, q);
        Ok(())
    }

    /// `r` exhibits the opponent's entry `k` as garbage-signed: serves the
    /// claim's data (the first bit whose preimage opens nothing, or, when
    /// `fabricated`, bit 0 of a sound entry) and queues it with `r`'s
    /// winning code.
    fn queue_sig(&mut self, r: Role, k: u32, fabricated: bool) -> Result<()> {
        let other = r.other();
        let p = self.published.get(&k).ok_or_else(|| anyhow!("no published entry {k}"))?.clone();
        let head_bits = ChessEntry::signed_bits(&p.entry.state);
        let commits = self.venue_commits[other.idx()][k as usize - 1].clone();
        let sig = self.program.sig_claim_for(r).ok_or_else(|| anyhow!("no commitment roots served"))?;
        let (i, b) = if fabricated { (0, head_bits[0]) } else { sig.find_garbage(&p.bytes, &head_bits, &commits).ok_or_else(|| anyhow!("entry {k} is soundly signed"))? };
        let data = sig.data(k as usize, i, b, &self.headers(), &p.bytes, &commits);
        self.store.put(&ChessFc::sig_key(CHESS_ID, r), data);
        self.escalated = true;
        let prior = self.state_before(k)?;
        let code = if r == Role::User { 0 } else { 1 };
        let q = QueuedClaim { kind: ClaimKind::Sig, depth: k, prior: prior.to_bits(), mv: vec![false; lngap_chess_fc::MOVE_BITS], new: None, code: Some(code) };
        self.h.party(r).queue_claim(ID_CHESS, q);
        Ok(())
    }

    pub fn step(&mut self) -> Result<u32> {
        self.h.rt.mine(1)?;
        let h = self.h.height();
        let txs = self.h.rt.block_txs(h)?;
        self.h.deliver(h, &txs)?;
        self.react_step()?;
        self.publish_step()?;
        self.mine_slot()?;
        self.h.settle_offchain()?;
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
    pub fn step_until(&mut self, max: u32, mut pred: impl FnMut(&ChessWorld) -> bool) -> Result<u32> {
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
    /// Silence an unused-field warning for the instance helper's twin.
    pub fn instance(&self) -> lngap_contract::ContractInstance {
        downcast(self.h.user.channel.current_state().contract(ID_CHESS).expect("chess contract")).clone()
    }
}
