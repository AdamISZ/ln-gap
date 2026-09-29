//! One party of the session: a Poon-Dryja channel with the counterparty,
//! and hand after hand of blackjack inside it (CHANNEL_DEMO_PLAN.md).
//!
//! The channel opens once: each party funds its half from the node's
//! wallet, the commitments of state 0 are signed over the shared
//! directory's message bus, both sign their funding inputs, the player
//! broadcasts. A hand is a contract of its own (contract id = hand number,
//! with its own per-depth keys, share commitments and venue registry). It
//! enters the channel by an update, is played on the venue, and leaves by
//! the next update with the agreed result: no chain transaction. A party
//! that cannot get an agreed result force-closes: its commitment confirms
//! with the hand's contract output on it, and the dispute graph is that
//! commitment version's (claims, refutations, disproves, splits as before).
//!
//! The Player drives from its page; the House is an autopilot (reveal when
//! due, play the dealer's rule, settle its wins, accept honest results,
//! answer disputes) unless its console sets a cheat.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::{BufRead, Write};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use anyhow::{anyhow, bail, ensure, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut, Txid};
use lngap_blackjack as bj;
use lngap_blackjack::{action, phase, status, Commitments, Share, State, K as POSITIONS};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::chain::Chain;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::protocol::{funding_tree, ChainEvent, ChannelParty, Closing, Envelope, Policy};
use lngap_channel::wire::WireEnvelope;
use lngap_channel::{ChannelParams, ChannelState, ContractOutput, PartyKeys, PresignedTx, Role};
use lngap_contract::Payout;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_pos::blackjack;
use lngap_pos::graph::{not_timely_witness, proposer_witness};
use lngap_pos::instance::{self, Game, GameClock, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNKS, HEAD_CHUNK_START};
use lngap_pos::{Registry, SealedBlock};
use rand::SeedableRng;
use serde::Serialize;

use crate::store::*;

fn sig_bytes(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

fn outcome_name(code: u8) -> &'static str {
    match code {
        0 => "UserWins",
        1 => "HubWins",
        _ => "Draw",
    }
}

fn outcome_ui(code: u8) -> &'static str {
    match code {
        0 => "the Player wins",
        1 => "the House wins",
        _ => "a push (refund)",
    }
}

fn status_ui(st: u8) -> &'static str {
    match st {
        status::PLAYER => "the Player wins",
        status::HOUSE => "the House wins",
        status::PUSH => "push",
        _ => "open",
    }
}

fn action_ui(a: u8) -> &'static str {
    match a {
        action::DEAL => "DEAL",
        action::REVEAL => "REVEAL",
        action::HIT => "HIT",
        action::STAND => "STAND",
        action::ACK => "ACK",
        _ => "?",
    }
}

fn payout_of(st: u8) -> Option<Payout> {
    match st {
        status::PLAYER => Some(Payout::UserAll),
        status::HOUSE => Some(Payout::HubAll),
        status::PUSH => Some(Payout::Even),
        _ => None,
    }
}

fn sat(a: Amount) -> String {
    let s = a.to_sat().to_string();
    let mut out = String::new();
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Mode {
    Honest,
    WrongCard,
    DrawAt17,
    StandOn16,
    Withhold,
}

impl Mode {
    fn parse(s: &str) -> Option<Mode> {
        Some(match s {
            "honest" => Mode::Honest,
            "wrongcard" => Mode::WrongCard,
            "drawat17" => Mode::DrawAt17,
            "standon16" => Mode::StandOn16,
            "withhold" => Mode::Withhold,
            _ => return None,
        })
    }
}

/// Where the current hand is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum HandPhase {
    /// Keys, shares and the venue's registry being exchanged.
    Negotiating,
    /// The channel update adding the hand's contract is in flight.
    Opening,
    Playing,
    /// Folded: the channel update removing it with the agreed result.
    Settled,
    /// On chain after a force-close.
    Disputed,
}

/// What this party's channel policy agrees to: adding the hand `id` with
/// `contribution` from each side, and removing it with `payout`.
#[derive(Default)]
struct Agree {
    open: Option<(u32, Amount)>,
    fold: Option<(u32, [Amount; 2])>,
}

#[derive(Clone, Debug)]
struct Live {
    height: u32,
    op: OutPoint,
    prev: TxOut,
}

struct Decoded {
    state: State,
    word0_ok: bool,
    signed: bool,
    strings: Option<Vec<Vec<u8>>>,
}

fn whose(r: Role) -> u8 {
    r.idx() as u8
}

pub struct Player {
    me: Role,
    store: Store,
    rt: Arc<Regtest>,
    vparams: VenueParams,
    params: ChannelParams,
    chan: ChannelParty,
    agree: Arc<Mutex<Agree>>,
    ks: KeyStore,
    /// Every hand's instance, by id (the bus resolves contract ids here).
    instances: BTreeMap<u32, Arc<PosInstance>>,
    bus_seen: BTreeSet<String>,
    scanned: u32,
    /// The commitment that closed the channel: (seq, broadcaster, height).
    closed: Option<(u64, Role, u32)>,
    /// Finished hands, for the page.
    results: Vec<String>,
    log: Vec<String>,
    mode: Mode,
    /// The house plays its own game moves (reveals, the dealer's forced
    /// draws) and settles hands it won.
    autopilot: bool,
    /// ... and also takes every dispute step by itself (off by default:
    /// the presenter clicks them, "if the house refutes...").
    auto_disputes: bool,
    done: BTreeSet<String>,
    /// Autopilot actions that failed, and when (retried after 10 s).
    failed: BTreeMap<String, u32>,
    /// When I proposed settling the current hand.
    settle_sent: Option<u32>,
    // ----- the current hand -----
    hand: u32,
    hand_phase: Option<HandPhase>,
    inst: Option<Arc<PosInstance>>,
    commits: Option<Commitments>,
    shares: Vec<Share>,
    strings: BTreeMap<(u8, usize), Vec<u8>>,
    their_state_keys: HashMap<u32, WotsPublic>,
    graph: Vec<PresignedTx>,
    blocks: BTreeMap<u32, SealedBlock>,
    seen_seals: BTreeSet<String>,
    flags: BTreeMap<u32, Vec<Option<SecretKey>>>,
    pending: Option<(u32, String, usize, u32)>,
    state: State,
    depth: u32,
    bad_slots: BTreeMap<u32, String>,
    late_slots: BTreeSet<u32>,
    rogue_slots: BTreeSet<u32>,
    live: BTreeMap<String, Live>,
    spent: HashMap<OutPoint, (Txid, u32)>,
    reveals: BTreeMap<String, WotsSig>,
}

fn wait_for<T>(mut f: impl FnMut() -> Result<Option<T>>) -> Result<T> {
    loop {
        if let Some(v) = f()? {
            return Ok(v);
        }
        std::thread::sleep(Duration::from_millis(300));
    }
}

impl Player {
    pub fn role(&self) -> Role {
        self.me
    }

    pub fn publish_web_port(&self, port: u16) -> Result<()> {
        self.store.write(&Store::web(self.me), &serde_json::json!({ "port": port }))
    }

    fn say(&mut self, s: String) {
        let s = ui(&s);
        println!("  {s}");
        self.log.push(s);
    }

    fn inst(&self) -> Result<&PosInstance> {
        self.inst.as_deref().ok_or_else(|| anyhow!("no hand in play"))
    }

    fn height(&self) -> u32 {
        self.rt.height().unwrap_or(0)
    }

    fn due(&self, d: u32) -> u32 {
        self.inst.as_ref().map(|i| i.due(d)).unwrap_or(0)
    }

    fn rel(&self, t: u32) -> i64 {
        let t0 = self.inst.as_ref().map(|i| i.t0).unwrap_or(t);
        i64::from(t) - i64::from(t0)
    }

    fn skel(&self, label: &str) -> Result<&PresignedTx> {
        self.graph.iter().find(|p| p.label == label).ok_or_else(|| anyhow!("no skeleton {label} (the channel must be force-closed first)"))
    }

    fn channel_open(&self) -> bool {
        self.chan.closing.is_none()
    }

    /// The hand's contract is in the channel's current state.
    fn hand_in_channel(&self) -> bool {
        self.chan.current_state().contract(self.hand).is_some()
    }

    // ============ setup: the channel ============

    pub fn open(dir: PathBuf, me: Role, max_depth: u32) -> Result<Player> {
        let store = Store::new(dir);
        let who = side(me);
        let them = side(me.other());
        println!("{who}: waiting for the venue's node...");
        let vparams: VenueParams = wait_for(|| store.read::<VenueParams>(Store::params()))?;
        let node: NodeInfo = wait_for(|| store.read(Store::node()))?;
        let rt = Arc::new(Regtest::attach(&PathBuf::from(node.datadir))?);
        let _ = max_depth;

        // the channel: my keys, my contribution, my offer
        let keys = PartyKeys::from_seed(me, Seed::from_label(&format!("blackjack-venue/{}", me.name())));
        let side_amt = Amount::from_sat(CHANNEL_SIDE_SAT);
        let (c_op, c_prev) = rt.fund(&keys.public().payout_spk, side_amt + Amount::from_sat(10_000))?;
        let offer = ChanOffer {
            pubs: keys.public(),
            rev: [hex::encode(keys.revocation_hash(0)), hex::encode(keys.revocation_hash(1))],
            contrib_txid: c_op.txid.to_string(),
            contrib_vout: c_op.vout,
            contrib_value: c_prev.value.to_sat(),
            contrib_spk: hex::encode(c_prev.script_pubkey.as_bytes()),
        };
        store.write(&Store::chan_offer(me), &offer)?;
        println!("{who}: channel offer published (a {} sat contribution); waiting for the {them}'s...", sat(side_amt));
        let theirs: ChanOffer = wait_for(|| store.read(&Store::chan_offer(me.other())))?;
        let coin = |o: &ChanOffer| -> Result<(OutPoint, TxOut)> { Ok((OutPoint { txid: o.contrib_txid.parse()?, vout: o.contrib_vout }, TxOut { value: Amount::from_sat(o.contrib_value), script_pubkey: ScriptBuf::from_bytes(hex::decode(&o.contrib_spk)?) })) };
        let (user_o, hub_o) = if me == Role::User { (&offer, &theirs) } else { (&theirs, &offer) };
        let contribs = [coin(user_o)?, coin(hub_o)?];
        let pubs = [user_o.pubs.clone(), hub_o.pubs.clone()];
        let params = ChannelParams { presign_fee: Amount::from_sat(FEE_SAT), ..ChannelParams::regtest(side_amt * 2) };
        let mut ftx = build_funding_tx(&contribs, funding_tree(&pubs).script_pubkey(), params.funding_amount);
        let funding = (OutPoint { txid: ftx.compute_txid(), vout: 0 }, ftx.output[0].clone());
        let rev = |o: &ChanOffer| -> Result<[[u8; 20]; 2]> {
            let h = |s: &str| -> Result<[u8; 20]> { hex::decode(s)?.try_into().map_err(|_| anyhow!("a revocation hash is 20 bytes")) };
            Ok([h(&o.rev[0])?, h(&o.rev[1])?])
        };
        let agree: Arc<Mutex<Agree>> = Arc::default();
        let a = agree.clone();
        let policy: Policy = Box::new(move |old: &ChannelState, new: &ChannelState| {
            let a = a.lock().unwrap();
            let olds: Vec<u32> = old.contracts.iter().map(|c| c.id()).collect();
            let news: Vec<u32> = new.contracts.iter().map(|c| c.id()).collect();
            let added: Vec<u32> = news.iter().filter(|i| !olds.contains(i)).copied().collect();
            let removed: Vec<u32> = olds.iter().filter(|i| !news.contains(i)).copied().collect();
            ensure!(added.len() + removed.len() <= 1, "one hand at a time");
            if let Some(id) = added.first() {
                let (aid, c) = a.open.ok_or_else(|| anyhow!("I agreed to no hand"))?;
                ensure!(aid == *id, "I agreed to hand {aid}, not {id}");
                ensure!(new.balances == [old.balances[0].checked_sub(c).ok_or_else(|| anyhow!("balance"))?, old.balances[1].checked_sub(c).ok_or_else(|| anyhow!("balance"))?], "each side puts in its stake and deposit");
            } else if let Some(id) = removed.first() {
                let (fid, pay) = a.fold.ok_or_else(|| anyhow!("hand {id} has no agreed result on my side"))?;
                ensure!(fid == *id, "my agreed result is hand {fid}'s");
                ensure!(new.balances == [old.balances[0] + pay[0], old.balances[1] + pay[1]], "the payout is not the result I see");
            } else {
                ensure!(new.balances == old.balances, "no change without a hand");
            }
            Ok(())
        });
        let initial = ChannelState { seq: 0, balances: [side_amt, side_amt], contracts: vec![] };
        let chain: Arc<dyn Chain> = rt.clone();
        let chan = ChannelParty::new(keys, pubs[me.other().idx()].clone(), params, funding.clone(), initial, rev(&theirs)?, chain, policy)?;
        let mut p = Player {
            me,
            store,
            rt,
            vparams,
            params,
            chan,
            agree,
            ks: KeyStore::new(Seed::from_label(&format!("blackjack-venue/{}-ks", me.name()))),
            instances: BTreeMap::new(),
            bus_seen: BTreeSet::new(),
            scanned: 0,
            closed: None,
            results: Vec::new(),
            log: Vec::new(),
            mode: Mode::Honest,
            autopilot: me == Role::Hub,
            auto_disputes: false,
            done: BTreeSet::new(),
            failed: BTreeMap::new(),
            settle_sent: None,
            hand: 0,
            hand_phase: None,
            inst: None,
            commits: None,
            shares: Vec::new(),
            strings: BTreeMap::new(),
            their_state_keys: HashMap::new(),
            graph: Vec::new(),
            blocks: BTreeMap::new(),
            seen_seals: BTreeSet::new(),
            flags: BTreeMap::new(),
            pending: None,
            state: State::initial(),
            depth: 0,
            bad_slots: BTreeMap::new(),
            late_slots: BTreeSet::new(),
            rogue_slots: BTreeSet::new(),
            live: BTreeMap::new(),
            spent: HashMap::new(),
            reveals: BTreeMap::new(),
        };
        // state 0's commitments, over the bus
        let m = p.chan.initial_commit_sigs()?;
        p.send_env(&m)?;
        wait_for(|| {
            p.bus()?;
            Ok(p.chan.ready_to_fund().then_some(()))
        })?;
        // the funding witnesses: each signs its own input
        let idx = me.idx();
        let prevouts = [contribs[0].1.clone(), contribs[1].1.clone()];
        sign_funding_input(&mut ftx, idx, &prevouts, &p.chan.keys.payout_tree(), &p.chan.keys.payout)?;
        let wit: Vec<String> = ftx.input[idx].witness.iter().map(hex::encode).collect();
        p.store.write(&Store::funding_wit(me), &wit)?;
        if me == Role::User {
            let other: Vec<String> = wait_for(|| p.store.read(&Store::funding_wit(Role::Hub)))?;
            ftx.input[1].witness = bitcoin::Witness::from_slice(&other.iter().map(hex::decode).collect::<std::result::Result<Vec<_>, _>>()?);
            let txid = p.rt.send_raw(&ftx)?;
            println!("{who}: the funding transaction {txid} is broadcast; waiting for it to confirm...");
            // (`confirmations` returns the confirming block's height)
            let h = wait_for(|| p.rt.confirmations(&txid))?;
            p.store.write(Store::funded(), &serde_json::json!({ "txid": txid.to_string(), "height": h }))?;
        }
        let f: serde_json::Value = wait_for(|| p.store.read(Store::funded()))?;
        let h = f["height"].as_u64().unwrap_or(0) as u32;
        p.scanned = h;
        p.say(format!("the channel is open: {} sat each side, funded at height {h}", sat(side_amt)));
        Ok(p)
    }

    // ============ the bus ============

    fn send_env(&self, e: &Envelope) -> Result<()> {
        let w = WireEnvelope::from_env(e)?;
        let name = format!("{}/{}.json", Store::bus(e.to), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
        self.store.write(&name, &w)
    }

    /// Handle every unread channel message; send the replies.
    fn bus(&mut self) -> Result<()> {
        for p in self.store.list(&Store::bus(self.me))? {
            let key = p.display().to_string();
            if self.bus_seen.contains(&key) {
                continue;
            }
            let Some(w) = std::fs::read_to_string(&p).ok().and_then(|s| serde_json::from_str::<WireEnvelope>(&s).ok()) else { continue };
            self.bus_seen.insert(key);
            let instances = self.instances.clone();
            let env = match w.into_env(|id| instances.get(&id).map(|i| i.clone() as Arc<dyn ContractOutput>)) {
                Ok(e) => e,
                Err(e) => {
                    self.say(format!("channel: a message I cannot read: {e:#}"));
                    continue;
                }
            };
            match self.chan.handle(env) {
                Ok(replies) => {
                    for r in replies {
                        self.send_env(&r)?;
                    }
                }
                Err(e) => self.say(format!("channel: I refused a message: {e:#}")),
            }
        }
        Ok(())
    }

    /// Propose a channel state (the counterparty's policy judges it).
    fn propose(&mut self, balances: [Amount; 2], contracts: Vec<Arc<dyn ContractOutput>>) -> Result<()> {
        let seq = self.chan.current_seq() + 1;
        let msgs = self.chan.propose(ChannelState { seq, balances, contracts })?;
        for m in &msgs {
            self.send_env(m)?;
        }
        Ok(())
    }

    // ============ hands ============

    /// Forget the previous hand's state and start hand `id`: my per-hand
    /// keys and shares, my offer.
    fn begin_hand(&mut self, id: u32) -> Result<()> {
        self.hand = id;
        self.hand_phase = Some(HandPhase::Negotiating);
        self.inst = None;
        self.commits = None;
        self.strings.clear();
        self.their_state_keys.clear();
        self.graph.clear();
        self.blocks.clear();
        self.seen_seals.clear();
        self.flags.clear();
        self.pending = None;
        self.state = State::initial();
        self.depth = 0;
        self.bad_slots.clear();
        self.late_slots.clear();
        self.rogue_slots.clear();
        self.live.clear();
        self.spent.clear();
        self.reveals.clear();
        self.done.clear();
        self.failed.clear();
        self.settle_sent = None;
        let keys = instance::gen_pos_keys(&mut self.ks, self.me, id, 1, self.vparams.max_depth, Game::Blackjack)?;
        let mut rng = rand::rngs::StdRng::from_entropy();
        self.shares = (0..POSITIONS).map(|_| Share::random(&mut rng)).collect();
        let commits = self.shares.iter().map(|s| hex::encode(s.commitment())).collect();
        self.store.write(&Store::offer(id, self.me), &Offer { keys, commits })?;
        Ok(())
    }

    /// Move the hand along: the House joins a requested hand; both build
    /// the instance once the registry, both offers and the terms are in;
    /// the Player proposes the terms and the channel update; the phase
    /// follows the channel.
    fn negotiate(&mut self) -> Result<()> {
        // the House joins a new hand
        if self.me == Role::Hub {
            if let Some(&h) = self.store.hands().iter().rev().find(|h| self.store.exists(&Store::request(**h))) {
                if h > self.hand && self.channel_open() {
                    self.begin_hand(h)?;
                    self.say(format!("hand {h}: the Player asks for a hand; my keys and share commitments are out"));
                }
            }
        }
        let h = self.hand;
        if h == 0 {
            return Ok(());
        }
        if self.inst.is_none() {
            let registry: Option<Registry> = self.store.read(&Store::registry(h))?;
            let (Some(registry), Some(user), Some(hub)) = (registry, self.store.read::<Offer>(&Store::offer(h, Role::User))?, self.store.read::<Offer>(&Store::offer(h, Role::Hub))?) else { return Ok(()) };
            if self.me == Role::User && !self.store.exists(&Store::contract(h)) {
                let t0 = unix_now() + self.vparams.start_secs;
                let deadline = t0 + (self.vparams.max_depth + 1) * self.vparams.ell + self.vparams.margin + 7 * 24 * 3600;
                let c = ContractJson { value: 2 * STAKE_SAT + 2 * self.vparams.deposit, deadline, t0, ell: self.vparams.ell, margin: self.vparams.margin, deposit: self.vparams.deposit };
                self.store.write(&Store::contract(h), &c)?;
            }
            let Some(c) = self.store.read::<ContractJson>(&Store::contract(h))? else { return Ok(()) };
            let commits = commitments(&user, &hub)?;
            let keys = instance::collect_keys(&user.keys, &hub.keys, self.vparams.max_depth)?;
            let theirs = if self.me == Role::User { &hub } else { &user };
            self.their_state_keys = theirs.keys.iter().filter_map(|(d, o)| o.state.clone().map(|k| (*d, k))).collect();
            let clock = GameClock { t0: c.t0, ell: c.ell, margin: c.margin };
            let inst = PosInstance::new(h, Amount::from_sat(c.value), c.deadline, GAME_ID, Game::Blackjack, clock, keys, registry)?.with_deposit(Amount::from_sat(c.deposit))?.with_commitments(commits.clone())?;
            let inst = Arc::new(inst);
            self.instances.insert(h, inst.clone());
            self.inst = Some(inst);
            self.commits = Some(commits);
            self.agree.lock().unwrap().open = Some((h, Amount::from_sat(STAKE_SAT + c.deposit)));
        }
        let in_chan = self.hand_in_channel();
        match self.hand_phase {
            Some(HandPhase::Negotiating) | Some(HandPhase::Opening) if in_chan => {
                self.hand_phase = Some(HandPhase::Playing);
                let b = self.chan.current_state().balances;
                self.say(format!("hand {h} is in the channel (update {}): {} sat at stake; balances Player {} / House {}. Move 1 is due in {}s", self.chan.current_seq(), sat(self.inst()?.value), sat(b[0]), sat(b[1]), i64::from(self.due(1)) - i64::from(unix_now())));
            }
            Some(HandPhase::Negotiating) if self.me == Role::User && self.store.exists(&Store::registered(h)) && self.chan.pending_seq().is_none() && self.channel_open() => {
                let inst = self.inst.clone().ok_or_else(|| anyhow!("no instance"))?;
                let c = Amount::from_sat(STAKE_SAT + self.vparams.deposit);
                let b = self.chan.current_state().balances;
                ensure!(b[0] >= c && b[1] >= c, "a side's channel balance cannot cover another hand");
                self.hand_phase = Some(HandPhase::Opening);
                self.propose([b[0] - c, b[1] - c], vec![inst as Arc<dyn ContractOutput>])?;
                self.say(format!("hand {h}: proposing the channel update that adds the hand's contract"));
            }
            Some(HandPhase::Playing) if !in_chan && self.channel_open() => {
                self.hand_phase = Some(HandPhase::Settled);
                let b = self.chan.current_state().balances;
                self.results.push(format!("hand {h}: {}", status_ui(self.state.status)));
                self.say(format!("hand {h}: {} — SETTLED in the channel (update {}, no chain transaction); balances Player {} / House {}", status_ui(self.state.status), self.chan.current_seq(), sat(b[0]), sat(b[1])));
            }
            _ => {}
        }
        self.agree_fold();
        Ok(())
    }

    /// My view's result, once the hand is over: what my policy accepts as
    /// the fold, and what my settle proposes.
    fn agree_fold(&mut self) -> Option<[Amount; 2]> {
        if self.hand_phase != Some(HandPhase::Playing) || !self.state.is_terminal() {
            return None;
        }
        let pay = self.inst().ok()?.cooperative_payout(payout_of(self.state.status)?);
        self.agree.lock().unwrap().fold = Some((self.hand, pay));
        Some(pay)
    }

    /// The winner proposes removing the hand with the agreed payout (the
    /// Player for a win or a push, the House for its wins).
    fn settle(&mut self) -> Result<()> {
        ensure!(self.hand_phase == Some(HandPhase::Playing) && self.hand_in_channel(), "no hand in the channel to settle");
        ensure!(self.state.is_terminal(), "the hand is not over");
        ensure!(self.chan.pending_seq().is_none(), "a channel update is in flight");
        let pay = self.agree_fold().ok_or_else(|| anyhow!("no agreed result"))?;
        self.settle_sent = Some(unix_now());
        let b = self.chan.current_state().balances;
        self.propose([b[0] + pay[0], b[1] + pay[1]], vec![])?;
        self.say(format!("hand {}: {} — proposing the channel update that pays it (Player +{}, House +{})", self.hand, status_ui(self.state.status), sat(pay[0]), sat(pay[1])));
        Ok(())
    }

    fn new_hand(&mut self) -> Result<()> {
        ensure!(self.me == Role::User, "the Player starts hands");
        ensure!(self.channel_open(), "the channel is closed");
        ensure!(matches!(self.hand_phase, None | Some(HandPhase::Settled)), "finish this hand first");
        let h = self.hand + 1;
        self.begin_hand(h)?;
        self.store.write(&Store::request(h), &serde_json::json!({ "hand": h }))?;
        self.say(format!("hand {h}: requested; keys and share commitments exchanged, the venue computes the hand's registry..."));
        Ok(())
    }

    fn force_close(&mut self) -> Result<()> {
        ensure!(self.channel_open(), "the channel is already closing");
        let txid = self.chan.force_close()?;
        self.say(format!("FORCE-CLOSING the channel: my commitment {} ({txid}) is broadcast; the hand's contract output appears on chain when it confirms", self.chan.current_seq()));
        Ok(())
    }

    fn close_channel(&mut self) -> Result<()> {
        ensure!(self.channel_open(), "the channel is already closing");
        ensure!(!self.hand_in_channel(), "settle the hand first");
        let msgs = self.chan.propose_close()?;
        for m in &msgs {
            self.send_env(m)?;
        }
        self.say("closing the channel cooperatively: one transaction pays both balances".into());
        Ok(())
    }

    // ============ the venue and the chain, as seen ============

    pub fn sync(&mut self) -> Result<()> {
        // the venue before the bus: a settle proposal must find the hand's
        // final seal already read (my policy judges it against my view)
        if self.inst.is_some() {
            self.venue()?;
        }
        self.agree_fold();
        self.bus()?;
        if let Err(e) = self.negotiate() {
            self.say(format!("hand {}: {e:#}", self.hand));
        }
        let h = self.height();
        while self.scanned < h {
            self.scanned += 1;
            let txs = self.rt.block_txs(self.scanned)?;
            let events = self.chan.on_block(self.scanned, &txs)?;
            for e in events {
                self.on_chain_event(e)?;
            }
            for tx in txs.iter().skip(1) {
                self.on_tx(self.scanned, tx)?;
            }
        }
        if self.autopilot {
            if let Err(e) = self.pilot() {
                self.say(format!("autopilot: {e:#}"));
            }
        }
        Ok(())
    }

    fn venue(&mut self) -> Result<()> {
        let h = self.hand;
        let mut new: Vec<BlockJson> = Vec::new();
        for p in self.store.list(&Store::seals_dir(h))? {
            let key = p.display().to_string();
            if self.seen_seals.contains(&key) {
                continue;
            }
            if let Some(b) = std::fs::read_to_string(&p).ok().and_then(|s| serde_json::from_str::<BlockJson>(&s).ok()) {
                self.seen_seals.insert(key);
                new.push(b);
            }
        }
        new.sort_by_key(|b| (b.sealed_at, b.depth));
        for b in new {
            let block = b.to_block(h)?;
            self.on_seal(&b, block)?;
        }
        for d in 1..=self.vparams.max_depth {
            if self.flags.contains_key(&d) {
                continue;
            }
            if let Some(f) = self.store.read::<FlagsJson>(&Store::flags(h, d))? {
                let f = flags_from_json(&f)?;
                let n = f.iter().filter(|x| x.is_some()).count();
                self.flags.insert(d, f);
                if matches!(self.hand_phase, Some(HandPhase::Playing) | Some(HandPhase::Disputed)) {
                    self.say(format!("venue: move {d} was due at t+{}s with no valid seal — {n} of {K} members flagged it", self.rel(self.due(d))));
                }
            }
        }
        if let Some((d, entry, to, at)) = self.pending.clone() {
            let now = unix_now();
            if self.blocks.contains_key(&d) {
                self.pending = None;
            } else if now > self.due(d) {
                self.say(format!("my move {d} was not sealed by its due time: I am stalled at {d}"));
                self.pending = None;
            } else if now >= at + self.vparams.backoff {
                let next = (to + 1) % self.vparams.n;
                self.say(format!("no seal of my move {d} from member {to} after {}s: resubmitting to member {next}", self.vparams.backoff));
                self.send(d, &entry, next)?;
            }
        }
        Ok(())
    }

    /// A commitment confirmed: the hand (if its contract is on it) is now
    /// disputed off that commitment version's graph.
    fn on_chain_event(&mut self, e: ChainEvent) -> Result<()> {
        let (seq, version, height, revoked) = match e {
            ChainEvent::LocalCommitConfirmed { seq, height } => (seq, self.me, height, false),
            ChainEvent::RemoteCommitConfirmed { seq, height } => (seq, self.me.other(), height, false),
            ChainEvent::RemoteRevokedCommitConfirmed { seq, height } => (seq, self.me.other(), height, true),
            ChainEvent::OutputSpent { .. } => return Ok(()),
        };
        self.closed = Some((seq, version, height));
        if revoked {
            self.say(format!("chain: height {height}: the {} broadcast a REVOKED commitment ({seq}) — the penalty sweeps everything on it to me", side(version)));
            return Ok(());
        }
        self.say(format!("chain: height {height}: the {}'s commitment {seq} confirmed — the channel is closed", side(version)));
        let rec = self.chan.record(seq).ok_or_else(|| anyhow!("no record of state {seq}"))?;
        self.graph = rec.graph.iter().filter(|(k, _)| k.version == version && k.contract_id == self.hand).map(|(_, p)| p.clone()).collect();
        let commit = rec.commits[version.idx()].clone();
        if let Some(c) = commit.output(lngap_channel::commit::OutputKind::Contract(self.hand)) {
            let op = commit.outpoint(c);
            let prev = commit.txout(c);
            self.live.insert("contract".into(), Live { height, op, prev: prev.clone() });
            self.hand_phase = Some(HandPhase::Disputed);
            self.say(format!("hand {}: its contract output {op} ({} sat) is on chain; the dispute graph is this commitment's", self.hand, sat(prev.value)));
        }
        Ok(())
    }

    fn decode(&self, slot: u32, entry: &[u8]) -> Option<Decoded> {
        if entry.len() < 48 {
            return None;
        }
        let head: [u8; 48] = entry[..48].try_into().ok()?;
        let mover = instance::mover_at(slot);
        let key = if mover == self.me { self.ks.wots_public(&instance::state_label(self.hand, 1, slot)).ok()? } else { self.their_state_keys.get(&slot)?.clone() };
        let n_sig = key.params.total_digits() as usize * 20;
        let signed = entry.len() >= 48 + n_sig && {
            let sigs: Vec<[u8; 20]> = entry[48..48 + n_sig].chunks(20).map(|x| x.try_into().unwrap()).collect();
            refute::check_entry_sig(&key, &blackjack::auth_message(&head), &sigs)
        };
        let strings = if entry.len() >= 48 + n_sig { bj::decode_shares(&entry[48 + n_sig..]) } else { None };
        let word0_ok = head[0..4] == bj::word0(GAME_ID, slot, whose(mover)).to_be_bytes();
        Some(Decoded { state: State::from_head(&head), word0_ok, signed, strings })
    }

    fn string(&self, who: u8, k: usize) -> Option<Vec<u8>> {
        if who == whose(self.me) {
            self.shares.get(k).map(|s| s.string.clone())
        } else {
            self.strings.get(&(who, k)).cloned()
        }
    }

    fn predicates(&self, slot: u32, prior: &State, new_head: &[u8; 48], word0_ok: bool) -> Vec<(String, Vec<Vec<u8>>)> {
        let n = State::from_head(new_head);
        let pl = instance::mover_at(slot) == Role::User;
        let mut out: Vec<(String, Vec<Vec<u8>>)> = Vec::new();
        let prior_ok = slot == 1 || self.blocks.get(&(slot - 1)).is_some_and(|b| b.header.head()[0..4] == bj::word0(GAME_ID, slot - 1, whose(instance::mover_at(slot - 1))).to_be_bytes());
        if !word0_ok || !prior_ok {
            out.push(("wrong_slot".into(), vec![]));
        }
        for (name, f) in [
            ("bj_malformed", bj::head_malformed(new_head)),
            ("bj_transition", bj::transition_fires(prior, &n, pl)),
            ("bj_counters", bj::counters_fires(prior, &n)),
            ("bj_cards_kept", bj::cards_kept_fires(prior, &n)),
            ("bj_status", bj::status_fires(prior, &n)),
            ("bj_dealer", !pl && bj::dealer_fires(prior, &n)),
        ] {
            if f {
                out.push((name.into(), vec![]));
            }
        }
        let mover = whose(instance::mover_at(slot));
        for k in 0..POSITIONS {
            if let Some(s) = self.string(mover, k) {
                if bj::share_fires(&n, k, bj::open(&s)) {
                    out.push((format!("bj_share_{k}"), vec![s]));
                }
            }
            if !pl {
                if let (Some(a), Some(b)) = (self.string(0, k), self.string(1, k)) {
                    if bj::card_fires(prior, &n, k, bj::open(&a), bj::open(&b)) {
                        out.push((format!("bj_card_{k}"), vec![a, b]));
                    }
                }
            }
        }
        out
    }

    fn on_seal(&mut self, b: &BlockJson, block: SealedBlock) -> Result<()> {
        let slot = b.depth;
        let by = block.proposer;
        let when = self.rel(b.sealed_at);
        if let Some(held) = self.blocks.get(&slot) {
            if held.head() != block.head() {
                self.say(format!("venue: move {slot}: a SECOND, different head sealed by member {by} — an equivocation"));
            }
            return Ok(());
        }
        if b.late {
            self.late_slots.insert(slot);
            self.say(format!("venue: move {slot} sealed LATE by member {by}: the members' flags stand"));
        }
        if b.rogue {
            self.rogue_slots.insert(slot);
        }
        self.blocks.insert(slot, block.clone());
        let mover = instance::mover_at(slot);
        let mover_s = side(mover);
        let Some(dec) = self.decode(slot, &block.entry) else {
            self.bad_slots.insert(slot, "an undecodable entry".into());
            self.say(format!("venue: move {slot} sealed by member {by} with an UNDECODABLE entry"));
            return Ok(());
        };
        if !dec.signed {
            self.bad_slots.insert(slot, "not signed by the mover".into());
            self.say(format!("venue: move {slot} sealed by member {by} (a ROGUE seal) — not signed by the {mover_s}: not a move"));
            return Ok(());
        }
        let n = dec.state;
        let strings = dec.strings.unwrap_or_default();
        let range: Vec<usize> = bj::revealed(&n).filter(|k| *k < POSITIONS).collect();
        let commits = self.commits.clone().ok_or_else(|| anyhow!("no commitments"))?;
        let mut opened = strings.len() == range.len();
        for (k, s) in range.iter().zip(strings.iter()) {
            opened &= bj::open(s) >= 0 && bj::commit(s) == *commits.of(mover == Role::User, *k);
            if mover != self.me {
                self.strings.insert((whose(mover), *k), s.clone());
            }
        }
        if !opened {
            self.bad_slots.insert(slot, "a declared share does not open its commitment".into());
            self.say(format!("venue: move {slot} sealed by member {by} (a ROGUE seal) — a declared share does not open: not a move"));
            return Ok(());
        }
        if slot != self.depth + 1 {
            self.bad_slots.insert(slot, format!("the hand was at depth {}", self.depth));
            self.say(format!("venue: move {slot} sealed out of sequence"));
            return Ok(());
        }
        let head = block.header.head();
        let firing = self.predicates(slot, &self.state, &head, dec.word0_ok);
        if !firing.is_empty() {
            let names: Vec<String> = firing.iter().map(|(n, _)| n.clone()).collect();
            self.bad_slots.insert(slot, names.join(", "));
            self.say(format!("venue: move {slot} sealed the {mover_s}'s {} — NOT a valid move ({}): nothing to settle; force-close and dispute", action_ui(n.action), names.join(", ")));
            return Ok(());
        }
        self.state = n;
        self.depth = slot;
        self.say(format!("venue: move {slot} sealed by member {by} at t+{when}s: the {mover_s} — {}", self.describe()));
        Ok(())
    }

    fn describe(&self) -> String {
        let s = &self.state;
        let cards = |ps: &[usize]| ps.iter().filter(|k| s.dealt(**k)).map(|k| bj::rank_name(s.cards[*k])).collect::<Vec<_>>().join(" ");
        match s.action {
            action::DEAL => "DEAL: the player's shares of the first three cards".into(),
            action::HIT => format!("HIT: the player's share of card {}", s.np),
            action::STAND => format!("STAND on {}: the player's shares of the hole and every draw", s.player_total()),
            action::ACK => format!("ACK: {}", status_ui(s.status)),
            action::REVEAL => {
                let mut t = format!("REVEAL: player {} ({})", cards(&s.player_positions()), s.player_total());
                if s.dealt(bj::HOLE) {
                    t += &format!(", dealer {} ({})", cards(&s.dealer_positions()), s.dealer_total());
                } else if s.dealt(bj::UP) {
                    t += &format!(", dealer shows {}", bj::rank_name(s.cards[bj::UP]));
                }
                if s.is_terminal() {
                    t += &format!(" — {}", status_ui(s.status));
                }
                t
            }
            _ => "?".into(),
        }
    }

    fn on_tx(&mut self, height: u32, tx: &Transaction) -> Result<()> {
        let txid = tx.compute_txid();
        if let Some(p) = self.graph.iter().find(|p| p.txid() == txid) {
            let label = p.label.clone();
            let live = Live { height, op: OutPoint { txid, vout: 0 }, prev: tx.output[0].clone() };
            self.say(format!("chain: height {height}: `{label}` confirmed ({} vB)", tx.vsize()));
            if label.ends_with("/refute") {
                let base = label.trim_end_matches("/refute").to_string();
                match self.parse_reveal(&base, tx) {
                    Ok(sig) => {
                        self.reveals.insert(base.clone(), sig);
                        self.say(format!("chain: read the mover's pair reveal off `{label}`'s witness"));
                    }
                    Err(e) => self.say(format!("chain: could not parse the reveal in `{label}`: {e}")),
                }
            }
            self.live.insert(label, live);
        }
        for i in &tx.input {
            let op = i.previous_output;
            if let Some((label, _)) = self.live.iter().find(|(_, l)| l.op == op) {
                if !self.spent.contains_key(&op) {
                    let label = label.clone();
                    self.spent.insert(op, (txid, height));
                    if !self.graph.iter().any(|p| p.txid() == txid) {
                        self.say(format!("chain: height {height}: the output of `{label}` was spent by a runtime transaction {txid} ({} vB) — a disprove or a timeliness flag", tx.vsize()));
                    }
                }
            }
        }
        Ok(())
    }

    fn parse_reveal(&self, base: &str, tx: &Transaction) -> Result<WotsSig> {
        let d = base_depth(base)?;
        let params = if d >= 2 { refute::pair_params() } else { refute::refute_params() };
        let total = params.total_digits() as usize;
        let w = &tx.input[0].witness;
        let n = w.len();
        ensure!(n >= 2 + 3 + 2 * total, "witness too short");
        let args: Vec<Vec<u8>> = (0..n - 2).map(|i| w.nth(i).unwrap().to_vec()).collect();
        let block = &args[args.len() - 3 - 2 * total..args.len() - 3];
        let hashes: Vec<[u8; 20]> = block.iter().step_by(2).map(|h| h.as_slice().try_into().map_err(|_| anyhow!("a reveal hash is 20 bytes"))).collect::<Result<_>>()?;
        let msg = self.parked_message(d)?;
        WotsSig::from_hashes(params, &msg, hashes).map_err(|e| anyhow!("{e}"))
    }

    fn parked_message(&self, d: u32) -> Result<Vec<u8>> {
        let head = |s: u32| -> Result<[u8; 48]> { Ok(self.blocks.get(&s).ok_or_else(|| anyhow!("no venue seal at depth {s}"))?.header.head()) };
        let mut m = Vec::new();
        if d >= 2 {
            m.extend_from_slice(&head(d - 1)?);
        }
        m.extend_from_slice(&head(d)?);
        Ok(m)
    }

    fn prior_of(&self, d: u32) -> State {
        if d >= 2 { self.blocks.get(&(d - 1)).map(|b| State::from_head(&b.header.head())).unwrap_or_default() } else { State::initial() }
    }

    // ============ what can be done now ============

    fn live_claims(&self) -> Vec<(String, u32)> {
        let mut v = Vec::new();
        for (label, l) in &self.live {
            if self.spent.contains_key(&l.op) {
                continue;
            }
            if let Some(d) = label.strip_prefix("absent_").and_then(|s| s.parse::<u32>().ok()) {
                v.push((label.clone(), d));
            } else if let Some(d) = label.strip_prefix("absent_").and_then(|s| s.strip_suffix("/counter")).and_then(|s| s.parse::<u32>().ok()) {
                v.push((label.clone(), d - 1));
            }
        }
        v
    }

    fn live_refuted(&self) -> Vec<(String, u32)> {
        self.live
            .iter()
            .filter(|(label, l)| label.ends_with("/refute") && !self.spent.contains_key(&l.op))
            .filter_map(|(label, _)| {
                let base = label.trim_end_matches("/refute").to_string();
                base_depth(&base).ok().map(|d| (base, d))
            })
            .collect()
    }

    fn mempool_labels(&self) -> Vec<String> {
        let Ok(pool) = self.rt.mempool() else { return vec![] };
        self.graph.iter().filter(|p| pool.contains(&p.txid())).map(|p| p.label.clone()).collect()
    }

    fn firing(&self, d: u32) -> Vec<(String, Vec<Vec<u8>>)> {
        let Some(new) = self.blocks.get(&d) else { return vec![] };
        if d >= 2 && !self.blocks.contains_key(&(d - 1)) {
            return vec![];
        }
        let head = new.header.head();
        let word0_ok = head[0..4] == bj::word0(GAME_ID, d, whose(instance::mover_at(d))).to_be_bytes();
        self.predicates(d, &self.prior_of(d), &head, word0_ok)
    }

    fn r_of(&self, d: u32) -> Option<u8> {
        let b = self.blocks.get(&d)?;
        Some(bj::resolution(&State::from_head(&b.header.head()), whose(instance::mover_at(d))))
    }

    fn wins(&self, code: u8) -> bool {
        code == 2 || code == whose(self.me)
    }

    /// Why a depth-`d` claim is not yet mineable: the contract output must
    /// be on chain; the claim's MTP lock; the broadcaster's own claim waits
    /// out `to_self_delay` after the commitment.
    fn claim_wait(&self, d: u32) -> Option<String> {
        let Some((_, version, h0)) = self.closed else { return Some("the channel is open: force-close it first".into()) };
        let at = self.inst.as_ref()?.claim_from(d);
        let mtp = self.rt.mtp().unwrap_or(0);
        if mtp <= at {
            return Some(format!("its lock is median-time-past > t+{}s; MTP is t+{}s", self.rel(at), self.rel(mtp)));
        }
        let h = self.height();
        let csv = h0 + u32::from(self.params.to_self_delay);
        if version == self.me && h < csv {
            return Some(format!("I broadcast the commitment: my claim waits to height {csv} ({} blocks)", csv - h));
        }
        None
    }

    fn window_open(&self, label: &str, blocks: u16) -> Result<u32> {
        let l = self.live.get(label).ok_or_else(|| anyhow!("`{label}` is not confirmed"))?;
        Ok(l.height + u32::from(blocks))
    }

    fn need_height(&self, at: u32, what: &str) -> Result<()> {
        let h = self.height();
        ensure!(h >= at, "not broadcast: {what} cannot be mined before height {at} ({} blocks to go)", at - h);
        Ok(())
    }

    /// The opponent's earliest due move with no valid timely seal: the
    /// reason for a claim (and, with the channel open, a force-close).
    fn grievance(&self) -> Option<(u32, String)> {
        if !matches!(self.hand_phase, Some(HandPhase::Playing) | Some(HandPhase::Disputed)) {
            return None;
        }
        let now = unix_now();
        let d = self.depth + 1;
        (1..=d).filter(|s| instance::mover_at(*s) != self.me && self.due(*s) < now).find_map(|s| {
            let untimely = self.blocks.get(&s).map(|_| self.bad_slots.contains_key(&s) || self.late_slots.contains(&s) || self.rogue_slots.contains(&s)).unwrap_or(true);
            let claimed = self.live.contains_key(&format!("absent_{s}")) || self.mempool_labels().contains(&format!("absent_{s}"));
            (untimely && !claimed).then(|| {
                let why = if self.late_slots.contains(&s) { format!("move {s} was sealed only LATE") } else if let Some(w) = self.bad_slots.get(&s) { format!("move {s} is not a valid move ({w})") } else { format!("the {} did not publish move {s} by t+{}s", side(instance::mover_at(s)), self.rel(self.due(s))) };
                (s, why)
            })
        })
    }

    fn actions(&self) -> Vec<ActionView> {
        let h = self.height();
        let now = unix_now();
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let delta = self.params.delta;
        let delta2 = self.params.delta + self.params.delta_prime;
        let playing = self.hand_phase == Some(HandPhase::Playing);
        let mut v = Vec::new();
        // the session
        if self.me == Role::User {
            v.push(if self.channel_open() && matches!(self.hand_phase, None | Some(HandPhase::Settled)) && self.chan.pending_seq().is_none() {
                ActionView::ok("new hand", &format!("hand {}: {} sat each into the pot, {} each as a dispute deposit", self.hand + 1, sat(Amount::from_sat(STAKE_SAT)), sat(Amount::from_sat(self.vparams.deposit))))
            } else {
                ActionView::no("new hand", if self.channel_open() { "a hand is in progress" } else { "the channel is closed" })
            });
        }
        // the game's moves (the player's buttons)
        if self.me == Role::User {
            let s = &self.state;
            let can = playing && mover == self.me && now <= self.due(d) && self.pending.as_ref().is_none_or(|p| p.0 != d);
            let why = if !playing { "no hand in play".to_string() } else if mover != self.me { format!("the House to move (move {d})") } else if now > self.due(d) { format!("move {d} was due at t+{}s", self.rel(self.due(d))) } else { format!("move {d} due in {}s", i64::from(self.due(d)) - i64::from(now)) };
            v.push(if can && s.phase == phase::START { ActionView::ok("deal", &why) } else { ActionView::no("deal", &why) });
            let decide = can && s.phase == phase::DECIDE;
            v.push(if decide && bj::can_hit(s) { ActionView::ok("hit", &format!("you have {}", s.player_total())) } else { ActionView::no("hit", "not your decision") });
            v.push(if decide { ActionView::ok("stand", &format!("stand on {}", s.player_total())) } else { ActionView::no("stand", "not your decision") });
        }
        // settle: the winner proposes the agreed result
        let my_win = self.state.is_terminal()
            && match self.state.status {
                status::PLAYER | status::PUSH => self.me == Role::User,
                status::HOUSE => self.me == Role::Hub,
                _ => false,
            };
        v.push(if playing && self.hand_in_channel() && my_win && self.chan.pending_seq().is_none() {
            ActionView::ok("settle", &format!("{}: pay it in the channel, now", status_ui(self.state.status)))
        } else if playing && self.state.is_terminal() {
            ActionView::no("settle", &format!("{}: the winner settles it", status_ui(self.state.status)))
        } else {
            ActionView::no("settle", "the hand is not over")
        });
        // force-close
        v.push(if self.channel_open() && self.hand_in_channel() {
            match self.grievance() {
                Some((_, why)) => ActionView::ok("force close", &format!("{why}: take it on chain")),
                None => ActionView::ok("force close", "nothing wrong yet; closing puts the hand on chain"),
            }
        } else {
            ActionView::no("force close", if self.channel_open() { "no hand in the channel" } else { "the channel is closed" })
        });
        // claim
        v.push(match self.grievance() {
            None => ActionView::no("claim", "nothing to claim"),
            Some((s, why)) => match self.claim_wait(s) {
                Some(wait) => ActionView::no("claim", &format!("{why}: not yet — {wait}")).with_cmd(&format!("claim {s}")),
                None => ActionView::ok("claim", &why).with_cmd(&format!("claim {s}")),
            },
        });
        // counter / refute
        let against_me: Vec<(String, u32)> = self.live_claims().into_iter().filter(|(_, dd)| instance::mover_at(*dd) == self.me).collect();
        match against_me.first() {
            Some((base, dd)) => {
                let can_counter = !base.contains("counter") && *dd >= 2;
                v.push(if can_counter { ActionView::ok("counter", &format!("`{base}`: say the claimant did not move at {}", dd - 1)) } else { ActionView::no("counter", "no counter on a counter, nor at depth 1") });
                v.push(match (self.blocks.contains_key(dd), self.bad_slots.get(dd)) {
                    (true, None) => ActionView::ok("refute", &format!("`{base}`: the venue attested your move {dd}")),
                    (true, Some(why)) => ActionView::ok("refute", &format!("`{base}`: the venue attested your move {dd}, which is NOT valid ({why})")),
                    (false, _) => ActionView::no("refute", &format!("`{base}`: nothing of yours is sealed for move {dd}")),
                });
            }
            None => {
                v.push(ActionView::no("counter", "no live claim against you"));
                v.push(ActionView::no("refute", "no live claim against you"));
            }
        }
        // disprove / timely
        match self.live_refuted().into_iter().find(|(_, dd)| instance::mover_at(*dd) != self.me) {
            Some((base, dd)) => {
                let open = self.window_open(&format!("{base}/refute"), delta).unwrap_or(0);
                let firing: Vec<String> = self.firing(dd).into_iter().map(|(n, _)| n).collect();
                let flags = self.flags.get(&dd).map(|f| f.iter().filter(|x| x.is_some()).count()).unwrap_or(0);
                if h < open {
                    v.push(ActionView::no("disprove", &format!("`{base}`: the window opens at height {open}; fires: {}", if firing.is_empty() { "nothing".into() } else { firing.join(", ") })));
                    v.push(ActionView::no("timely", &format!("the window opens at height {open}; {flags} of {K} flags known")));
                } else {
                    v.push(if firing.is_empty() { ActionView::no("disprove", &format!("`{base}` (move {dd}): nothing fires")) } else { ActionView::ok("disprove", &format!("`{base}` (move {dd}): {}", firing.join(", "))) });
                    v.push(if flags >= self.vparams.threshold as usize { ActionView::ok("timely", &format!("{flags} of {K} members flagged move {dd}")) } else { ActionView::no("timely", &format!("{flags} of {K} flags known for move {dd}")) });
                }
            }
            None => {
                v.push(ActionView::no("disprove", "no live refutation against you"));
                v.push(ActionView::no("timely", "no live refutation against you"));
            }
        }
        // split
        let mut split = ActionView::no("split", "nothing of yours to split");
        if let Some((base, dd, code)) = self.live_refuted().into_iter().filter_map(|(b, dd)| self.r_of(dd).map(|c| (b, dd, c))).find(|(_, _, c)| self.wins(*c)) {
            let open = self.window_open(&format!("{base}/refute"), delta2).unwrap_or(0);
            split = if h >= open { ActionView::ok("split", &format!("`{base}` (move {dd}): R = {}", outcome_ui(code))) } else { ActionView::no("split", &format!("`{base}`: R = {}; opens at height {open} ({} blocks)", outcome_ui(code), open - h)) };
        } else if let Some((base, _)) = self.live_claims().into_iter().find(|(_, dd)| instance::mover_at(*dd) != self.me) {
            let open = self.window_open(&base, delta).unwrap_or(0);
            split = if h >= open { ActionView::ok("split", &format!("your claim `{base}` is unanswered: the timeout split")) } else { ActionView::no("split", &format!("your claim `{base}`: the timeout opens at height {open} ({} blocks)", open - h)) };
        }
        v.push(split);
        // the session's end
        if self.me == Role::User {
            v.push(if self.channel_open() && !self.hand_in_channel() && self.chan.pending_seq().is_none() && self.chan.current_seq() > 0 { ActionView::ok("close channel", "pay both balances out in one cooperative transaction") } else { ActionView::no("close channel", "only with no hand in the channel") });
        }
        v
    }

    // ============ the house's autopilot ============

    fn pilot(&mut self) -> Result<()> {
        let d = self.depth + 1;
        let now = unix_now();
        let playing = self.hand_phase == Some(HandPhase::Playing);
        if playing && instance::mover_at(d) == self.me && now <= self.due(d) && self.pending.is_none() && !self.blocks.contains_key(&d) && self.mode != Mode::Withhold && matches!(self.state.phase, phase::DEALT | phase::HIT | phase::STOOD) {
            self.reveal()?;
        }
        let pool = self.mempool_labels();
        let now = unix_now();
        // a finished hand is settled in the channel, not taken on chain,
        // unless my settle went unanswered for 30 s
        let settling = self.state.is_terminal() && self.hand_in_channel() && self.settle_sent.is_none_or(|t| now < t + 30);
        for a in self.actions() {
            if !a.enabled {
                continue;
            }
            let key = format!("{}:{}", a.name, a.hint);
            if self.done.contains(&key) || self.failed.get(&key).is_some_and(|t| now < t + 10) {
                continue;
            }
            if a.name != "settle" && !self.auto_disputes {
                continue;
            }
            let r = match a.name.as_str() {
                "settle" => self.settle(),
                // the house takes a stall on chain (a withholding house does not)
                "force close" if self.grievance().is_some() && self.mode != Mode::Withhold && !settling => self.force_close(),
                "refute" if !pool.iter().any(|l| l.ends_with("/refute")) => self.refute(),
                "claim" if self.mode != Mode::Withhold => {
                    let dd = a.cmd.split_whitespace().nth(1).and_then(|x| x.parse().ok());
                    self.claim(dd)
                }
                "counter" => match self.live_claims().into_iter().find(|(b, dd)| !b.contains("counter") && instance::mover_at(*dd) == self.me && *dd >= 2) {
                    Some((_, dd)) => {
                        let prev = dd - 1;
                        let claimant_won = self.r_of(prev).is_some_and(|c| c == whose(self.me.other()));
                        let steals = !self.blocks.contains_key(&dd) && (self.bad_slots.contains_key(&prev) || !self.blocks.contains_key(&prev) || !claimant_won);
                        if steals { self.counter(Some(dd)) } else { continue }
                    }
                    None => continue,
                },
                "disprove" => self.disprove(None),
                "timely" => self.timely(),
                "split" => self.split(),
                _ => continue,
            };
            match r {
                Ok(()) => {
                    self.done.insert(key);
                }
                Err(e) => {
                    self.failed.insert(key, now);
                    self.say(format!("autopilot: {} failed (retrying in 10s): {e:#}", a.name));
                }
            }
        }
        Ok(())
    }

    fn reveal(&mut self) -> Result<()> {
        let d = self.depth + 1;
        let prior = self.state;
        let card_of = |me: &Self, k: usize| -> Result<u8> {
            let a = me.strings.get(&(0, k)).ok_or_else(|| anyhow!("the player's share {k} is not known"))?;
            let a = bj::open(a);
            ensure!((0..=12).contains(&a), "the player's share {k} is out of range");
            Ok(bj::card(a as u8, me.shares[k].value))
        };
        let mut cards = [0u8; POSITIONS];
        for k in bj::revealed(&match prior.phase {
            phase::DEALT => State { lo: 0, hi: 3, ..prior },
            _ => prior,
        }) {
            cards[k] = card_of(self, k)?;
        }
        let mut n = bj::house_reveal(&prior, |k| cards[k]).ok_or_else(|| anyhow!("no reveal from phase {}", prior.phase))?;
        let mut cheat = "";
        match self.mode {
            Mode::WrongCard => {
                let k = if prior.phase == phase::STOOD { bj::HOLE } else { (n.np - 1) as usize };
                n.cards[k] = (n.cards[k] + 1) % 13;
                if prior.phase == phase::STOOD {
                    n.status = bj::showdown(&n);
                } else if prior.phase == phase::HIT {
                    n.status = if n.player_total() > 21 { status::HOUSE } else { status::OPEN };
                    n.phase = if n.status != status::OPEN { phase::DONE } else { phase::DECIDE };
                }
                cheat = " (CHEAT: a card one rank off)";
            }
            Mode::DrawAt17 if prior.phase == phase::STOOD && n.np < bj::DRAW_LIMIT => {
                let k = n.np as usize;
                n.cards[k] = cards[k];
                n.np += 1;
                n.status = bj::showdown(&n);
                cheat = " (CHEAT: the dealer draws past 17)";
            }
            Mode::StandOn16 if prior.phase == phase::STOOD && n.np > prior.np => {
                let keep = n.np - 1;
                n.cards[keep as usize] = 0;
                n.np = keep;
                n.status = bj::showdown(&n);
                cheat = " (CHEAT: the dealer stops early)";
            }
            _ => {}
        }
        if !cheat.is_empty() {
            self.mode = Mode::Honest;
        }
        self.submit(d, &n)?;
        self.say(format!("submitted move {d}: REVEAL{cheat}"));
        Ok(())
    }

    // ============ moves ============

    fn submit(&mut self, d: u32, n: &State) -> Result<()> {
        let head = n.head(GAME_ID, d, whose(self.me));
        let sig = self.ks.sign_wots(&instance::state_label(self.hand, 1, d), &blackjack::auth_message(&head)).map_err(|e| anyhow!("signing (a depth's state key signs once): {e}"))?;
        let strings: Vec<Vec<u8>> = bj::revealed(n).filter(|k| *k < POSITIONS).map(|k| self.shares[k].string.clone()).collect();
        let refs: Vec<&[u8]> = strings.iter().map(|v| v.as_slice()).collect();
        let entry = blackjack::entry(&head, &sig, &refs);
        let to = lngap_pos::rotation(self.hand, d, self.vparams.n);
        self.send(d, &hex::encode(entry), to)
    }

    fn play(&mut self, what: &str) -> Result<()> {
        ensure!(self.me == Role::User, "the House plays itself");
        ensure!(self.hand_phase == Some(HandPhase::Playing), "no hand in play");
        let d = self.depth + 1;
        ensure!(instance::mover_at(d) == self.me, "it is the House's move (move {d})");
        ensure!(unix_now() <= self.due(d), "your move {d} was due at t+{}s", self.rel(self.due(d)));
        ensure!(self.pending.as_ref().is_none_or(|p| p.0 != d), "your move {d} is already with the venue");
        let s = self.state;
        let n = match what {
            "deal" => {
                ensure!(s.phase == phase::START, "already dealt");
                bj::deal(&s)
            }
            "hit" => {
                ensure!(s.phase == phase::DECIDE && bj::can_hit(&s), "you cannot hit now");
                bj::hit(&s)
            }
            "stand" => {
                ensure!(s.phase == phase::DECIDE, "you cannot stand now");
                bj::stand(&s)
            }
            "ack" => {
                ensure!(bj::can_ack(&s), "only after a hand you won or pushed");
                bj::ack(&s)
            }
            _ => bail!("unknown move {what}"),
        };
        self.submit(d, &n)?;
        self.say(format!("submitted move {d}: {}", what.to_uppercase()));
        Ok(())
    }

    fn send(&mut self, d: u32, entry: &str, to: usize) -> Result<()> {
        let at = unix_now();
        let name = format!("{}/{}.json", Store::inbox_dir(self.hand), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
        self.store.write(&name, &InboxEntry { from: side(self.me).into(), depth: d, to, entry: entry.to_string(), at })?;
        self.pending = Some((d, entry.to_string(), to, at));
        Ok(())
    }

    fn broadcast(&mut self, tx: &Transaction, what: &str) -> Result<()> {
        if let Err(e) = self.rt.test_accept(tx) {
            bail!("{what}: the node rejects it: {e}");
        }
        let txid = self.rt.send_raw(tx)?;
        self.say(format!("broadcast {what}: {txid} ({} vB); it confirms at the next block", tx.vsize()));
        Ok(())
    }

    fn sigs22(&self, label: &str) -> Result<[Vec<u8>; 2]> {
        let p = self.skel(label)?;
        let su = p.sigs[0].ok_or_else(|| anyhow!("{label}: no user sig"))?;
        let sh = p.sigs[1].ok_or_else(|| anyhow!("{label}: no hub sig"))?;
        Ok([sh.as_ref().to_vec(), su.as_ref().to_vec()])
    }

    fn claim(&mut self, d: Option<u32>) -> Result<()> {
        let d = d.or_else(|| self.grievance().map(|g| g.0)).ok_or_else(|| anyhow!("nothing to claim"))?;
        ensure!(instance::mover_at(d) != self.me, "depth {d} is your own move");
        if let Some(wait) = self.claim_wait(d) {
            bail!("not broadcast: `absent_{d}` is not mineable yet — {wait}");
        }
        let label = format!("absent_{d}");
        let [sh, su] = self.sigs22(&label)?;
        let p = self.skel(&label)?;
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&[sh, su], &p.leaf.script, &p.control_block);
        self.say(format!("claiming: no valid move {d} by its due time t+{}s", self.rel(self.due(d))));
        self.broadcast(&tx, &format!("`{label}`"))
    }

    fn counter(&mut self, d: Option<u32>) -> Result<()> {
        let live = self.live_claims();
        let (base, depth) = match d {
            Some(d) => (format!("absent_{d}"), d),
            None => live.iter().find(|(b, dd)| !b.contains("counter") && instance::mover_at(*dd) == self.me).cloned().ok_or_else(|| anyhow!("no live claim against you to counter"))?,
        };
        ensure!(depth >= 2, "no counter at depth 1");
        let label = format!("{base}/counter");
        let [sh, su] = self.sigs22(&label)?;
        let p = self.skel(&label)?;
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&[sh, su], &p.leaf.script, &p.control_block);
        self.say(format!("countering `{base}`: the claim was not due — no move {}", depth - 1));
        self.broadcast(&tx, &format!("`{label}`"))
    }

    fn refute(&mut self) -> Result<()> {
        let live = self.live_claims();
        let (base, d) = live.iter().find(|(_, d)| instance::mover_at(*d) == self.me).cloned().ok_or_else(|| anyhow!("no live claim against you on the chain"))?;
        let label = format!("{base}/refute");
        let (tx, prev, leaf, control) = {
            let p = self.skel(&label)?;
            (p.tx.clone(), p.prevouts[0].clone(), p.leaf.script.clone(), p.control_block.clone())
        };
        let new = self.blocks.get(&d).ok_or_else(|| anyhow!("nothing is sealed for move {d}"))?.clone();
        let new_head = new.header.head();
        let msg = self.parked_message(d)?;
        let pair_sig = self.ks.sign_wots(&instance::refute_label(self.hand, 1, d), &msg).map_err(|e| anyhow!("{e}"))?;
        let auth = self.ks.sign_wots(&instance::state_label(self.hand, 1, d), &blackjack::auth_message(&new_head)).map_err(|e| anyhow!("{e}"))?;
        let sign_at = |b: &SealedBlock| -> Vec<Vec<u8>> { (0..HEAD_CHUNKS).map(|j| sig_bytes(&Keypair::from_secret_key(SECP256K1, &b.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect() };
        let sigs_new = sign_at(&new);
        let mut w = if d >= 2 {
            let prior = self.blocks.get(&(d - 1)).ok_or_else(|| anyhow!("no seal for move {}", d - 1))?;
            refute::refute_witness_pair(&sign_at(prior), &sigs_new, &pair_sig, &[&auth])
        } else {
            refute::refute_witness(&sigs_new, &pair_sig, &auth)
        };
        w.extend(proposer_witness(sig_bytes(&Keypair::from_secret_key(SECP256K1, &new.proposer_secret), &tx, &prev, &leaf), new.proposer));
        w.push(sig_bytes(&self.chan.keys.payment, &tx, &prev, &leaf));
        let mut tx = tx;
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.reveals.insert(base.clone(), pair_sig);
        self.say(format!("refuting `{base}`: the venue attested my move {d}"));
        self.broadcast(&tx, &format!("`{label}`"))
    }

    fn payout_tx(&self, base: &str, d: u32, leaf_name: &str) -> Result<(Transaction, TxOut, ScriptBuf, bitcoin::taproot::ControlBlock)> {
        let l = self.live.get(&format!("{base}/refute")).ok_or_else(|| anyhow!("no live refutation on `{base}`"))?.clone();
        let (seq, version, _) = self.closed.ok_or_else(|| anyhow!("the channel is open"))?;
        let ctx = self.chan.commit_ctx(seq, version)?;
        let tree = self.inst()?.refuted_tree(&ctx, d)?;
        let leaf = tree.leaf(leaf_name)?.clone();
        let tx = build_spend(l.op, &leaf.timelock, vec![TxOut { value: l.prev.value - self.params.presign_fee, script_pubkey: self.chan.my_payout_spk() }]);
        Ok((tx, l.prev, leaf.script, tree.control_block(leaf_name)?))
    }

    fn disprove(&mut self, which: Option<String>) -> Result<()> {
        let (base, d) = self.live_refuted().into_iter().find(|(_, d)| instance::mover_at(*d) != self.me).ok_or_else(|| anyhow!("no live refutation against you"))?;
        let firing = self.firing(d);
        let (name, wits) = match which {
            Some(w) => firing.into_iter().find(|(n, _)| *n == w || *n == format!("bj_{w}")).ok_or_else(|| anyhow!("`{w}` does not fire on the parked tuple"))?,
            None => firing.into_iter().next().ok_or_else(|| anyhow!("no disprove leaf fires: the move is valid"))?,
        };
        let leaf_name = format!("disprove_{name}");
        self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta)?, &leaf_name)?;
        let (mut tx, prev, leaf, control) = self.payout_tx(&base, d, &leaf_name)?;
        let reveal = self.reveals.get(&base).ok_or_else(|| anyhow!("the mover's reveal is not known yet"))?.clone();
        let mut w = wits;
        w.extend(refute::wots_wire(&reveal));
        w.push(sig_bytes(&self.chan.keys.payment, &tx, &prev, &leaf));
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.say(format!("disproving the parked move {d} of `{base}`: {name}"));
        self.broadcast(&tx, &leaf_name)
    }

    fn timely(&mut self) -> Result<()> {
        let (base, d) = self.live_refuted().into_iter().find(|(_, d)| instance::mover_at(*d) != self.me).ok_or_else(|| anyhow!("no live refutation against you"))?;
        let scalars = self.flags.get(&d).cloned().ok_or_else(|| anyhow!("no flags known for move {d}"))?;
        self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta)?, "not_timely")?;
        let (mut tx, prev, leaf, control) = self.payout_tx(&base, d, "not_timely")?;
        let w = not_timely_witness(&tx, 0, std::slice::from_ref(&prev), &leaf, &self.chan.keys.payment, &scalars);
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.say(format!("killing the refutation on `{base}` as NOT TIMELY"));
        self.broadcast(&tx, "not_timely")
    }

    fn split(&mut self) -> Result<()> {
        if let Some((base, d, code)) = self.live_refuted().into_iter().filter_map(|(b, dd)| self.r_of(dd).map(|c| (b, dd, c))).find(|(_, _, c)| self.wins(*c)) {
            let label = format!("{base}/refuted/split_{}", outcome_name(code));
            self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta + self.params.delta_prime)?, &label)?;
            let pair = self.reveals.get(&base).ok_or_else(|| anyhow!("no reveal for {base}"))?.clone();
            let [sh, su] = self.sigs22(&label)?;
            let p = self.skel(&label)?;
            let mut tx = p.tx.clone();
            tx.input[0].witness = tapscript_witness(&blackjack::checked_split_witness(su, sh, &pair), &p.leaf.script, &p.control_block);
            self.say(format!("the checked split on `{base}` (move {d}): R = {}", outcome_ui(code)));
            return self.broadcast(&tx, &format!("`{label}`"));
        }
        if let Some((base, d)) = self.live_claims().into_iter().find(|(_, d)| instance::mover_at(*d) != self.me) {
            let code: u8 = whose(self.me);
            let label = format!("{base}/split_{}", outcome_name(code));
            self.need_height(self.window_open(&base, self.params.delta)?, &label)?;
            let reveal = self.ks.reveal_uint(&instance::ccode_label(self.hand, 1, d), u32::from(code))?;
            let [sh, su] = self.sigs22(&label)?;
            let p = self.skel(&label)?;
            let mut tx = p.tx.clone();
            let mut w = reveal.consumption_order();
            w.reverse();
            w.push(sh);
            w.push(su);
            tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
            self.say(format!("timeout split on `{base}`: {} (the staller forfeits)", outcome_ui(code)));
            return self.broadcast(&tx, &format!("`{label}`"));
        }
        bail!("nothing of yours to split")
    }

    pub fn snapshot(&mut self) -> Snapshot {
        let s = self.state;
        let dealt = |k: usize| s.dealt(k);
        let player_cards: Vec<String> = s.player_positions().into_iter().filter(|k| dealt(*k)).map(|k| bj::rank_name(s.cards[k]).to_string()).collect();
        let mut dealer_cards: Vec<String> = Vec::new();
        if dealt(bj::UP) {
            dealer_cards.push(bj::rank_name(s.cards[bj::UP]).into());
            if dealt(bj::HOLE) {
                dealer_cards.push(bj::rank_name(s.cards[bj::HOLE]).into());
                for k in s.ds as usize..s.np as usize {
                    dealer_cards.push(bj::rank_name(s.cards[k]).into());
                }
            } else {
                dealer_cards.push("?".into());
            }
        }
        let mut slots: Vec<SlotView> = self
            .blocks
            .iter()
            .map(|(d, b)| {
                let st = State::from_head(&b.header.head());
                let what = format!("{}: {}", side(instance::mover_at(*d)), action_ui(st.action));
                let entry = match self.bad_slots.get(d) {
                    Some(why) => format!("{what} — NOT a move ({why})"),
                    None => what,
                };
                SlotView { slot: *d, due: self.rel(self.due(*d)), proposer: b.proposer, entry, ok: !self.bad_slots.contains_key(d) && !self.late_slots.contains(d), flags: self.flags.get(d).map(|f| f.iter().filter(|x| x.is_some()).count()), late: self.late_slots.contains(d) }
            })
            .collect();
        for (d, f) in &self.flags {
            if !self.blocks.contains_key(d) {
                slots.push(SlotView { slot: *d, due: self.rel(self.due(*d)), proposer: usize::MAX, entry: "nothing sealed".into(), ok: false, flags: Some(f.iter().filter(|x| x.is_some()).count()), late: false });
            }
        }
        slots.sort_by_key(|v| v.slot);
        let mut live: Vec<LiveView> = self.live.iter().map(|(label, l)| LiveView { label: ui(label), height: l.height, spent: self.spent.contains_key(&l.op), value_sat: l.prev.value.to_sat() }).collect();
        if let Some((seq, v, h)) = self.closed {
            live.insert(0, LiveView { label: format!("commitment {seq} (the {}'s)", side(v)), height: h, spent: false, value_sat: self.params.funding_amount.to_sat() });
        }
        let disproves = self.live_refuted().into_iter().find(|(_, dd)| instance::mover_at(*dd) != self.me).map(|(_, dd)| self.firing(dd).into_iter().map(|(name, _)| DisproveView { name, fires: true }).collect()).unwrap_or_default();
        let balance_sat = self.rt.balance_of(&self.chan.my_payout_spk()).map(|a| a.to_sat()).unwrap_or(0);
        let cb = self.chan.current_state().balances;
        let d = self.depth;
        Snapshot {
            role: self.me.name().into(),
            height: self.height(),
            mtp: self.rel(self.rt.mtp().unwrap_or(0)),
            now: self.rel(unix_now()),
            ell: self.vparams.ell,
            backoff: self.vparams.backoff,
            margin: self.vparams.margin,
            next_due: self.rel(self.due(d + 1)),
            depth: d,
            to_move: side(instance::mover_at(d + 1)).into(),
            hand: self.hand,
            hand_phase: self.hand_phase,
            channel: ChannelView {
                seq: self.chan.current_seq(),
                player: cb[0].to_sat(),
                house: cb[1].to_sat(),
                in_play: self.chan.current_state().contracts_value().to_sat(),
                status: match &self.chan.closing {
                    None => "open".into(),
                    Some(Closing::Cooperative { .. }) => "closed cooperatively".into(),
                    Some(_) => "force-closed".into(),
                },
            },
            results: self.results.clone(),
            phase: s.phase,
            status: status_ui(s.status).into(),
            terminal: s.is_terminal(),
            player_cards,
            player_total: if dealt(0) { s.player_total() } else { 0 },
            dealer_cards,
            dealer_total: if dealt(bj::HOLE) { Some(s.dealer_total()) } else { None },
            n: self.vparams.n,
            threshold: self.vparams.threshold,
            slots,
            live,
            actions: self.actions(),
            disproves,
            mempool: self.mempool_labels().iter().map(|l| ui(l)).collect(),
            balance_sat,
            mode: self.mode,
            autopilot: self.autopilot,
            auto_disputes: self.auto_disputes,
            log: self.log.iter().rev().take(80).rev().cloned().collect(),
        }
    }
}

fn base_depth(base: &str) -> Result<u32> {
    if let Some(d) = base.strip_prefix("absent_").and_then(|s| s.strip_suffix("/counter")).and_then(|s| s.parse::<u32>().ok()) {
        return Ok(d - 1);
    }
    base.strip_prefix("absent_").and_then(|s| s.parse::<u32>().ok()).ok_or_else(|| anyhow!("not a claim base: {base}"))
}

const HELP: &str = "commands:
  status | s            the channel, the hand, what is due
  new | deal | hit | stand | settle
                        the player's session and moves (settle: pay the hand's result in the channel)
  force | claim [d] | counter [d] | refute | disprove [name] | timely | split
                        disputes (force: force-close the channel, putting the hand on chain)
  close                 close the channel cooperatively (no hand in it)
  mode honest|wrongcard|drawat17|standon16|withhold   the house's next move
  autopilot on|off      the house plays its own moves and settles its wins (default on)
  autodisputes on|off   the house also takes every dispute step itself (default off)
  quit";

impl Player {
    fn status(&mut self) -> Result<String> {
        let snap = self.snapshot();
        let mut out = format!("--- {} | channel {} (update {}): Player {} / House {} | hand {} {:?}\n", side(self.me), snap.channel.status, snap.channel.seq, snap.channel.player, snap.channel.house, self.hand, self.hand_phase);
        out += &format!("    player: {} ({})   dealer: {}{}   {}\n", snap.player_cards.join(" "), snap.player_total, snap.dealer_cards.join(" "), snap.dealer_total.map(|t| format!(" ({t})")).unwrap_or_default(), snap.status);
        for a in self.actions() {
            if a.enabled {
                out += &format!("    you may `{}`: {}\n", a.name, a.hint);
            }
        }
        Ok(out.trim_end().to_string())
    }

    pub fn exec(&mut self, line: &str) -> Result<String> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        let Some(cmd) = parts.first() else { return Ok(String::new()) };
        let arg = parts.get(1).map(|s| s.to_string());
        let before = self.log.len();
        let r: Result<String> = match *cmd {
            "help" | "?" => Ok(HELP.to_string()),
            "status" | "s" => self.status(),
            "new" => self.new_hand().map(|_| String::new()),
            "deal" | "hit" | "stand" | "ack" => self.play(cmd).map(|_| String::new()),
            "settle" => self.settle().map(|_| String::new()),
            "force" => self.force_close().map(|_| String::new()),
            "close" => self.close_channel().map(|_| String::new()),
            "mode" => {
                let m = arg.as_deref().and_then(Mode::parse).ok_or_else(|| anyhow!("mode honest|wrongcard|drawat17|standon16|withhold"))?;
                ensure!(self.me == Role::Hub, "the Player does not cheat in this demo");
                self.mode = m;
                Ok(format!("the House's next move: {m:?}"))
            }
            "autopilot" => {
                self.autopilot = arg.as_deref() != Some("off");
                Ok(format!("autopilot (own moves and settling wins) {}", if self.autopilot { "on" } else { "off" }))
            }
            "autodisputes" => {
                self.auto_disputes = arg.as_deref() != Some("off");
                Ok(format!("automatic disputes {}", if self.auto_disputes { "on" } else { "off: click each step" }))
            }
            "claim" => self.claim(arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "counter" => self.counter(arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "refute" => self.refute().map(|_| String::new()),
            "disprove" => self.disprove(arg).map(|_| String::new()),
            "timely" => self.timely().map(|_| String::new()),
            "split" => self.split().map(|_| String::new()),
            other => Err(anyhow!("unknown command {other} (try `help`)")),
        };
        let said: Vec<String> = self.log[before..].to_vec();
        match r {
            Ok(text) => Ok(if text.is_empty() { said.join("\n") } else { text }),
            Err(e) => Err(e),
        }
    }
}

pub fn run(dir: PathBuf, me: Role, max_depth: u32, web: Option<u16>) -> Result<()> {
    let p = Player::open(dir, me, max_depth)?;
    if let Some(port) = web {
        return crate::web::serve_player(p, port);
    }
    let mut p = p;
    println!("{HELP}");
    let stdin = std::io::stdin();
    let mut line = String::new();
    loop {
        p.sync()?;
        print!("{}> ", side(me));
        std::io::stdout().flush()?;
        line.clear();
        if stdin.lock().read_line(&mut line)? == 0 {
            break;
        }
        if line.trim() == "quit" || line.trim() == "exit" {
            break;
        }
        match p.exec(&line) {
            Ok(text) if text.is_empty() => {}
            Ok(text) => println!("{text}"),
            Err(e) => println!("  ! {e:#}"),
        }
    }
    Ok(())
}

// ============ the pages' view ============

#[derive(Serialize, Clone, Debug)]
pub struct ActionView {
    pub name: String,
    pub enabled: bool,
    pub hint: String,
    pub cmd: String,
}

impl ActionView {
    fn ok(name: &str, hint: &str) -> ActionView {
        ActionView { name: name.into(), enabled: true, hint: hint.into(), cmd: cmd_of(name) }
    }
    fn no(name: &str, hint: &str) -> ActionView {
        ActionView { name: name.into(), enabled: false, hint: hint.into(), cmd: cmd_of(name) }
    }
    fn with_cmd(mut self, cmd: &str) -> ActionView {
        self.cmd = cmd.into();
        self
    }
}

fn cmd_of(name: &str) -> String {
    match name {
        "new hand" => "new".into(),
        "force close" => "force".into(),
        "close channel" => "close".into(),
        n => n.into(),
    }
}

#[derive(Serialize, Clone, Debug)]
pub struct SlotView {
    pub slot: u32,
    pub due: i64,
    pub proposer: usize,
    pub entry: String,
    pub ok: bool,
    pub flags: Option<usize>,
    pub late: bool,
}

#[derive(Serialize, Clone, Debug)]
pub struct LiveView {
    pub label: String,
    pub height: u32,
    pub spent: bool,
    pub value_sat: u64,
}

#[derive(Serialize, Clone, Debug)]
pub struct DisproveView {
    pub name: String,
    pub fires: bool,
}

#[derive(Serialize, Clone, Debug)]
pub struct ChannelView {
    pub seq: u64,
    pub player: u64,
    pub house: u64,
    pub in_play: u64,
    pub status: String,
}

#[derive(Serialize, Clone, Debug)]
pub struct Snapshot {
    pub role: String,
    pub height: u32,
    pub mtp: i64,
    pub now: i64,
    pub ell: u32,
    pub backoff: u32,
    pub margin: u32,
    pub next_due: i64,
    pub depth: u32,
    pub to_move: String,
    pub hand: u32,
    pub hand_phase: Option<HandPhase>,
    pub channel: ChannelView,
    pub results: Vec<String>,
    pub phase: u8,
    pub status: String,
    pub terminal: bool,
    pub player_cards: Vec<String>,
    pub player_total: u32,
    pub dealer_cards: Vec<String>,
    pub dealer_total: Option<u32>,
    pub n: usize,
    pub threshold: u32,
    pub slots: Vec<SlotView>,
    pub live: Vec<LiveView>,
    pub actions: Vec<ActionView>,
    pub disproves: Vec<DisproveView>,
    pub mempool: Vec<String>,
    pub balance_sat: u64,
    pub mode: Mode,
    pub autopilot: bool,
    pub auto_disputes: bool,
    pub log: Vec<String>,
}
