//! One side of the hand: its keys and shares, its view of the venue and the
//! chain, its moves and its disputes. The Player drives it from its page;
//! the House runs an autopilot (reveal when due, play the dealer's rule,
//! answer disputes honestly) unless a cheat mode is set from its console.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::{BufRead, Write};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{anyhow, bail, ensure, Context, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut, Txid};
use lngap_blackjack as bj;
use lngap_blackjack::{action, phase, status, Commitments, Share, State, K as POSITIONS};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, PresignedTx, Role};
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

/// The house's cheat for its next move (the presenter's console).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Mode {
    Honest,
    /// The next card the house deals is one rank off.
    WrongCard,
    /// In the dealer phase, draw one card past 17.
    DrawAt17,
    /// In the dealer phase, stop below 17.
    StandOn16,
    /// Never reveal (a stall): the player's claim wins.
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

/// A confirmed graph transaction's output, by label.
#[derive(Clone, Debug)]
struct Live {
    height: u32,
    op: OutPoint,
    prev: TxOut,
}

/// A sealed entry, decoded.
struct Decoded {
    state: State,
    word0_ok: bool,
    signed: bool,
    strings: Option<Vec<Vec<u8>>>,
}

pub struct Player {
    me: Role,
    store: Store,
    rt: Regtest,
    keys: PartyKeys,
    ks: KeyStore,
    pubs: [PartyPubKeys; 2],
    params: ChannelParams,
    vparams: VenueParams,
    registry: Registry,
    inst: PosInstance,
    commits: Commitments,
    /// My sixteen shares (secret until revealed).
    shares: Vec<Share>,
    /// Revealed strings, by (whose, position): mine and the counterparty's
    /// (read off its sealed entries).
    strings: BTreeMap<(u8, usize), Vec<u8>>,
    their_state_keys: HashMap<u32, WotsPublic>,
    graph: Vec<PresignedTx>,
    funded_height: u32,
    blocks: BTreeMap<u32, SealedBlock>,
    seen_seals: BTreeSet<String>,
    flags: BTreeMap<u32, Vec<Option<SecretKey>>>,
    pending: Option<(u32, String, usize, u32)>,
    /// The hand after the last valid sealed move, and its depth.
    state: State,
    depth: u32,
    bad_slots: BTreeMap<u32, String>,
    late_slots: BTreeSet<u32>,
    rogue_slots: BTreeSet<u32>,
    scanned: u32,
    live: BTreeMap<String, Live>,
    spent: HashMap<OutPoint, (Txid, u32)>,
    reveals: BTreeMap<String, WotsSig>,
    log: Vec<String>,
    // ----- the house -----
    mode: Mode,
    autopilot: bool,
    /// Labels (and runtime actions) the autopilot already broadcast.
    done: BTreeSet<String>,
}

fn whose(r: Role) -> u8 {
    r.idx() as u8
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

    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] }
    }

    fn skel(&self, label: &str) -> Result<&PresignedTx> {
        self.graph.iter().find(|p| p.label == label).ok_or_else(|| anyhow!("no skeleton {label}"))
    }

    fn height(&self) -> u32 {
        self.rt.height().unwrap_or(0)
    }

    fn due(&self, d: u32) -> u32 {
        self.inst.due(d)
    }

    fn rel(&self, t: u32) -> i64 {
        i64::from(t) - i64::from(self.inst.t0)
    }

    fn claim_wait(&self, d: u32) -> Option<String> {
        let at = self.inst.claim_from(d);
        let mtp = self.rt.mtp().unwrap_or(0);
        let h = self.height();
        let csv = self.funded_height + u32::from(self.params.to_self_delay);
        if mtp <= at {
            return Some(format!("its lock is median-time-past > t+{}s; MTP is t+{}s (it trails the clock by ~6 blocks)", self.rel(at), self.rel(mtp)));
        }
        if h < csv {
            return Some(format!("the contract output's delay: from height {csv} ({} blocks to go)", csv - h));
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

    // ============ setup ============

    pub fn open(dir: PathBuf, me: Role, max_depth: u32) -> Result<Player> {
        let store = Store::new(dir);
        let who = side(me);
        let them = side(me.other());
        println!("{who}: waiting for the venue's node...");
        let node = wait_for(|| store.read::<NodeInfo>(Store::node()))?;
        let rt = Regtest::attach(&PathBuf::from(node.datadir))?;
        println!("{who}: waiting for the venue's registry...");
        let registry: Registry = wait_for(|| store.read(Store::registry()))?;

        let label = format!("blackjack-venue/{}", me.name());
        let keys = PartyKeys::from_seed(me, Seed::from_label(&label));
        let mut ks = KeyStore::new(Seed::from_label(&format!("{label}-ks")));
        let mine = instance::gen_pos_keys(&mut ks, me, CONTRACT_ID, 1, max_depth, Game::Blackjack)?;
        // my shares: fresh randomness every hand
        let mut rng = rand::rngs::StdRng::from_entropy();
        let shares: Vec<Share> = (0..POSITIONS).map(|_| Share::random(&mut rng)).collect();
        let my_commits: Vec<String> = shares.iter().map(|s| hex::encode(s.commitment())).collect();
        let my_offer = Offer { pubs: keys.public(), keys: mine.clone(), commits: my_commits };
        store.write(&Store::offer(me), &my_offer)?;
        println!("{who}: offer published (keys and sixteen share commitments); waiting for the {them}'s...");
        let theirs: Offer = wait_for(|| store.read(&Store::offer(me.other())))?;
        let their_state_keys = theirs.keys.iter().filter_map(|(d, o)| o.state.clone().map(|k| (*d, k))).collect();
        let merged = instance::collect_keys(&mine, &theirs.keys, max_depth)?;
        let mut pubs = [keys.public(), keys.public()];
        pubs[me.other().idx()] = theirs.pubs.clone();
        let commits = match me {
            Role::User => commitments(&my_offer, &theirs)?,
            Role::Hub => commitments(&theirs, &my_offer)?,
        };

        let params = ChannelParams { presign_fee: Amount::from_sat(FEE_SAT), ..ChannelParams::regtest(Amount::from_sat(400_000)) };
        let vparams: VenueParams = wait_for(|| store.read(Store::params()))?;
        let build = |c: &ContractJson| -> Result<PosInstance> {
            let clock = GameClock { t0: c.t0, ell: c.ell, margin: c.margin };
            PosInstance::new(CONTRACT_ID, Amount::from_sat(c.value), c.deadline, GAME_ID, Game::Blackjack, clock, merged.clone(), registry.clone())?
                .with_deposit(Amount::from_sat(c.deposit))?
                .with_commitments(commits.clone())
        };
        let funded: FundedJson = if me == Role::User {
            let t0 = unix_now() + vparams.start_secs;
            let deadline = t0 + (max_depth + 1) * vparams.ell + vparams.margin + 7 * 24 * 3600;
            let value = POT_SAT + 2 * vparams.deposit;
            let mut c = ContractJson { spk: String::new(), value, deadline, t0, ell: vparams.ell, margin: vparams.margin, deposit: vparams.deposit };
            let probe = build(&c)?;
            let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
            c.spk = hex::encode(probe.tree(&ctx)?.script_pubkey().as_bytes());
            store.write(Store::contract(), &c)?;
            println!("{who}: contract proposed ({value} sat: a {POT_SAT} sat pot and a {} sat dispute deposit each; move 1 due in {}s, a move every {}s); waiting for the venue to fund it...", vparams.deposit, vparams.start_secs + vparams.ell, vparams.ell);
            wait_for(|| store.read(Store::funded()))?
        } else {
            println!("{who}: waiting for the Player's contract and the venue's funding...");
            wait_for(|| store.read(Store::funded()))?
        };
        let contract: ContractJson = wait_for(|| store.read(Store::contract()))?;
        let inst = build(&contract)?;
        let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
        let tree = inst.tree(&ctx)?;
        ensure!(hex::encode(tree.script_pubkey().as_bytes()) == funded.spk, "the funded output is not the contract we agreed");
        let op = OutPoint { txid: funded.txid.parse()?, vout: funded.vout };
        let prev = TxOut { value: Amount::from_sat(funded.value), script_pubkey: tree.script_pubkey() };
        print!("{who}: building and signing the pre-signed graph... ");
        std::io::stdout().flush()?;
        let t = std::time::Instant::now();
        let mut graph = inst.graph(&ctx, op, &prev)?;
        let mut mine_sigs = SigsJson::new();
        for p in graph.iter_mut() {
            match p.sign_as(me, &keys.payment)? {
                lngap_channel::GraphSig::Full(s) => {
                    mine_sigs.insert(p.label.clone(), hex::encode(s.as_ref()));
                }
                lngap_channel::GraphSig::Adaptor(_) => bail!("no adaptor pre-signatures in this graph"),
            }
        }
        println!("{} transactions in {:.1}s", graph.len(), t.elapsed().as_secs_f64());
        store.write(&Store::sigs(me), &mine_sigs)?;
        println!("{who}: signatures published; waiting for the {them}'s...");
        let theirs_sigs: SigsJson = wait_for(|| store.read(&Store::sigs(me.other())))?;
        for p in graph.iter_mut() {
            let s = theirs_sigs.get(&p.label).ok_or_else(|| anyhow!("the {them} did not sign {}", p.label))?;
            let sig = Signature::from_slice(&hex::decode(s)?)?;
            p.add_sig(me.other(), lngap_channel::GraphSig::Full(sig), &pubs).with_context(|| format!("the {them}'s signature on {}", p.label))?;
        }
        store.write(&Store::ready(me), &serde_json::json!({ "ready": true }))?;
        let t1 = i64::from(contract.t0 + contract.ell) - i64::from(unix_now());
        println!("{who}: every skeleton is fully signed. The Player deals first; move 1 is due in {t1}s.");
        Ok(Player {
            me,
            store,
            rt,
            keys,
            ks,
            pubs,
            params,
            vparams,
            registry,
            inst,
            commits,
            shares,
            strings: BTreeMap::new(),
            their_state_keys,
            graph,
            funded_height: funded.height,
            blocks: BTreeMap::new(),
            seen_seals: Default::default(),
            flags: BTreeMap::new(),
            pending: None,
            state: State::initial(),
            depth: 0,
            bad_slots: BTreeMap::new(),
            late_slots: Default::default(),
            rogue_slots: Default::default(),
            scanned: funded.height - 1,
            live: BTreeMap::new(),
            spent: HashMap::new(),
            reveals: BTreeMap::new(),
            log: Vec::new(),
            mode: Mode::Honest,
            autopilot: me == Role::Hub,
            done: BTreeSet::new(),
        })
    }

    // ============ the venue and the chain, as seen ============

    pub fn sync(&mut self) -> Result<()> {
        let mut new: Vec<BlockJson> = Vec::new();
        for p in self.store.list(Store::seals_dir())? {
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
            let block = b.to_block()?;
            self.on_seal(&b, block)?;
        }
        for d in 1..=self.vparams.max_depth {
            if self.flags.contains_key(&d) {
                continue;
            }
            if let Some(f) = self.store.read::<FlagsJson>(&Store::flags(d))? {
                let f = flags_from_json(&f)?;
                let n = f.iter().filter(|x| x.is_some()).count();
                self.flags.insert(d, f);
                self.say(format!("venue: move {d} was due at t+{}s with no valid seal — {n} of {K} members flagged it", self.rel(self.due(d))));
            }
        }
        if let Some((d, entry, to, at)) = self.pending.clone() {
            let now = unix_now();
            if self.blocks.contains_key(&d) {
                self.pending = None;
            } else if now > self.due(d) {
                self.say(format!("my move {d} was not sealed by its due time t+{}s: I am stalled at {d}", self.rel(self.due(d))));
                self.pending = None;
            } else if now >= at + self.vparams.backoff {
                let next = (to + 1) % self.registry.n();
                self.say(format!("no seal of my move {d} from member {to} after {}s: resubmitting to member {next}", self.vparams.backoff));
                self.send(d, &entry, next)?;
            }
        }
        let h = self.height();
        while self.scanned < h {
            self.scanned += 1;
            let txs = self.rt.block_txs(self.scanned)?;
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

    /// Decode a sealed entry: the head, the signature, the share strings.
    fn decode(&self, slot: u32, entry: &[u8]) -> Option<Decoded> {
        if entry.len() < 48 {
            return None;
        }
        let head: [u8; 48] = entry[..48].try_into().ok()?;
        let mover = instance::mover_at(slot);
        let key = if mover == self.me { self.ks.wots_public(&instance::state_label(CONTRACT_ID, 1, slot)).ok()? } else { self.their_state_keys.get(&slot)?.clone() };
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
            Some(self.shares[k].string.clone())
        } else {
            self.strings.get(&(who, k)).cloned()
        }
    }

    /// The native predicates that fire on (prior, new) at `slot`, with the
    /// witness strings each needs. `wrong_slot` included.
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
                self.say(format!("venue: move {slot}: a SECOND, different head sealed by member {by} (t+{when}s) — an equivocation at depth {slot}"));
            }
            return Ok(());
        }
        if b.late {
            self.late_slots.insert(slot);
            self.say(format!("venue: move {slot} sealed LATE by member {by} at t+{when}s: the members' flags stand"));
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
        // the declared reveals: record the strings, check they open
        let n = dec.state;
        let strings = dec.strings.unwrap_or_default();
        let range: Vec<usize> = bj::revealed(&n).filter(|k| *k < POSITIONS).collect();
        let mut opened = strings.len() == range.len();
        for (k, s) in range.iter().zip(strings.iter()) {
            opened &= bj::open(s) >= 0 && bj::commit(s) == *self.commits.of(mover == Role::User, *k);
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
            self.say(format!("venue: move {slot} sealed out of sequence (the hand is at depth {})", self.depth));
            return Ok(());
        }
        let head = block.header.head();
        let firing = self.predicates(slot, &self.state, &head, dec.word0_ok);
        if !firing.is_empty() {
            let names: Vec<String> = firing.iter().map(|(n, _)| n.clone()).collect();
            self.bad_slots.insert(slot, names.join(", "));
            self.say(format!("venue: move {slot} sealed the {mover_s}'s {} — NOT a valid move ({}); the absence claim and the disprove family apply", action_ui(n.action), names.join(", ")));
            return Ok(());
        }
        self.state = n;
        self.depth = slot;
        self.say(format!("venue: move {slot} sealed by member {by} at t+{when}s: the {mover_s} — {}", self.describe(slot)));
        Ok(())
    }

    /// What move `slot` did to the hand (the current state).
    fn describe(&self, slot: u32) -> String {
        let s = &self.state;
        let cards = |ps: &[usize]| ps.iter().filter(|k| s.dealt(**k)).map(|k| bj::rank_name(s.cards[*k])).collect::<Vec<_>>().join(" ");
        match s.action {
            action::DEAL => "DEAL: the player's shares of the first three cards".into(),
            action::HIT => format!("HIT: the player's share of card {}", s.np),
            action::STAND => format!("STAND on {}: the player's shares of the hole and every draw", s.player_total()),
            action::ACK => format!("ACK: {} (the hand is closed)", status_ui(s.status)),
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
                let _ = slot;
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

    /// The prior state of the tuple parked at `d`.
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

    /// The disprove predicates that fire on the tuple parked at `d`.
    fn firing(&self, d: u32) -> Vec<(String, Vec<Vec<u8>>)> {
        let Some(new) = self.blocks.get(&d) else { return vec![] };
        if d >= 2 && !self.blocks.contains_key(&(d - 1)) {
            return vec![];
        }
        let head = new.header.head();
        let word0_ok = head[0..4] == bj::word0(GAME_ID, d, whose(instance::mover_at(d))).to_be_bytes();
        self.predicates(d, &self.prior_of(d), &head, word0_ok)
    }

    /// R of the tuple parked at `d` (the outcome code).
    fn r_of(&self, d: u32) -> Option<u8> {
        let b = self.blocks.get(&d)?;
        Some(bj::resolution(&State::from_head(&b.header.head()), whose(instance::mover_at(d))))
    }

    fn wins(&self, code: u8) -> bool {
        code == 2 || code == whose(self.me)
    }

    fn actions(&self) -> Vec<ActionView> {
        let h = self.height();
        let now = unix_now();
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let delta = self.params.delta;
        let delta2 = self.params.delta + self.params.delta_prime;
        let mut v = Vec::new();
        // the game's own moves (the player's buttons)
        if self.me == Role::User {
            let s = &self.state;
            let can = mover == self.me && now <= self.due(d) && self.pending.as_ref().is_none_or(|p| p.0 != d);
            let why = if mover != self.me { format!("the House to move (move {d})") } else if now > self.due(d) { format!("move {d} was due at t+{}s", self.rel(self.due(d))) } else { format!("move {d} due in {}s", i64::from(self.due(d)) - i64::from(now)) };
            v.push(if can && s.phase == phase::START { ActionView::ok("deal", &why) } else { ActionView::no("deal", if s.phase == phase::START { &why } else { "dealt" }) });
            let decide = can && s.phase == phase::DECIDE;
            v.push(if decide && bj::can_hit(s) { ActionView::ok("hit", &format!("you have {}", s.player_total())) } else { ActionView::no("hit", if s.phase == phase::DECIDE { &why } else { "not your decision" }) });
            v.push(if decide { ActionView::ok("stand", &format!("stand on {}", s.player_total())) } else { ActionView::no("stand", if s.phase == phase::DECIDE { &why } else { "not your decision" }) });
            v.push(if can && bj::can_ack(s) { ActionView::ok("ack", &format!("{}: close the hand so the House has no move left", status_ui(s.status))) } else { ActionView::no("ack", "only after a hand you won or pushed") });
        }
        // claim
        let claimable = (1..=d)
            .filter(|s| instance::mover_at(*s) != self.me && self.due(*s) < now)
            .find(|s| {
                let untimely = self.blocks.get(s).map(|_| self.bad_slots.contains_key(s) || self.late_slots.contains(s) || self.rogue_slots.contains(s)).unwrap_or(true);
                let claimed = self.live.contains_key(&format!("absent_{s}")) || self.mempool_labels().contains(&format!("absent_{s}"));
                untimely && !claimed
            });
        v.push(match claimable {
            None => ActionView::no("claim", "nothing to claim: every due move of the opponent's is sealed and valid, or claimed"),
            Some(s) => {
                let why = if self.late_slots.contains(&s) { format!("move {s} was sealed only LATE") } else if let Some(w) = self.bad_slots.get(&s) { format!("move {s} is not a valid move ({w})") } else { format!("the {} did not publish move {s} by t+{}s", side(instance::mover_at(s)), self.rel(self.due(s))) };
                match self.claim_wait(s) {
                    Some(wait) => ActionView::no("claim", &format!("{why}: not yet — {wait}")).with_cmd(&format!("claim {s}")),
                    None => ActionView::ok("claim", &why).with_cmd(&format!("claim {s}")),
                }
            }
        });
        // counter / refute
        let against_me: Vec<(String, u32)> = self.live_claims().into_iter().filter(|(_, dd)| instance::mover_at(*dd) == self.me).collect();
        match against_me.first() {
            Some((base, dd)) => {
                let can_counter = !base.contains("counter") && *dd >= 2;
                v.push(if can_counter { ActionView::ok("counter", &format!("`{base}`: say the claimant did not move at {}", dd - 1)) } else { ActionView::no("counter", "no counter on a counter, nor at depth 1") });
                // a refutation needs only a seal of my move: an invalid one
                // (a cheat) can still be refuted with, and then disproved
                v.push(match (self.blocks.contains_key(dd), self.bad_slots.get(dd)) {
                    (true, None) => ActionView::ok("refute", &format!("`{base}`: the venue attested your move {dd}")),
                    (true, Some(why)) => ActionView::ok("refute", &format!("`{base}`: the venue attested your move {dd}, which is NOT valid ({why}): the claimant can disprove it")),
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
                    v.push(if firing.is_empty() { ActionView::no("disprove", &format!("`{base}` (move {dd}): the parked move is valid, nothing fires")) } else { ActionView::ok("disprove", &format!("`{base}` (move {dd}): {}", firing.join(", "))) });
                    v.push(if flags >= self.registry.threshold as usize { ActionView::ok("timely", &format!("{flags} of {K} members flagged move {dd}")) } else { ActionView::no("timely", &format!("{flags} of {K} flags known for move {dd}")) });
                }
            }
            None => {
                v.push(ActionView::no("disprove", "no live refutation against you"));
                v.push(ActionView::no("timely", "no live refutation against you"));
            }
        }
        // split: a refuted output whose R favours me (either party may
        // broadcast the ungated split, D57), or my unanswered claim
        let mut split = ActionView::no("split", "nothing of yours to split");
        if let Some((base, dd, code)) = self.live_refuted().into_iter().filter_map(|(b, dd)| self.r_of(dd).map(|c| (b, dd, c))).find(|(_, _, c)| self.wins(*c)) {
            let open = self.window_open(&format!("{base}/refute"), delta2).unwrap_or(0);
            split = if h >= open { ActionView::ok("split", &format!("`{base}` (move {dd}): R = {}", outcome_ui(code))) } else { ActionView::no("split", &format!("`{base}`: R = {}; the split opens at height {open} ({} blocks to go)", outcome_ui(code), open - h)) };
        } else if let Some((base, _)) = self.live_claims().into_iter().find(|(_, dd)| instance::mover_at(*dd) != self.me) {
            let open = self.window_open(&base, delta).unwrap_or(0);
            split = if h >= open { ActionView::ok("split", &format!("your claim `{base}` is unanswered: the timeout split")) } else { ActionView::no("split", &format!("your claim `{base}`: the timeout opens at height {open} ({} blocks to go)", open - h)) };
        }
        v.push(split);
        v
    }

    // ============ the house's autopilot ============

    /// Play the house: reveal when due, answer disputes honestly.
    fn pilot(&mut self) -> Result<()> {
        let d = self.depth + 1;
        let now = unix_now();
        // my move: the reveal the player's sealed move calls for
        if instance::mover_at(d) == self.me && now <= self.due(d) && self.pending.is_none() && !self.blocks.contains_key(&d) && self.mode != Mode::Withhold && matches!(self.state.phase, phase::DEALT | phase::HIT | phase::STOOD) {
            self.reveal()?;
        }
        let pool = self.mempool_labels();
        let fresh = |me: &Self, key: &str| !me.done.contains(key);
        for a in self.actions() {
            if !a.enabled {
                continue;
            }
            match a.name.as_str() {
                "refute" => {
                    let key = format!("refute:{}", a.hint);
                    if fresh(self, &key) && !pool.iter().any(|l| l.ends_with("/refute")) {
                        self.done.insert(key);
                        self.refute()?;
                    }
                }
                "claim" if self.mode != Mode::Withhold => {
                    let key = format!("claim:{}", a.cmd);
                    if fresh(self, &key) {
                        self.done.insert(key);
                        let dd = a.cmd.split_whitespace().nth(1).and_then(|x| x.parse().ok());
                        self.claim(dd)?;
                    }
                }
                "counter" => {
                    // counter only a claim that steals: the claimant's last
                    // state is terminal with R not the claimant's, or the
                    // claimant never validly moved there
                    if let Some((base, dd)) = self.live_claims().into_iter().find(|(b, dd)| !b.contains("counter") && instance::mover_at(*dd) == self.me && *dd >= 2) {
                        let prev = dd - 1;
                        let claimant_won = self.r_of(prev).is_some_and(|c| c == whose(self.me.other()));
                        let steals = !self.blocks.contains_key(&dd) && (self.bad_slots.contains_key(&prev) || !self.blocks.contains_key(&prev) || !claimant_won);
                        let key = format!("counter:{base}");
                        if steals && fresh(self, &key) {
                            self.done.insert(key);
                            self.counter(Some(dd))?;
                        }
                    }
                }
                "disprove" => {
                    let key = format!("disprove:{}", a.hint);
                    if fresh(self, &key) {
                        self.done.insert(key);
                        self.disprove(None)?;
                    }
                }
                "timely" => {
                    let key = format!("timely:{}", a.hint);
                    if fresh(self, &key) {
                        self.done.insert(key);
                        self.timely()?;
                    }
                }
                "split" => {
                    let key = format!("split:{}", a.hint);
                    if fresh(self, &key) {
                        self.done.insert(key);
                        self.split()?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// The house's reveal for the next depth, with the mode's cheat.
    fn reveal(&mut self) -> Result<()> {
        let d = self.depth + 1;
        let prior = self.state;
        let card_of = |me: &Self, k: usize| -> Result<u8> {
            let a = me.strings.get(&(0, k)).ok_or_else(|| anyhow!("the player's share {k} is not known"))?;
            let a = bj::open(a);
            ensure!((0..=12).contains(&a), "the player's share {k} is out of range");
            Ok(bj::card(a as u8, me.shares[k].value))
        };
        // every card this reveal can need, from both shares
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
                if n.phase == phase::DONE || prior.phase == phase::HIT {
                    n.status = if prior.phase == phase::STOOD { bj::showdown(&n) } else if n.player_total() > 21 { status::HOUSE } else { status::OPEN };
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

    /// Sign the head for `n` at depth `d`, attach my strings for the
    /// positions it reveals, and send it to the designated sealer.
    fn submit(&mut self, d: u32, n: &State) -> Result<()> {
        let head = n.head(GAME_ID, d, whose(self.me));
        let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &blackjack::auth_message(&head)).map_err(|e| anyhow!("signing (a depth's state key signs once): {e}"))?;
        let strings: Vec<Vec<u8>> = bj::revealed(n).filter(|k| *k < POSITIONS).map(|k| self.shares[k].string.clone()).collect();
        let refs: Vec<&[u8]> = strings.iter().map(|v| v.as_slice()).collect();
        let entry = blackjack::entry(&head, &sig, &refs);
        let to = lngap_pos::rotation(CONTRACT_ID, d, self.registry.n());
        self.send(d, &hex::encode(entry), to)
    }

    fn play(&mut self, what: &str) -> Result<()> {
        ensure!(self.me == Role::User, "the House plays itself");
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
        self.say(format!("submitted move {d}: {} to member {}", what.to_uppercase(), lngap_pos::rotation(CONTRACT_ID, d, self.registry.n())));
        Ok(())
    }

    fn send(&mut self, d: u32, entry: &str, to: usize) -> Result<()> {
        let at = unix_now();
        let name = format!("{}/{}.json", Store::inbox_dir(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
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
        let d = d.unwrap_or(self.depth + 1);
        ensure!(instance::mover_at(d) != self.me, "depth {d} is your own move");
        let label = format!("absent_{d}");
        let [sh, su] = self.sigs22(&label)?;
        let p = self.skel(&label)?;
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&[sh, su], &p.leaf.script, &p.control_block);
        if let Some(wait) = self.claim_wait(d) {
            bail!("not broadcast: `absent_{d}` is not mineable yet — {wait}");
        }
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
        let new = self.blocks.get(&d).ok_or_else(|| anyhow!("nothing is sealed for move {d}: nothing to refute with"))?.clone();
        let new_head = new.header.head();
        let msg = self.parked_message(d)?;
        let pair_sig = self.ks.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).map_err(|e| anyhow!("{e}"))?;
        let auth = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &blackjack::auth_message(&new_head)).map_err(|e| anyhow!("{e}"))?;
        let sign_at = |b: &SealedBlock| -> Vec<Vec<u8>> { (0..HEAD_CHUNKS).map(|j| sig_bytes(&Keypair::from_secret_key(SECP256K1, &b.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect() };
        let sigs_new = sign_at(&new);
        let mut w = if d >= 2 {
            let prior = self.blocks.get(&(d - 1)).ok_or_else(|| anyhow!("no seal for move {}", d - 1))?;
            refute::refute_witness_pair(&sign_at(prior), &sigs_new, &pair_sig, &[&auth])
        } else {
            refute::refute_witness(&sigs_new, &pair_sig, &auth)
        };
        w.extend(proposer_witness(sig_bytes(&Keypair::from_secret_key(SECP256K1, &new.proposer_secret), &tx, &prev, &leaf), new.proposer));
        w.push(sig_bytes(&self.keys.payment, &tx, &prev, &leaf));
        let mut tx = tx;
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.reveals.insert(base.clone(), pair_sig);
        self.say(format!("refuting `{base}`: the venue attested my move {d} (sealed by member {})", new.proposer));
        self.broadcast(&tx, &format!("`{label}`"))
    }

    fn payout_tx(&self, base: &str, d: u32, leaf_name: &str) -> Result<(Transaction, TxOut, ScriptBuf, bitcoin::taproot::ControlBlock)> {
        let l = self.live.get(&format!("{base}/refute")).ok_or_else(|| anyhow!("no live refutation on `{base}`"))?.clone();
        let tree = self.inst.refuted_tree(&self.ctx(), d)?;
        let leaf = tree.leaf(leaf_name)?.clone();
        let tx = build_spend(l.op, &leaf.timelock, vec![TxOut { value: l.prev.value - self.params.presign_fee, script_pubkey: self.pubs[self.me.idx()].payout_spk.clone() }]);
        Ok((tx, l.prev, leaf.script, tree.control_block(leaf_name)?))
    }

    fn disprove(&mut self, which: Option<String>) -> Result<()> {
        let (base, d) = self.live_refuted().into_iter().find(|(_, d)| instance::mover_at(*d) != self.me).ok_or_else(|| anyhow!("no live refutation against you on the chain"))?;
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
        w.push(sig_bytes(&self.keys.payment, &tx, &prev, &leaf));
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.say(format!("disproving the parked move {d} of `{base}`: {name}"));
        self.broadcast(&tx, &leaf_name)
    }

    fn timely(&mut self) -> Result<()> {
        let (base, d) = self.live_refuted().into_iter().find(|(_, d)| instance::mover_at(*d) != self.me).ok_or_else(|| anyhow!("no live refutation against you"))?;
        let scalars = self.flags.get(&d).cloned().ok_or_else(|| anyhow!("no flags known for move {d}"))?;
        self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta)?, "not_timely")?;
        let (mut tx, prev, leaf, control) = self.payout_tx(&base, d, "not_timely")?;
        let w = not_timely_witness(&tx, 0, std::slice::from_ref(&prev), &leaf, &self.keys.payment, &scalars);
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.say(format!("killing the refutation on `{base}` as NOT TIMELY: {} of {K} members flagged move {d}", scalars.iter().filter(|x| x.is_some()).count()));
        self.broadcast(&tx, "not_timely")
    }

    fn split(&mut self) -> Result<()> {
        // a refuted output whose R favours me: the ungated checked split
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
            let reveal = self.ks.reveal_uint(&instance::ccode_label(CONTRACT_ID, 1, d), u32::from(code))?;
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

    fn balance(&self) -> Result<String> {
        let spk = &self.pubs[self.me.idx()].payout_spk;
        Ok(format!("the {}'s payout address holds {} sat", side(self.me), self.rt.balance_of(spk)?.to_sat()))
    }

    /// Everything the pages show.
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
        let live = self.live.iter().map(|(label, l)| LiveView { label: ui(label), height: l.height, spent: self.spent.contains_key(&l.op), value_sat: l.prev.value.to_sat() }).collect();
        let disproves = self
            .live_refuted()
            .into_iter()
            .find(|(_, dd)| instance::mover_at(*dd) != self.me)
            .map(|(_, dd)| self.firing(dd).into_iter().map(|(name, _)| DisproveView { name, fires: true }).collect())
            .unwrap_or_default();
        let balance_sat = self.rt.balance_of(&self.pubs[self.me.idx()].payout_spk).map(|a| a.to_sat()).unwrap_or(0);
        let d = self.depth;
        Snapshot {
            role: self.me.name().into(),
            height: self.height(),
            mtp: self.rel(self.rt.mtp().unwrap_or(0)),
            now: self.rel(unix_now()),
            ell: self.inst.ell,
            backoff: self.vparams.backoff,
            margin: self.inst.margin,
            next_due: self.rel(self.due(d + 1)),
            depth: d,
            to_move: side(instance::mover_at(d + 1)).into(),
            phase: s.phase,
            status: status_ui(s.status).into(),
            terminal: s.is_terminal(),
            player_cards,
            player_total: if dealt(0) { s.player_total() } else { 0 },
            dealer_cards,
            dealer_total: if dealt(bj::HOLE) { Some(s.dealer_total()) } else { None },
            n: self.registry.n(),
            threshold: self.registry.threshold,
            slots,
            live,
            actions: self.actions(),
            disproves,
            mempool: self.mempool_labels().iter().map(|l| ui(l)).collect(),
            balance_sat,
            mode: self.mode,
            autopilot: self.autopilot,
            log: self.log.iter().rev().take(60).rev().cloned().collect(),
        }
    }
}

fn base_depth(base: &str) -> Result<u32> {
    if let Some(d) = base.strip_prefix("absent_").and_then(|s| s.strip_suffix("/counter")).and_then(|s| s.parse::<u32>().ok()) {
        return Ok(d - 1);
    }
    base.strip_prefix("absent_").and_then(|s| s.parse::<u32>().ok()).ok_or_else(|| anyhow!("not a claim base: {base}"))
}

fn wait_for<T>(mut f: impl FnMut() -> Result<Option<T>>) -> Result<T> {
    loop {
        if let Some(v) = f()? {
            return Ok(v);
        }
        std::thread::sleep(Duration::from_millis(500));
    }
}

const HELP: &str = "commands:
  status | s          the hand, the venue, what is due
  deal | hit | stand | ack
                      the player's moves
  mode honest|wrongcard|drawat17|standon16|withhold
                      the house's cheat for its next move (withhold: never reveal)
  autopilot on|off    the house plays itself (default on)
  claim [d] | counter [d] | refute | disprove [name] | timely | split
                      disputes
  balance             your payout address
  quit";

impl Player {
    fn status(&mut self) -> Result<String> {
        let s = self.state;
        let mut out = format!("--- {} | t+{}s | height {} | depth {} | the {} to move, move {} due t+{}s\n", side(self.me), self.rel(unix_now()), self.height(), self.depth, side(instance::mover_at(self.depth + 1)), self.depth + 1, self.rel(self.due(self.depth + 1)));
        let snap = self.snapshot();
        out += &format!("    player: {} ({})   dealer: {}{}   {}\n", snap.player_cards.join(" "), snap.player_total, snap.dealer_cards.join(" "), snap.dealer_total.map(|t| format!(" ({t})")).unwrap_or_default(), status_ui(s.status));
        for (d, why) in &self.bad_slots {
            out += &format!("    move {d}: not a valid move ({why})\n");
        }
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
            "deal" | "hit" | "stand" | "ack" => self.play(cmd).map(|_| String::new()),
            "mode" => {
                let m = arg.as_deref().and_then(Mode::parse).ok_or_else(|| anyhow!("mode honest|wrongcard|drawat17|standon16|withhold"))?;
                ensure!(self.me == Role::Hub, "the Player does not cheat in this demo");
                self.mode = m;
                Ok(format!("the House's next move: {m:?}"))
            }
            "autopilot" => {
                self.autopilot = arg.as_deref() != Some("off");
                Ok(format!("autopilot {}", if self.autopilot { "on" } else { "off" }))
            }
            "claim" => self.claim(arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "counter" => self.counter(arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "refute" => self.refute().map(|_| String::new()),
            "disprove" => self.disprove(arg).map(|_| String::new()),
            "timely" => self.timely().map(|_| String::new()),
            "split" => self.split().map(|_| String::new()),
            "balance" => self.balance(),
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
        ActionView { name: name.into(), enabled: true, hint: hint.into(), cmd: name.into() }
    }
    fn no(name: &str, hint: &str) -> ActionView {
        ActionView { name: name.into(), enabled: false, hint: hint.into(), cmd: name.into() }
    }
    fn with_cmd(mut self, cmd: &str) -> ActionView {
        self.cmd = cmd.into();
        self
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
    pub log: Vec<String>,
}
