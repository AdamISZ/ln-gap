//! One game in the session: its negotiation (per-game keys, the venue's
//! registry, the terms, the channel update that adds it), its view of the
//! venue (seals, flags, the mover's fallback), its settlement, and its
//! disputes after a force-close (claims, counters, refutations, disproves,
//! timeliness, splits) off the confirmed commitment version's graph. What
//! is game-specific comes from [`Rules`].

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use anyhow::{anyhow, bail, ensure, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut, Txid};
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::protocol::ChainEvent;
use lngap_channel::{ContractOutput, PresignedTx, Role};
use lngap_contract::Payout;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_pos::graph::{not_timely_witness, proposer_witness};
use lngap_pos::instance::{self, Game, GameClock, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNKS, HEAD_CHUNK_START};
use lngap_pos::{Registry, SealedBlock};
use serde::Serialize;

use crate::session::{sat, Session};
use crate::store::*;

/// A game's rules as the session needs them.
pub trait Rules {
    /// The game's variant (the per-depth state key's size).
    fn game(&self) -> Game;
    /// The mover's state-key message for a head (what an entry's signature
    /// signs and the refutation's authorship fragment checks).
    fn auth_message(&self, head: &[u8; 48]) -> Vec<u8>;
    /// Start game `id`: my private material, and the public part of my
    /// offer (a JSON value both parties' instances are built from).
    fn begin(&mut self, id: u32) -> serde_json::Value;
    /// Build the game's instance (both parties and the venue build it the
    /// same way) from both offers' extras.
    fn instance(&self, inst: PosInstance, user_extra: &serde_json::Value, hub_extra: &serde_json::Value) -> Result<PosInstance>;
    /// Judge the signed, in-sequence entry sealed at `slot`: on `Ok`, apply
    /// it to my view of the game and describe it; on `Err`, why it is not a
    /// valid move. `tail` is the entry after the head and the signature.
    fn judge(&mut self, h: &Hand, slot: u32, head: &[u8; 48], tail: &[u8]) -> std::result::Result<String, String>;
    /// The disprove leaves that fire on the tuple parked at `d`, with the
    /// witness elements each needs below the pair reveal.
    fn firing(&self, h: &Hand, d: u32) -> Vec<(String, Vec<Vec<u8>>)>;
    /// R of a parked head at depth `d` (the outcome code).
    fn resolution(&self, head: &[u8; 48], d: u32) -> u8;
    /// My view's result, once the game is over.
    fn result(&self) -> Option<Payout>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Phase {
    Negotiating,
    Opening,
    Playing,
    Settled,
    Disputed,
}

#[derive(Clone, Debug)]
pub struct Live {
    pub height: u32,
    pub op: OutPoint,
    pub prev: TxOut,
}

#[derive(Serialize, Clone, Debug)]
pub struct ActionView {
    pub name: String,
    pub enabled: bool,
    pub hint: String,
    pub cmd: String,
}

impl ActionView {
    pub fn ok(name: &str, hint: &str) -> ActionView {
        ActionView { name: name.into(), enabled: true, hint: hint.into(), cmd: cmd_of(name) }
    }
    pub fn no(name: &str, hint: &str) -> ActionView {
        ActionView { name: name.into(), enabled: false, hint: hint.into(), cmd: cmd_of(name) }
    }
    pub fn with_cmd(mut self, cmd: &str) -> ActionView {
        self.cmd = cmd.into();
        self
    }
}

fn cmd_of(name: &str) -> String {
    match name {
        "new game" | "new hand" => "new".into(),
        "force close" => "force".into(),
        "close channel" => "close".into(),
        "offer draw" => "draw".into(),
        "accept draw" => "accept".into(),
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

fn sig_bytes(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

pub fn outcome_name(code: u8) -> &'static str {
    match code {
        0 => "UserWins",
        1 => "HubWins",
        _ => "Draw",
    }
}

fn base_depth(base: &str) -> Result<u32> {
    if let Some(d) = base.strip_prefix("absent_").and_then(|s| s.strip_suffix("/counter")).and_then(|s| s.parse::<u32>().ok()) {
        return Ok(d - 1);
    }
    base.strip_prefix("absent_").and_then(|s| s.parse::<u32>().ok()).ok_or_else(|| anyhow!("not a claim base: {base}"))
}

/// One game's state in the session (reset for each game).
#[derive(Default)]
pub struct Hand {
    pub id: u32,
    pub phase: Option<Phase>,
    pub inst: Option<Arc<PosInstance>>,
    pub their_state_keys: HashMap<u32, WotsPublic>,
    pub extras: Option<(serde_json::Value, serde_json::Value)>,
    pub blocks: BTreeMap<u32, SealedBlock>,
    seen_seals: BTreeSet<String>,
    pub flags: BTreeMap<u32, Vec<Option<SecretKey>>>,
    pub pending: Option<(u32, String, usize, u32)>,
    /// The deepest valid move.
    pub depth: u32,
    pub bad_slots: BTreeMap<u32, String>,
    pub late_slots: BTreeSet<u32>,
    pub rogue_slots: BTreeSet<u32>,
    pub graph: Vec<PresignedTx>,
    pub live: BTreeMap<String, Live>,
    pub spent: HashMap<OutPoint, (Txid, u32)>,
    pub reveals: BTreeMap<String, WotsSig>,
    /// When I proposed settling this game.
    pub settle_sent: Option<u32>,
    /// Results of finished games, for the page.
    pub results: Vec<String>,
    /// The channel balances while the game was in it (a settlement's
    /// result is the change from these).
    in_play_balances: Option<[Amount; 2]>,
}

impl Hand {
    pub fn due(&self, d: u32) -> u32 {
        self.inst.as_ref().map(|i| i.due(d)).unwrap_or(0)
    }

    pub fn rel(&self, t: u32) -> i64 {
        let t0 = self.inst.as_ref().map(|i| i.t0).unwrap_or(t);
        i64::from(t) - i64::from(t0)
    }

    pub fn inst(&self) -> Result<&PosInstance> {
        self.inst.as_deref().ok_or_else(|| anyhow!("no game in play"))
    }

    pub fn playing(&self) -> bool {
        self.phase == Some(Phase::Playing)
    }

    /// Start game `id` (forgetting the previous one's state): my per-game
    /// keys and the rules' private material; my offer.
    pub fn begin(&mut self, s: &mut Session, rules: &mut dyn Rules, id: u32) -> Result<()> {
        let results = std::mem::take(&mut self.results);
        *self = Hand { id, phase: Some(Phase::Negotiating), results, ..Default::default() };
        let keys = instance::gen_pos_keys(&mut s.ks, s.me, id, 1, s.vparams.max_depth, rules.game())?;
        let extra = rules.begin(id);
        s.store.write(&Store::offer(id, s.me), &Offer { keys, extra })?;
        Ok(())
    }

    /// The user asks the venue for game `id + 1`.
    pub fn request_new(&mut self, s: &mut Session, rules: &mut dyn Rules) -> Result<u32> {
        ensure!(s.me == Role::User, "the user starts games");
        ensure!(s.channel_open(), "the channel is closed");
        ensure!(matches!(self.phase, None | Some(Phase::Settled)), "finish this game first");
        let id = self.id + 1;
        self.begin(s, rules, id)?;
        s.store.write(&Store::request(id), &serde_json::json!({ "game": id }))?;
        Ok(id)
    }

    /// Move the game along: the hub joins a requested game; both build the
    /// instance once the registry, both offers and the terms are in; the
    /// user proposes the terms and the channel update; the phase follows
    /// the channel. `what` names a game in messages ("game", "hand").
    pub fn negotiate(&mut self, s: &mut Session, rules: &mut dyn Rules, what: &str) -> Result<()> {
        if s.me == Role::Hub {
            if let Some(&id) = s.store.games().iter().rev().find(|h| s.store.exists(&Store::request(**h))) {
                if id > self.id && s.channel_open() {
                    self.begin(s, rules, id)?;
                    s.say(format!("{what} {id}: requested; my keys are out"));
                }
            }
        }
        let id = self.id;
        if id == 0 {
            return Ok(());
        }
        if self.inst.is_none() {
            let registry: Option<Registry> = s.store.read(&Store::registry(id))?;
            let (Some(registry), Some(user), Some(hub)) = (registry, s.store.read::<Offer>(&Store::offer(id, Role::User))?, s.store.read::<Offer>(&Store::offer(id, Role::Hub))?) else { return Ok(()) };
            if s.me == Role::User && !s.store.exists(&Store::contract(id)) {
                let t0 = unix_now() + s.vparams.start_secs;
                let deadline = t0 + (s.vparams.max_depth + 1) * s.vparams.ell + s.vparams.margin + 7 * 24 * 3600;
                let c = ContractJson { value: 2 * STAKE_SAT + 2 * s.vparams.deposit, deadline, t0, ell: s.vparams.ell, margin: s.vparams.margin, deposit: s.vparams.deposit };
                s.store.write(&Store::contract(id), &c)?;
            }
            let Some(c) = s.store.read::<ContractJson>(&Store::contract(id))? else { return Ok(()) };
            let keys = instance::collect_keys(&user.keys, &hub.keys, s.vparams.max_depth)?;
            let theirs = if s.me == Role::User { &hub } else { &user };
            self.their_state_keys = theirs.keys.iter().filter_map(|(d, o)| o.state.clone().map(|k| (*d, k))).collect();
            let clock = GameClock { t0: c.t0, ell: c.ell, margin: c.margin };
            let base = PosInstance::new(id, Amount::from_sat(c.value), c.deadline, GAME_ID, rules.game(), clock, keys, registry)?.with_deposit(Amount::from_sat(c.deposit))?;
            let inst = Arc::new(rules.instance(base, &user.extra, &hub.extra)?);
            self.extras = Some((user.extra.clone(), hub.extra.clone()));
            s.instances.insert(id, inst.clone());
            self.inst = Some(inst);
            s.agree_open(id, Amount::from_sat(STAKE_SAT + c.deposit));
            // the counterparty may always concede the game to me
            let mine = if s.me == Role::User { Payout::UserAll } else { Payout::HubAll };
            s.agree_concede(id, self.inst()?.cooperative_payout(mine));
        }
        let in_chan = s.in_channel(id);
        match self.phase {
            Some(Phase::Negotiating) | Some(Phase::Opening) if in_chan => {
                self.phase = Some(Phase::Playing);
                let b = s.balances();
                self.in_play_balances = Some(b);
                s.say(format!("{what} {id} is in the channel (update {}): {} sat at stake; balances {} {} / {} {}. Move 1 is due in {}s", s.chan.current_seq(), sat(self.inst()?.value), s.side(Role::User), sat(b[0]), s.side(Role::Hub), sat(b[1]), i64::from(self.due(1)) - i64::from(unix_now())));
            }
            Some(Phase::Negotiating) if s.me == Role::User && s.store.exists(&Store::registered(id)) && s.idle() && s.channel_open() => {
                let inst = self.inst.clone().ok_or_else(|| anyhow!("no instance"))?;
                let c = Amount::from_sat(STAKE_SAT + s.vparams.deposit);
                let b = s.balances();
                ensure!(b[0] >= c && b[1] >= c, "a side's channel balance cannot cover another {what}");
                self.phase = Some(Phase::Opening);
                s.propose([b[0] - c, b[1] - c], vec![inst as Arc<dyn ContractOutput>])?;
                s.say(format!("{what} {id}: proposing the channel update that adds its contract"));
            }
            Some(Phase::Playing) if !in_chan && s.channel_open() => {
                self.phase = Some(Phase::Settled);
                let b = s.balances();
                let r = self.in_play_balances.map(|a| format!("{} +{}, {} +{}", s.side(Role::User), sat(b[0] - a[0]), s.side(Role::Hub), sat(b[1] - a[1]))).unwrap_or_default();
                self.results.push(format!("{what} {id}: {r}"));
                s.say(format!("{what} {id}: SETTLED in the channel (update {}, no chain transaction: {r}); balances {} {} / {} {}", s.chan.current_seq(), s.side(Role::User), sat(b[0]), s.side(Role::Hub), sat(b[1])));
            }
            _ => {}
        }
        Ok(())
    }

    /// Set what my policy accepts as this game's fold from the rules' result
    /// (or an explicit `payout`, e.g. a resignation or an agreed draw).
    pub fn agree(&self, s: &Session, payout: Payout) -> Result<[Amount; 2]> {
        let pay = self.inst()?.cooperative_payout(payout);
        s.agree_fold(self.id, pay);
        Ok(pay)
    }

    /// Propose removing the game with `payout`.
    pub fn settle(&mut self, s: &mut Session, payout: Payout) -> Result<()> {
        ensure!(self.playing() && s.in_channel(self.id), "no game in the channel to settle");
        ensure!(s.idle(), "a channel update is in flight");
        let pay = self.agree(s, payout)?;
        let b = s.balances();
        s.propose([b[0] + pay[0], b[1] + pay[1]], vec![])?;
        self.settle_sent = Some(unix_now());
        s.say(format!("proposing the channel update that settles it: {} +{}, {} +{}", s.side(Role::User), sat(pay[0]), s.side(Role::Hub), sat(pay[1])));
        Ok(())
    }

    // ============ the venue ============

    /// Read new seals and flags; resubmit an unsealed move of mine.
    pub fn venue(&mut self, s: &mut Session, rules: &mut dyn Rules) -> Result<()> {
        if self.inst.is_none() {
            return Ok(());
        }
        let id = self.id;
        let mut new: Vec<BlockJson> = Vec::new();
        for p in s.store.list(&Store::seals_dir(id))? {
            let key = p.display().to_string();
            if self.seen_seals.contains(&key) {
                continue;
            }
            if let Some(b) = std::fs::read_to_string(&p).ok().and_then(|x| serde_json::from_str::<BlockJson>(&x).ok()) {
                self.seen_seals.insert(key);
                new.push(b);
            }
        }
        new.sort_by_key(|b| (b.sealed_at, b.depth));
        for b in new {
            let block = b.to_block(id)?;
            self.on_seal(s, rules, &b, block);
        }
        for d in 1..=s.vparams.max_depth {
            if self.flags.contains_key(&d) {
                continue;
            }
            if let Some(f) = s.store.read::<FlagsJson>(&Store::flags(id, d))? {
                let f = flags_from_json(&f)?;
                let n = f.iter().filter(|x| x.is_some()).count();
                self.flags.insert(d, f);
                if matches!(self.phase, Some(Phase::Playing) | Some(Phase::Disputed)) {
                    s.say(format!("venue: move {d} was due at {} with no valid seal — {n} of {K} members flagged it", t_rel(self.rel(self.due(d)))));
                }
            }
        }
        if let Some((d, entry, to, at)) = self.pending.clone() {
            let now = unix_now();
            if self.blocks.contains_key(&d) {
                self.pending = None;
            } else if now > self.due(d) {
                s.say(format!("my move {d} was not sealed by its due time: I am stalled at {d}"));
                self.pending = None;
            } else if now >= at + s.vparams.backoff {
                let next = (to + 1) % s.vparams.n;
                s.say(format!("no seal of my move {d} from member {to} after {}s: resubmitting to member {next}", s.vparams.backoff));
                self.send(s, d, &entry, next)?;
            }
        }
        Ok(())
    }

    fn on_seal(&mut self, s: &mut Session, rules: &mut dyn Rules, b: &BlockJson, block: SealedBlock) {
        let slot = b.depth;
        let by = block.proposer;
        let when = self.rel(b.sealed_at);
        if let Some(held) = self.blocks.get(&slot) {
            if held.head() != block.head() {
                s.say(format!("venue: move {slot}: a SECOND, different head sealed by member {by} — an equivocation at depth {slot}"));
            }
            return;
        }
        if b.late {
            self.late_slots.insert(slot);
            s.say(format!("venue: move {slot} sealed LATE by member {by}: the members' flags stand"));
        }
        if b.rogue {
            self.rogue_slots.insert(slot);
        }
        self.blocks.insert(slot, block.clone());
        let mover = instance::mover_at(slot);
        let mover_s = s.side(mover);
        let entry = &block.entry;
        let head = block.header.head();
        // the mover's signature over the head
        let key = if mover == s.me { s.ks.wots_public(&instance::state_label(self.id, 1, slot)).ok() } else { self.their_state_keys.get(&slot).cloned() };
        let n_sig = key.as_ref().map(|k| k.params.total_digits() as usize * 20).unwrap_or(0);
        let signed = key.as_ref().is_some_and(|k| {
            entry.len() >= 48 + n_sig && {
                let sigs: Vec<[u8; 20]> = entry[48..48 + n_sig].chunks(20).map(|x| x.try_into().unwrap()).collect();
                refute::check_entry_sig(k, &rules.auth_message(&head), &sigs)
            }
        });
        if !signed {
            self.bad_slots.insert(slot, "not signed by the mover".into());
            s.say(format!("venue: move {slot} sealed by member {by} (a ROGUE seal) — not signed by {mover_s}: not a move"));
            return;
        }
        if slot != self.depth + 1 {
            self.bad_slots.insert(slot, format!("the game was at depth {}", self.depth));
            s.say(format!("venue: move {slot} sealed out of sequence (the game is at depth {})", self.depth));
            return;
        }
        match rules.judge(self, slot, &head, &entry[48 + n_sig..]) {
            Ok(desc) => {
                self.depth = slot;
                s.say(format!("venue: move {slot} sealed by member {by} at {}: {mover_s} — {desc}", t_rel(when)));
            }
            Err(why) => {
                self.bad_slots.insert(slot, why.clone());
                s.say(format!("venue: move {slot}: {mover_s}'s entry is NOT a valid move ({why}): nothing to settle; force-close and dispute"));
            }
        }
    }

    /// Submit an entry for depth `d` to its designated sealer.
    pub fn submit(&mut self, s: &mut Session, d: u32, entry: &[u8]) -> Result<()> {
        let to = lngap_pos::rotation(self.id, d, s.vparams.n);
        self.send(s, d, &hex::encode(entry), to)
    }

    fn send(&mut self, s: &Session, d: u32, entry: &str, to: usize) -> Result<()> {
        let at = unix_now();
        let name = format!("{}/{}.json", Store::inbox_dir(self.id), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
        s.store.write(&name, &InboxEntry { from: s.side(s.me).into(), depth: d, to, entry: entry.to_string(), at })?;
        self.pending = Some((d, entry.to_string(), to, at));
        Ok(())
    }

    // ============ the chain ============

    /// Feed the session's scan: a commitment confirming puts the game on
    /// chain (the dispute graph is that version's); graph transactions and
    /// spends are tracked.
    pub fn on_blocks(&mut self, s: &mut Session, blocks: Vec<(u32, Vec<Transaction>, Vec<ChainEvent>)>) -> Result<()> {
        for (height, txs, events) in blocks {
            for e in events {
                self.on_chain_event(s, e)?;
            }
            for tx in txs.iter().skip(1) {
                self.on_tx(s, height, tx)?;
            }
        }
        Ok(())
    }

    fn on_chain_event(&mut self, s: &mut Session, e: ChainEvent) -> Result<()> {
        let (seq, version, height, revoked) = match e {
            ChainEvent::LocalCommitConfirmed { seq, height } => (seq, s.me, height, false),
            ChainEvent::RemoteCommitConfirmed { seq, height } => (seq, s.me.other(), height, false),
            ChainEvent::RemoteRevokedCommitConfirmed { seq, height } => (seq, s.me.other(), height, true),
            ChainEvent::OutputSpent { .. } => return Ok(()),
        };
        let v = s.side(version);
        if revoked {
            s.say(format!("chain: height {height}: the {v} broadcast a REVOKED commitment ({seq}) — the penalty sweeps everything on it to me"));
            return Ok(());
        }
        s.say(format!("chain: height {height}: the {v}'s commitment {seq} confirmed — the channel is closed"));
        let rec = s.chan.record(seq).ok_or_else(|| anyhow!("no record of state {seq}"))?;
        self.graph = rec.graph.iter().filter(|(k, _)| k.version == version && k.contract_id == self.id).map(|(_, p)| p.clone()).collect();
        let commit = rec.commits[version.idx()].clone();
        if let Some(c) = commit.output(lngap_channel::commit::OutputKind::Contract(self.id)) {
            let op = commit.outpoint(c);
            let prev = commit.txout(c);
            self.live.insert("contract".into(), Live { height, op, prev: prev.clone() });
            self.phase = Some(Phase::Disputed);
            s.say(format!("game {}: its contract output {op} ({} sat) is on chain; the dispute graph is this commitment's", self.id, sat(prev.value)));
        }
        Ok(())
    }

    fn on_tx(&mut self, s: &mut Session, height: u32, tx: &Transaction) -> Result<()> {
        let txid = tx.compute_txid();
        if let Some(p) = self.graph.iter().find(|p| p.txid() == txid) {
            let label = p.label.clone();
            s.say(format!("chain: height {height}: `{label}` confirmed ({} vB)", tx.vsize()));
            if label.ends_with("/refute") {
                let base = label.trim_end_matches("/refute").to_string();
                match self.parse_reveal(&base, tx) {
                    Ok(sig) => {
                        self.reveals.insert(base.clone(), sig);
                        s.say(format!("chain: read the mover's pair reveal off `{label}`'s witness"));
                    }
                    Err(e) => s.say(format!("chain: could not parse the reveal in `{label}`: {e}")),
                }
            }
            self.live.insert(label, Live { height, op: OutPoint { txid, vout: 0 }, prev: tx.output[0].clone() });
        }
        for i in &tx.input {
            let op = i.previous_output;
            if let Some((label, _)) = self.live.iter().find(|(_, l)| l.op == op) {
                if !self.spent.contains_key(&op) {
                    let label = label.clone();
                    self.spent.insert(op, (txid, height));
                    if !self.graph.iter().any(|p| p.txid() == txid) {
                        s.say(format!("chain: height {height}: the output of `{label}` was spent by a runtime transaction {txid} ({} vB) — a disprove or a timeliness flag", tx.vsize()));
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
        // the reveal sits below the four elements the leaf consumes first:
        // the proposer's signature and index, then the 2-of-2's two
        // signatures (the script and control block follow them)
        const AFTER: usize = 4;
        ensure!(n >= 2 + AFTER + 2 * total, "witness too short");
        let args: Vec<Vec<u8>> = (0..n - 2).map(|i| w.nth(i).unwrap().to_vec()).collect();
        let block = &args[args.len() - AFTER - 2 * total..args.len() - AFTER];
        let hashes: Vec<[u8; 20]> = block.iter().step_by(2).map(|h| h.as_slice().try_into().map_err(|_| anyhow!("a reveal hash is 20 bytes"))).collect::<Result<_>>()?;
        let msg = self.parked_message(d)?;
        WotsSig::from_hashes(params, &msg, hashes).map_err(|e| anyhow!("{e}"))
    }

    fn parked_message(&self, d: u32) -> Result<Vec<u8>> {
        let head = |x: u32| -> Result<[u8; 48]> { Ok(self.blocks.get(&x).ok_or_else(|| anyhow!("no venue seal at depth {x}"))?.header.head()) };
        let mut m = Vec::new();
        if d >= 2 {
            m.extend_from_slice(&head(d - 1)?);
        }
        m.extend_from_slice(&head(d)?);
        Ok(m)
    }

    // ============ disputes ============

    fn skel(&self, label: &str) -> Result<&PresignedTx> {
        self.graph.iter().find(|p| p.label == label).ok_or_else(|| anyhow!("no skeleton {label} (the channel must be force-closed first)"))
    }

    fn live_claims(&self) -> Vec<(String, u32)> {
        let mut v = Vec::new();
        for (label, l) in &self.live {
            if self.spent.contains_key(&l.op) {
                continue;
            }
            if let Some(d) = label.strip_prefix("absent_").and_then(|x| x.parse::<u32>().ok()) {
                v.push((label.clone(), d));
            } else if let Some(d) = label.strip_prefix("absent_").and_then(|x| x.strip_suffix("/counter")).and_then(|x| x.parse::<u32>().ok()) {
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

    /// The depth of a live refutation against me (the disprove target).
    pub fn disprove_depth(&self, s: &Session) -> Option<u32> {
        self.live_refuted().into_iter().find(|(_, dd)| instance::mover_at(*dd) != s.me).map(|(_, d)| d)
    }

    pub fn mempool_labels(&self, s: &Session) -> Vec<String> {
        let Ok(pool) = s.rt.mempool() else { return vec![] };
        self.graph.iter().filter(|p| pool.contains(&p.txid())).map(|p| p.label.clone()).collect()
    }

    fn r_of(&self, rules: &dyn Rules, d: u32) -> Option<u8> {
        Some(rules.resolution(&self.blocks.get(&d)?.header.head(), d))
    }

    fn wins(s: &Session, code: u8) -> bool {
        code == 2 || code == s.me.idx() as u8
    }

    fn claim_wait(&self, s: &Session, d: u32) -> Option<String> {
        let Some((_, version, h0)) = s.closed else { return Some("the channel is open: force-close it first".into()) };
        let at = self.inst.as_ref()?.claim_from(d);
        let mtp = s.rt.mtp().unwrap_or(0);
        if mtp <= at {
            return Some(format!("its lock is median-time-past > {}; MTP is {}", t_rel(self.rel(at)), t_rel(self.rel(mtp))));
        }
        let h = s.height();
        let csv = h0 + u32::from(s.params.to_self_delay);
        if version == s.me && h < csv {
            return Some(format!("I broadcast the commitment: my claim waits to height {csv} ({} blocks)", csv - h));
        }
        None
    }

    fn window_open(&self, label: &str, blocks: u16) -> Result<u32> {
        let l = self.live.get(label).ok_or_else(|| anyhow!("`{label}` is not confirmed"))?;
        Ok(l.height + u32::from(blocks))
    }

    fn need_height(s: &Session, at: u32, what: &str) -> Result<()> {
        let h = s.height();
        ensure!(h >= at, "not broadcast: {what} cannot be mined before height {at} ({} blocks to go)", at - h);
        Ok(())
    }

    /// The opponent's earliest due move with no valid timely seal.
    pub fn grievance(&self, s: &Session) -> Option<(u32, String)> {
        if !matches!(self.phase, Some(Phase::Playing) | Some(Phase::Disputed)) {
            return None;
        }
        let now = unix_now();
        let d = self.depth + 1;
        let pool = self.mempool_labels(s);
        (1..=d).filter(|x| instance::mover_at(*x) != s.me && self.due(*x) < now).find_map(|x| {
            let untimely = self.blocks.get(&x).map(|_| self.bad_slots.contains_key(&x) || self.late_slots.contains(&x) || self.rogue_slots.contains(&x)).unwrap_or(true);
            let claimed = self.live.contains_key(&format!("absent_{x}")) || pool.contains(&format!("absent_{x}"));
            (untimely && !claimed).then(|| {
                let why = if self.late_slots.contains(&x) { format!("move {x} was sealed only LATE") } else if let Some(w) = self.bad_slots.get(&x) { format!("move {x} is not a valid move ({w})") } else { format!("the {} did not publish move {x} by t+{}s", s.side(instance::mover_at(x)), self.rel(self.due(x))) };
                (x, why)
            })
        })
    }

    /// The dispute buttons (and force close).
    pub fn dispute_actions(&self, s: &Session, rules: &dyn Rules) -> Vec<ActionView> {
        let h = s.height();
        let delta = s.params.delta;
        let delta2 = s.params.delta + s.params.delta_prime;
        let mut v = Vec::new();
        v.push(if s.channel_open() && s.in_channel(self.id) {
            match self.grievance(s) {
                Some((_, why)) => ActionView::ok("force close", &format!("{why}: take it on chain")),
                None => ActionView::ok("force close", "nothing wrong yet; closing puts the game on chain"),
            }
        } else {
            ActionView::no("force close", if s.channel_open() { "no game in the channel" } else { "the channel is closed" })
        });
        v.push(match self.grievance(s) {
            None => ActionView::no("claim", "nothing to claim"),
            Some((x, why)) => match self.claim_wait(s, x) {
                Some(wait) => ActionView::no("claim", &format!("{why}: not yet — {wait}")).with_cmd(&format!("claim {x}")),
                None => ActionView::ok("claim", &why).with_cmd(&format!("claim {x}")),
            },
        });
        let against_me: Vec<(String, u32)> = self.live_claims().into_iter().filter(|(_, dd)| instance::mover_at(*dd) == s.me).collect();
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
        match self.live_refuted().into_iter().find(|(_, dd)| instance::mover_at(*dd) != s.me) {
            Some((base, dd)) => {
                let open = self.window_open(&format!("{base}/refute"), delta).unwrap_or(0);
                let firing: Vec<String> = rules.firing(self, dd).into_iter().map(|(n, _)| n).collect();
                let flags = self.flags.get(&dd).map(|f| f.iter().filter(|x| x.is_some()).count()).unwrap_or(0);
                if h < open {
                    v.push(ActionView::no("disprove", &format!("`{base}`: the window opens at height {open}; fires: {}", if firing.is_empty() { "nothing".into() } else { firing.join(", ") })));
                    v.push(ActionView::no("timely", &format!("the window opens at height {open}; {flags} of {K} flags known")));
                } else {
                    let closes = self.window_open(&format!("{base}/refute"), delta2).unwrap_or(0);
                    v.push(if firing.is_empty() { ActionView::no("disprove", &format!("`{base}` (move {dd}): nothing fires")) } else { ActionView::ok("disprove", &format!("`{base}` (move {dd}): {} — before height {closes}", firing.join(", "))) });
                    v.push(if flags >= s.vparams.threshold as usize { ActionView::ok("timely", &format!("{flags} of {K} members flagged move {dd}")) } else { ActionView::no("timely", &format!("{flags} of {K} flags known for move {dd}")) });
                }
            }
            None => {
                v.push(ActionView::no("disprove", "no live refutation against you"));
                v.push(ActionView::no("timely", "no live refutation against you"));
            }
        }
        let mut split = ActionView::no("split", "nothing of yours to split");
        if let Some((base, dd, code)) = self.live_refuted().into_iter().filter_map(|(b, dd)| self.r_of(rules, dd).map(|c| (b, dd, c))).find(|(_, _, c)| Self::wins(s, *c)) {
            let open = self.window_open(&format!("{base}/refute"), delta2).unwrap_or(0);
            let r = (s.ui)(outcome_name(code));
            split = if h >= open { ActionView::ok("split", &format!("`{base}` (move {dd}): R = {r}")) } else { ActionView::no("split", &format!("`{base}`: R = {r}; opens at height {open} ({} blocks)", open - h)) };
        } else if let Some((base, _)) = self.live_claims().into_iter().find(|(_, dd)| instance::mover_at(*dd) != s.me) {
            let open = self.window_open(&base, delta).unwrap_or(0);
            split = if h >= open { ActionView::ok("split", &format!("your claim `{base}` is unanswered: the timeout split")) } else { ActionView::no("split", &format!("your claim `{base}`: the timeout opens at height {open} ({} blocks)", open - h)) };
        }
        v.push(split);
        v
    }

    fn sigs22(&self, label: &str) -> Result<[Vec<u8>; 2]> {
        let p = self.skel(label)?;
        let su = p.sigs[0].ok_or_else(|| anyhow!("{label}: no user sig"))?;
        let sh = p.sigs[1].ok_or_else(|| anyhow!("{label}: no hub sig"))?;
        Ok([sh.as_ref().to_vec(), su.as_ref().to_vec()])
    }

    fn broadcast(s: &mut Session, tx: &Transaction, what: &str) -> Result<()> {
        if let Err(e) = s.rt.test_accept(tx) {
            bail!("{what}: the node rejects it: {e}");
        }
        let txid = s.rt.send_raw(tx)?;
        s.say(format!("broadcast {what}: {txid} ({} vB); it confirms at the next block", tx.vsize()));
        Ok(())
    }

    pub fn claim(&mut self, s: &mut Session, d: Option<u32>) -> Result<()> {
        let d = d.or_else(|| self.grievance(s).map(|g| g.0)).ok_or_else(|| anyhow!("nothing to claim"))?;
        ensure!(instance::mover_at(d) != s.me, "depth {d} is your own move");
        if let Some(wait) = self.claim_wait(s, d) {
            bail!("not broadcast: `absent_{d}` is not mineable yet — {wait}");
        }
        let label = format!("absent_{d}");
        let [sh, su] = self.sigs22(&label)?;
        let p = self.skel(&label)?;
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&[sh, su], &p.leaf.script, &p.control_block);
        s.say(format!("claiming: no valid move {d} by its due time {}", t_rel(self.rel(self.due(d)))));
        Self::broadcast(s, &tx, &format!("`{label}`"))
    }

    pub fn counter(&mut self, s: &mut Session, d: Option<u32>) -> Result<()> {
        let live = self.live_claims();
        let (base, depth) = match d {
            Some(d) => (format!("absent_{d}"), d),
            None => live.iter().find(|(b, dd)| !b.contains("counter") && instance::mover_at(*dd) == s.me).cloned().ok_or_else(|| anyhow!("no live claim against you to counter"))?,
        };
        ensure!(depth >= 2, "no counter at depth 1");
        let label = format!("{base}/counter");
        let [sh, su] = self.sigs22(&label)?;
        let p = self.skel(&label)?;
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&[sh, su], &p.leaf.script, &p.control_block);
        s.say(format!("countering `{base}`: the claim was not due — no move {}", depth - 1));
        Self::broadcast(s, &tx, &format!("`{label}`"))
    }

    pub fn refute(&mut self, s: &mut Session, rules: &dyn Rules) -> Result<()> {
        let live = self.live_claims();
        let (base, d) = live.iter().find(|(_, d)| instance::mover_at(*d) == s.me).cloned().ok_or_else(|| anyhow!("no live claim against you on the chain"))?;
        let label = format!("{base}/refute");
        let (tx, prev, leaf, control) = {
            let p = self.skel(&label)?;
            (p.tx.clone(), p.prevouts[0].clone(), p.leaf.script.clone(), p.control_block.clone())
        };
        let new = self.blocks.get(&d).ok_or_else(|| anyhow!("nothing is sealed for move {d}"))?.clone();
        let new_head = new.header.head();
        let msg = self.parked_message(d)?;
        let pair_sig = s.ks.sign_wots(&instance::refute_label(self.id, 1, d), &msg).map_err(|e| anyhow!("{e}"))?;
        let auth = s.ks.sign_wots(&instance::state_label(self.id, 1, d), &rules.auth_message(&new_head)).map_err(|e| anyhow!("{e}"))?;
        let sign_at = |b: &SealedBlock| -> Vec<Vec<u8>> { (0..HEAD_CHUNKS).map(|j| sig_bytes(&Keypair::from_secret_key(SECP256K1, &b.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect() };
        let sigs_new = sign_at(&new);
        let mut w = if d >= 2 {
            // the prior is bound by the opponent's own signature, taken from
            // its sealed entry; only the new head is read out
            let prior = self.blocks.get(&(d - 1)).ok_or_else(|| anyhow!("no seal for move {}", d - 1))?;
            let key = self.their_state_keys.get(&(d - 1)).ok_or_else(|| anyhow!("no state key for move {}", d - 1))?;
            let prior_auth = refute::entry_auth_sig(key, &rules.auth_message(&prior.header.head()), &prior.entry).ok_or_else(|| anyhow!("move {} is not signed by its mover", d - 1))?;
            refute::refute_witness_pair_signed(&sigs_new, &pair_sig, [&auth, &prior_auth])
        } else {
            refute::refute_witness(&sigs_new, &pair_sig, &auth)
        };
        w.extend(proposer_witness(sig_bytes(&Keypair::from_secret_key(SECP256K1, &new.proposer_secret), &tx, &prev, &leaf), new.proposer));
        // the refutation is 2-of-2: both parties' pre-signatures of the skeleton
        w.extend(self.sigs22(&label)?);
        let mut tx = tx;
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.reveals.insert(base.clone(), pair_sig);
        s.say(format!("refuting `{base}`: the venue attested my move {d}"));
        Self::broadcast(s, &tx, &format!("`{label}`"))
    }

    fn payout_tx(&self, s: &Session, base: &str, d: u32, leaf_name: &str) -> Result<(Transaction, TxOut, ScriptBuf, bitcoin::taproot::ControlBlock)> {
        let l = self.live.get(&format!("{base}/refute")).ok_or_else(|| anyhow!("no live refutation on `{base}`"))?.clone();
        let (seq, version, _) = s.closed.ok_or_else(|| anyhow!("the channel is open"))?;
        let ctx = s.chan.commit_ctx(seq, version)?;
        let tree = self.inst()?.refuted_tree(&ctx, d)?;
        let leaf = tree.leaf(leaf_name)?.clone();
        let tx = build_spend(l.op, &leaf.timelock, vec![TxOut { value: l.prev.value - s.params.presign_fee, script_pubkey: s.chan.my_payout_spk() }]);
        Ok((tx, l.prev, leaf.script, tree.control_block(leaf_name)?))
    }

    pub fn disprove(&mut self, s: &mut Session, rules: &dyn Rules, which: Option<String>) -> Result<()> {
        let (base, d) = self.live_refuted().into_iter().find(|(_, d)| instance::mover_at(*d) != s.me).ok_or_else(|| anyhow!("no live refutation against you"))?;
        let firing = rules.firing(self, d);
        let (name, wits) = match which {
            Some(w) => firing.into_iter().find(|(n, _)| n.ends_with(&w)).ok_or_else(|| anyhow!("`{w}` does not fire on the parked tuple"))?,
            None => firing.into_iter().next().ok_or_else(|| anyhow!("no disprove leaf fires: the move is valid"))?,
        };
        let leaf_name = format!("disprove_{name}");
        Self::need_height(s, self.window_open(&format!("{base}/refute"), s.params.delta)?, &leaf_name)?;
        let (mut tx, prev, leaf, control) = self.payout_tx(s, &base, d, &leaf_name)?;
        let reveal = self.reveals.get(&base).ok_or_else(|| anyhow!("the mover's reveal is not known yet"))?.clone();
        let mut w = wits;
        w.extend(refute::wots_wire(&reveal));
        w.push(sig_bytes(&s.chan.keys.payment, &tx, &prev, &leaf));
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        s.say(format!("disproving the parked move {d} of `{base}`: {name}"));
        Self::broadcast(s, &tx, &leaf_name)
    }

    pub fn timely(&mut self, s: &mut Session) -> Result<()> {
        let (base, d) = self.live_refuted().into_iter().find(|(_, d)| instance::mover_at(*d) != s.me).ok_or_else(|| anyhow!("no live refutation against you"))?;
        let scalars = self.flags.get(&d).cloned().ok_or_else(|| anyhow!("no flags known for move {d}"))?;
        Self::need_height(s, self.window_open(&format!("{base}/refute"), s.params.delta)?, "not_timely")?;
        let (mut tx, prev, leaf, control) = self.payout_tx(s, &base, d, "not_timely")?;
        let w = not_timely_witness(&tx, 0, std::slice::from_ref(&prev), &leaf, &s.chan.keys.payment, &scalars);
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        s.say(format!("killing the refutation on `{base}` as NOT TIMELY"));
        Self::broadcast(s, &tx, "not_timely")
    }

    /// The checked split (a refuted output whose R favours me; either party
    /// may broadcast it) or my timeout split. `checked_witness` builds the
    /// game's checked-split witness from (sig_user, sig_hub, pair reveal,
    /// the mover's code reveal if the game's split is gated).
    pub fn split(&mut self, s: &mut Session, rules: &dyn Rules, checked_witness: &dyn Fn(&mut Session, u32, u8, Vec<u8>, Vec<u8>, &WotsSig) -> Result<Vec<Vec<u8>>>) -> Result<()> {
        if let Some((base, d, code)) = self.live_refuted().into_iter().filter_map(|(b, dd)| self.r_of(rules, dd).map(|c| (b, dd, c))).find(|(_, _, c)| Self::wins(s, *c)) {
            let label = format!("{base}/refuted/split_{}", outcome_name(code));
            Self::need_height(s, self.window_open(&format!("{base}/refute"), s.params.delta + s.params.delta_prime)?, &label)?;
            let pair = self.reveals.get(&base).ok_or_else(|| anyhow!("no reveal for {base}"))?.clone();
            let [sh, su] = self.sigs22(&label)?;
            let w = checked_witness(s, d, code, su, sh, &pair)?;
            let p = self.skel(&label)?;
            let mut tx = p.tx.clone();
            tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
            s.say(format!("the checked split on `{base}` (move {d}): R = {}", (s.ui)(outcome_name(code))));
            return Self::broadcast(s, &tx, &format!("`{label}`"));
        }
        if let Some((base, d)) = self.live_claims().into_iter().find(|(_, d)| instance::mover_at(*d) != s.me) {
            let code: u8 = s.me.idx() as u8;
            let label = format!("{base}/split_{}", outcome_name(code));
            Self::need_height(s, self.window_open(&base, s.params.delta)?, &label)?;
            let reveal = s.ks.reveal_uint(&instance::ccode_label(self.id, 1, d), u32::from(code))?;
            let [sh, su] = self.sigs22(&label)?;
            let p = self.skel(&label)?;
            let mut tx = p.tx.clone();
            let mut w = reveal.consumption_order();
            w.reverse();
            w.push(sh);
            w.push(su);
            tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
            s.say(format!("timeout split on `{base}`: {} (the staller forfeits)", (s.ui)(outcome_name(code))));
            return Self::broadcast(s, &tx, &format!("`{label}`"));
        }
        bail!("nothing of yours to split")
    }

    /// The venue timeline and the chain view, for the pages.
    pub fn views(&self, s: &Session, describe: &dyn Fn(u32, &SealedBlock) -> String) -> (Vec<SlotView>, Vec<LiveView>, Vec<String>) {
        let mut slots: Vec<SlotView> = self
            .blocks
            .iter()
            .map(|(d, b)| {
                let what = format!("{}: {}", s.side(instance::mover_at(*d)), describe(*d, b));
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
        let mut live: Vec<LiveView> = self.live.iter().map(|(label, l)| LiveView { label: (s.ui)(label), height: l.height, spent: self.spent.contains_key(&l.op), value_sat: l.prev.value.to_sat() }).collect();
        if let Some((seq, v, h)) = s.closed {
            live.insert(0, LiveView { label: format!("commitment {seq} ({}'s)", s.side(v)), height: h, spent: false, value_sat: s.params.funding_amount.to_sat() });
        }
        let mempool = self.mempool_labels(s).iter().map(|l| (s.ui)(l)).collect();
        (slots, live, mempool)
    }
}

/// A time relative to the game's start as the pages show it: `t+5s`, or
/// `t-5s` for a move sealed before its game's clock started.
pub fn t_rel(x: i64) -> String {
    if x < 0 { format!("t{x}s") } else { format!("t+{x}s") }
}
