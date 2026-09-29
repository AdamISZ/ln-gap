//! The channel session (D58): a Poon-Dryja channel between the two parties,
//! opened once, whose updates carry one game at a time as a contract
//! output. Messages travel over the shared directory (`channel/bus/<to>/`,
//! `channel::wire` envelopes); each party's channel policy accepts adding
//! a game only with each side's stake and deposit, and removing it only
//! with the payout of the result it saw itself.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use anyhow::{anyhow, ensure, Result};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::chain::Chain;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::protocol::{funding_tree, ChainEvent, ChannelParty, Closing, Envelope, Policy};
use lngap_channel::wire::WireEnvelope;
use lngap_channel::{ChannelParams, ChannelState, ContractOutput, PartyKeys, Role};
use lngap_lamport::keystore::KeyStore;
use lngap_pos::instance::PosInstance;
use serde::Serialize;

use crate::store::*;

/// What this party's policy agrees to: adding game `id` with `contribution`
/// from each side, and removing it with `payout`.
#[derive(Default)]
struct Agree {
    open: Option<(u32, Amount)>,
    fold: Option<(u32, [Amount; 2])>,
    /// The payout of game `id` that gives me the win: a concession (the
    /// counterparty resigning) is always acceptable.
    concede: Option<(u32, [Amount; 2])>,
}

pub fn wait_for<T>(mut f: impl FnMut() -> Result<Option<T>>) -> Result<T> {
    loop {
        if let Some(v) = f()? {
            return Ok(v);
        }
        std::thread::sleep(Duration::from_millis(300));
    }
}

/// Satoshis with thousands separators.
pub fn sat(a: Amount) -> String {
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

#[derive(Serialize, Clone, Debug)]
pub struct ChannelView {
    pub seq: u64,
    pub user: u64,
    pub hub: u64,
    pub in_play: u64,
    pub status: String,
}

pub struct Session {
    pub me: Role,
    pub store: Store,
    pub rt: Arc<Regtest>,
    pub vparams: VenueParams,
    pub params: ChannelParams,
    pub chan: ChannelParty,
    agree: Arc<Mutex<Agree>>,
    pub ks: KeyStore,
    /// Every game's instance, by id (the bus resolves contract ids here).
    pub instances: BTreeMap<u32, Arc<PosInstance>>,
    bus_seen: BTreeSet<String>,
    pub scanned: u32,
    /// The commitment that closed the channel: (seq, broadcaster, height).
    pub closed: Option<(u64, Role, u32)>,
    pub log: Vec<String>,
    /// The parties' names in the interface, and the label rewriter.
    pub names: fn(Role) -> &'static str,
    pub ui: fn(&str) -> String,
}

impl Session {
    pub fn side(&self, r: Role) -> &'static str {
        (self.names)(r)
    }

    pub fn say(&mut self, s: String) {
        let s = (self.ui)(&s);
        println!("  {s}");
        self.log.push(s);
    }

    pub fn height(&self) -> u32 {
        self.rt.height().unwrap_or(0)
    }

    pub fn publish_web_port(&self, port: u16) -> Result<()> {
        self.store.write(&Store::web(self.me), &serde_json::json!({ "port": port }))
    }

    /// Open the channel: fund my half from the node's wallet, exchange
    /// offers, sign state 0 over the bus, sign my funding input; the user
    /// broadcasts. `label` seeds the keys (one per demo).
    pub fn open(dir: PathBuf, me: Role, label: &str, names: fn(Role) -> &'static str, ui: fn(&str) -> String) -> Result<Session> {
        let store = Store::new(dir);
        let who = names(me);
        let them = names(me.other());
        println!("{who}: waiting for the venue's node...");
        let vparams: VenueParams = wait_for(|| store.read::<VenueParams>(Store::params()))?;
        let node: NodeInfo = wait_for(|| store.read(Store::node()))?;
        let rt = Arc::new(Regtest::attach(&PathBuf::from(node.datadir))?);

        let keys = PartyKeys::from_seed(me, Seed::from_label(&format!("{label}/{}", me.name())));
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
        println!("{who}: channel offer published (a {} sat contribution); waiting for {them}'s...", sat(side_amt));
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
            ensure!(added.len() + removed.len() <= 1, "one game at a time");
            if let Some(id) = added.first() {
                let (aid, c) = a.open.ok_or_else(|| anyhow!("I agreed to no game"))?;
                ensure!(aid == *id, "I agreed to game {aid}, not {id}");
                ensure!(new.balances == [old.balances[0].checked_sub(c).ok_or_else(|| anyhow!("balance"))?, old.balances[1].checked_sub(c).ok_or_else(|| anyhow!("balance"))?], "each side puts in its stake and deposit");
            } else if let Some(id) = removed.first() {
                let paid = |p: [Amount; 2]| new.balances == [old.balances[0] + p[0], old.balances[1] + p[1]];
                let conceded = a.concede.is_some_and(|(cid, p)| cid == *id && paid(p));
                if !conceded {
                    let (fid, pay) = a.fold.ok_or_else(|| anyhow!("game {id} has no agreed result on my side"))?;
                    ensure!(fid == *id, "my agreed result is game {fid}'s");
                    ensure!(paid(pay), "the payout is not the result I agreed");
                }
            } else {
                ensure!(new.balances == old.balances, "no change without a game");
            }
            Ok(())
        });
        let initial = ChannelState { seq: 0, balances: [side_amt, side_amt], contracts: vec![] };
        let chain: Arc<dyn Chain> = rt.clone();
        let chan = ChannelParty::new(keys, pubs[me.other().idx()].clone(), params, funding.clone(), initial, rev(&theirs)?, chain, policy)?;
        let mut s = Session {
            me,
            store,
            rt,
            vparams,
            params,
            chan,
            agree,
            ks: KeyStore::new(Seed::from_label(&format!("{label}/{}-ks", me.name()))),
            instances: BTreeMap::new(),
            bus_seen: BTreeSet::new(),
            scanned: 0,
            closed: None,
            log: Vec::new(),
            names,
            ui,
        };
        let m = s.chan.initial_commit_sigs()?;
        s.send_env(&m)?;
        wait_for(|| {
            s.bus()?;
            Ok(s.chan.ready_to_fund().then_some(()))
        })?;
        let idx = me.idx();
        let prevouts = [contribs[0].1.clone(), contribs[1].1.clone()];
        sign_funding_input(&mut ftx, idx, &prevouts, &s.chan.keys.payout_tree(), &s.chan.keys.payout)?;
        let wit: Vec<String> = ftx.input[idx].witness.iter().map(hex::encode).collect();
        s.store.write(&Store::funding_wit(me), &wit)?;
        if me == Role::User {
            let other: Vec<String> = wait_for(|| s.store.read(&Store::funding_wit(Role::Hub)))?;
            ftx.input[1].witness = bitcoin::Witness::from_slice(&other.iter().map(hex::decode).collect::<std::result::Result<Vec<_>, _>>()?);
            let txid = s.rt.send_raw(&ftx)?;
            println!("{who}: the funding transaction {txid} is broadcast; waiting for it to confirm...");
            // (`confirmations` returns the confirming block's height)
            let h = wait_for(|| s.rt.confirmations(&txid))?;
            s.store.write(Store::funded(), &serde_json::json!({ "txid": txid.to_string(), "height": h }))?;
        }
        let f: serde_json::Value = wait_for(|| s.store.read(Store::funded()))?;
        let h = f["height"].as_u64().unwrap_or(0) as u32;
        s.scanned = h;
        s.say(format!("the channel is open: {} sat each side, funded at height {h}", sat(side_amt)));
        Ok(s)
    }

    fn send_env(&self, e: &Envelope) -> Result<()> {
        let w = WireEnvelope::from_env(e)?;
        let name = format!("{}/{}.json", Store::bus(e.to), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
        self.store.write(&name, &w)
    }

    /// Handle every unread channel message; send the replies.
    pub fn bus(&mut self) -> Result<()> {
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
    pub fn propose(&mut self, balances: [Amount; 2], contracts: Vec<Arc<dyn ContractOutput>>) -> Result<()> {
        let seq = self.chan.current_seq() + 1;
        let msgs = self.chan.propose(ChannelState { seq, balances, contracts })?;
        for m in &msgs {
            self.send_env(m)?;
        }
        Ok(())
    }

    pub fn agree_open(&self, id: u32, contribution: Amount) {
        self.agree.lock().unwrap().open = Some((id, contribution));
    }

    pub fn agree_concede(&self, id: u32, payout: [Amount; 2]) {
        self.agree.lock().unwrap().concede = Some((id, payout));
    }

    pub fn agree_fold(&self, id: u32, payout: [Amount; 2]) {
        self.agree.lock().unwrap().fold = Some((id, payout));
    }

    pub fn agreed_fold(&self) -> Option<(u32, [Amount; 2])> {
        self.agree.lock().unwrap().fold
    }

    pub fn channel_open(&self) -> bool {
        self.chan.closing.is_none()
    }

    pub fn in_channel(&self, id: u32) -> bool {
        self.chan.current_state().contract(id).is_some()
    }

    pub fn idle(&self) -> bool {
        self.chan.pending_seq().is_none()
    }

    pub fn balances(&self) -> [Amount; 2] {
        self.chan.current_state().balances
    }

    pub fn force_close(&mut self) -> Result<()> {
        ensure!(self.channel_open(), "the channel is already closing");
        let txid = self.chan.force_close()?;
        self.say(format!("FORCE-CLOSING the channel: my commitment {} ({txid}) is broadcast; the game's contract output appears on chain when it confirms", self.chan.current_seq()));
        Ok(())
    }

    pub fn close_channel(&mut self) -> Result<()> {
        ensure!(self.channel_open(), "the channel is already closing");
        ensure!(self.chan.current_state().contracts.is_empty(), "settle the game first");
        let msgs = self.chan.propose_close()?;
        for m in &msgs {
            self.send_env(m)?;
        }
        self.say("closing the channel cooperatively: one transaction pays both balances".into());
        Ok(())
    }

    /// New blocks: each block's transactions and the channel's events for
    /// it (the channel's own sweeps and penalties happen here).
    pub fn scan(&mut self) -> Result<Vec<(u32, Vec<Transaction>, Vec<ChainEvent>)>> {
        let mut out = Vec::new();
        let h = self.height();
        while self.scanned < h {
            self.scanned += 1;
            let txs = self.rt.block_txs(self.scanned)?;
            let events = self.chan.on_block(self.scanned, &txs)?;
            for e in &events {
                match e {
                    ChainEvent::LocalCommitConfirmed { seq, height } => self.closed = Some((*seq, self.me, *height)),
                    ChainEvent::RemoteCommitConfirmed { seq, height } | ChainEvent::RemoteRevokedCommitConfirmed { seq, height } => self.closed = Some((*seq, self.me.other(), *height)),
                    ChainEvent::OutputSpent { .. } => {}
                }
            }
            out.push((self.scanned, txs, events));
        }
        Ok(out)
    }

    pub fn channel_view(&self) -> ChannelView {
        let cb = self.balances();
        ChannelView {
            seq: self.chan.current_seq(),
            user: cb[0].to_sat(),
            hub: cb[1].to_sat(),
            in_play: self.chan.current_state().contracts_value().to_sat(),
            status: match &self.chan.closing {
                None => "open".into(),
                Some(Closing::Cooperative { .. }) => "closed cooperatively".into(),
                Some(_) => "force-closed".into(),
            },
        }
    }

    pub fn onchain_balance(&self) -> u64 {
        self.rt.balance_of(&self.chan.my_payout_spk()).map(|a| a.to_sat()).unwrap_or(0)
    }
}
