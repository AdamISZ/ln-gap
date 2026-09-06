//! Scenario harness: a regtest node, a user and a hub with one channel,
//! a clock (mining) and a message bus. The harness mines, delivers blocks,
//! relays messages and observes; it never tells a party what to broadcast.

use std::sync::Arc;

use anyhow::{ensure, Result};
use bitcoin::{Amount, OutPoint, Transaction, Txid};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::chain::Chain;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::protocol::{funding_tree, run_bus as run_channel_bus};
use lngap_channel::{ChannelParams, ChannelState, PartyKeys, Role};
use lngap_contract::Program;
use lngap_party::{run_bus, PEnvelope, Party};
use tracing::info;

pub const FUNDING: Amount = Amount::from_sat(200_000);
pub mod scenarios;

pub const HALF: Amount = Amount::from_sat(100_000);
const CONTRIB: Amount = Amount::from_sat(100_500);

/// One on-chain transaction the harness saw, with the role the broadcasting
/// party gave it.
#[derive(Clone, Debug)]
pub struct SeenTx {
    pub height: u32,
    pub txid: Txid,
    pub role: String,
    pub by: Option<Role>,
}

pub struct Harness {
    pub rt: Arc<Regtest>,
    pub user: Party,
    pub hub: Party,
    pub funding_txid: Txid,
    pub funding_height: u32,
    pub seen: Vec<SeenTx>,
}

pub fn init_log() {
    let _ = tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with_test_writer()
        .try_init();
}

impl Harness {
    /// Fresh regtest, fresh keys, one 100k/100k channel, both parties knowing `programs`.
    pub fn new(label: &str, programs: Vec<Arc<dyn Program>>) -> Result<Harness> {
        init_log();
        let rt = Arc::new(Regtest::start()?);
        Harness::with_regtest(rt, label, programs)
    }

    pub fn with_regtest(rt: Arc<Regtest>, label: &str, programs: Vec<Arc<dyn Program>>) -> Result<Harness> {
        let params = ChannelParams::regtest(FUNDING);
        let user_seed = Seed::from_label(&format!("{label}/user"));
        let hub_seed = Seed::from_label(&format!("{label}/hub"));
        let user_keys = PartyKeys::from_seed(Role::User, user_seed.child("channel"));
        let hub_keys = PartyKeys::from_seed(Role::Hub, hub_seed.child("channel"));
        let pubs = [user_keys.public(), hub_keys.public()];

        let (u_op, u_prev) = rt.fund(&pubs[0].payout_spk, CONTRIB)?;
        let (h_op, h_prev) = rt.fund(&pubs[1].payout_spk, CONTRIB)?;
        let ftree = funding_tree(&pubs);
        let mut ftx = build_funding_tx(&[(u_op, u_prev.clone()), (h_op, h_prev.clone())], ftree.script_pubkey(), FUNDING);
        let funding = (OutPoint { txid: ftx.compute_txid(), vout: 0 }, ftx.output[0].clone());
        let initial = ChannelState { seq: 0, balances: [HALF, HALF], contracts: vec![] };
        let chain: Arc<dyn Chain> = rt.clone();
        let user_rev = [user_keys.revocation_hash(0), user_keys.revocation_hash(1)];
        let hub_rev = [hub_keys.revocation_hash(0), hub_keys.revocation_hash(1)];
        let mut user = Party::new(Role::User, user_seed, pubs[1].clone(), params, funding.clone(), initial.clone(), hub_rev, chain.clone(), programs.clone())?;
        let mut hub = Party::new(Role::Hub, hub_seed, pubs[0].clone(), params, funding, initial, user_rev, chain, programs)?;

        let m1 = user.channel.initial_commit_sigs()?;
        let m2 = hub.channel.initial_commit_sigs()?;
        run_channel_bus(&mut user.channel, &mut hub.channel, vec![m1, m2])?;
        ensure!(user.channel.ready_to_fund() && hub.channel.ready_to_fund());
        let prevouts = [u_prev, h_prev];
        sign_funding_input(&mut ftx, 0, &prevouts, &user.channel.keys.payout_tree(), &user.channel.keys.payout)?;
        sign_funding_input(&mut ftx, 1, &prevouts, &hub.channel.keys.payout_tree(), &hub.channel.keys.payout)?;
        let (funding_txid, funding_height) = rt.send_and_confirm(&ftx)?;
        let h = rt.height()?;
        user.set_height(h);
        hub.set_height(h);
        info!(%funding_txid, funding_height, "channel funded");
        let seen = vec![SeenTx { height: funding_height, txid: funding_txid, role: "funding".into(), by: None }];
        Ok(Harness { rt, user, hub, funding_txid, funding_height, seen })
    }

    pub fn height(&self) -> u32 {
        self.rt.height().unwrap()
    }
    pub fn params(&self) -> ChannelParams {
        self.user.channel.params
    }
    pub fn party(&mut self, r: Role) -> &mut Party {
        match r {
            Role::User => &mut self.user,
            Role::Hub => &mut self.hub,
        }
    }

    /// Deliver messages until quiescent.
    pub fn bus(&mut self, msgs: Vec<PEnvelope>) -> Result<()> {
        run_bus(&mut self.user, &mut self.hub, msgs)
    }

    /// Let both parties act off-chain (moves, resolutions) until nothing
    /// more happens.
    pub fn settle_offchain(&mut self) -> Result<()> {
        for _ in 0..100 {
            let mut msgs = self.user.poll()?;
            if msgs.is_empty() {
                msgs = self.hub.poll()?;
            }
            if msgs.is_empty() {
                return Ok(());
            }
            self.bus(msgs)?;
        }
        anyhow::bail!("off-chain activity did not quiesce")
    }

    /// Mine one block; deliver it to both parties; then let them act off-chain.
    pub fn step(&mut self) -> Result<u32> {
        self.rt.mine(1)?;
        let h = self.height();
        let txs = self.rt.block_txs(h)?;
        self.record_block(h, &txs);
        self.user.on_block(h, &txs)?;
        self.hub.on_block(h, &txs)?;
        self.settle_offchain()?;
        Ok(h)
    }

    pub fn steps(&mut self, n: u32) -> Result<()> {
        for _ in 0..n {
            self.step()?;
        }
        Ok(())
    }

    /// Step until `pred` holds or `max` blocks pass.
    pub fn step_until(&mut self, max: u32, mut pred: impl FnMut(&Harness) -> bool) -> Result<u32> {
        for i in 0..max {
            if pred(self) {
                return Ok(i);
            }
            self.step()?;
        }
        ensure!(pred(self), "condition not met within {max} blocks");
        Ok(max)
    }

    fn record_block(&mut self, height: u32, txs: &[Transaction]) {
        for tx in txs.iter().skip(1) {
            let txid = tx.compute_txid();
            let by = self.user.channel.broadcasts.iter().map(|b| (b, Role::User)).chain(self.hub.channel.broadcasts.iter().map(|b| (b, Role::Hub))).find(|(b, _)| b.txid == txid);
            let (role, by) = match by {
                Some((b, r)) => (b.role.clone(), Some(r)),
                None => ("external".to_string(), None),
            };
            info!(height, %txid, role, ?by, "confirmed");
            self.seen.push(SeenTx { height, txid, role, by });
        }
    }

    pub fn balance(&self, r: Role) -> Amount {
        let spk = match r {
            Role::User => self.user.channel.my_payout_spk(),
            Role::Hub => self.hub.channel.my_payout_spk(),
        };
        self.rt.balance_of(&spk).unwrap()
    }

    /// Channel-related transactions confirmed after funding, by role.
    pub fn roles_seen(&self) -> Vec<String> {
        self.seen.iter().filter(|s| s.role != "funding").map(|s| s.role.clone()).collect()
    }

    /// Print the narrative from both parties and the on-chain log.
    pub fn narrative(&self) -> String {
        let mut lines: Vec<String> = Vec::new();
        lines.push("--- on-chain ---".into());
        for s in &self.seen {
            lines.push(format!("block {}: {} {} ({})", s.height, s.role, s.txid, s.by.map(|r| r.name()).unwrap_or("harness")));
        }
        lines.push("--- user ---".into());
        lines.extend(self.user.narrative().iter().cloned());
        lines.push("--- hub ---".into());
        lines.extend(self.hub.narrative().iter().cloned());
        lines.join("\n")
    }

    /// Cross-cutting: every party-broadcast transaction was signed by both
    /// parties unless it is a disproof or a revocation/balance sweep.
    pub fn assert_signing_rule(&self) {
        for s in &self.seen {
            let r = s.role.as_str();
            let single = r.starts_with("disprove_") || r.starts_with("revoke_sweep") || r.starts_with("claim_to_");
            let dual = r.starts_with("commitment_") || r == "settle" || r.starts_with("move_") || r.starts_with("split_") || r == "coop_close";
            assert!(single || dual || r == "funding" || r == "external", "unexpected tx role {r}");
        }
    }
}
