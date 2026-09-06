//! Two channels (Alice–hub, Bob–hub), one registry operator, one clock.
//! The world mines, delivers blocks to every party and to the registry,
//! relays statements the registry hands out, relays messages, and performs
//! the users' *application* steps (send the reveal once the commit is
//! anchored). It never tells a party what to broadcast.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, Result};
use bitcoin::key::XOnlyPublicKey;
use bitcoin::{Amount, Transaction};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_names::hub::{NamesHub, Receipt};
use lngap_names::programs::{AttestPayParams, NRegParams};
use lngap_names::registry::Event;
use lngap_names::statements::{attest_label, attest_value, receipt_label, STATEMENT_BITS};
use lngap_names::user::NamesUser;
use lngap_names::{registry_programs, AttestPay, NReg};
use lngap_party::draft::{downcast, Change};
use lngap_party::{ChangeCtx, MoveCtx};
use tracing::info;

use crate::{init_log, Harness};

pub const BOND: Amount = Amount::from_sat(20_000);
pub const PRICE: Amount = Amount::from_sat(10_000);
pub const ID_BOND: u32 = 10;
pub const ID_LEG1: u32 = 20;
pub const ID_LEG2: u32 = 21;
pub const ID_TBOND: u32 = 22;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Who {
    Alice,
    Bob,
}

pub struct NamesWorld {
    pub rt: Arc<Regtest>,
    pub alice: Harness,
    pub bob: Harness,
    pub hub: Arc<Mutex<NamesHub>>,
    pub alice_name: NamesUser,
    pub bob_user: NamesUser,
    /// Users interested in a statement label (they registered its key).
    interested: HashMap<String, HashSet<Who>>,
    /// Statements the hub withholds from a user (scenario fault).
    pub withhold_from: HashSet<Who>,
    pub genesis_height: u32,
    reveal_sent: bool,
    pub registering: bool,
    pub log: Vec<String>,
}

impl NamesWorld {
    pub fn new(label: &str) -> Result<NamesWorld> {
        init_log();
        let rt = Arc::new(Regtest::start()?);
        let hub_seed = Seed::from_label(&format!("{label}/registry"));
        let mut hub = NamesHub::new(&hub_seed);
        let (op, txout) = rt.fund(&hub.genesis_spk(), Amount::from_sat(50_000))?;
        let genesis_height = rt.height()?;
        hub.set_genesis(op, txout, genesis_height);
        let alice = Harness::with_regtest(rt.clone(), &format!("{label}/alice"), registry_programs())?;
        let bob = Harness::with_regtest(rt.clone(), &format!("{label}/bob"), registry_programs())?;
        let alice_name = NamesUser::new(&Seed::from_label(&format!("{label}/alice/name")), "alice");
        let bob_user = NamesUser::new(&Seed::from_label(&format!("{label}/bob/name")), "alice");
        let hub = Arc::new(Mutex::new(hub));
        let mut w = NamesWorld {
            rt,
            alice,
            bob,
            hub,
            alice_name,
            bob_user,
            interested: HashMap::new(),
            withhold_from: HashSet::new(),
            genesis_height,
            reveal_sent: false,
            registering: false,
            log: Vec::new(),
        };
        w.install_hub_policies();
        w.sync_heights();
        Ok(w)
    }

    fn say(&mut self, s: String) {
        info!(world = "names", "{s}");
        self.log.push(format!("[world @ {}] {s}", self.height()));
    }

    pub fn height(&self) -> u32 {
        self.rt.height().unwrap()
    }
    fn sync_heights(&mut self) {
        let h = self.height();
        for p in [&mut self.alice.user, &mut self.alice.hub, &mut self.bob.user, &mut self.bob.hub] {
            p.set_height(h);
        }
    }
    pub fn channel(&mut self, who: Who) -> &mut Harness {
        match who {
            Who::Alice => &mut self.alice,
            Who::Bob => &mut self.bob,
        }
    }
    pub fn alice_key(&self) -> XOnlyPublicKey {
        self.alice_name.owner_key()
    }
    pub fn bob_key(&self) -> XOnlyPublicKey {
        self.bob_user.owner_key()
    }

    /// The hub's change policy on both channels: bonds only for receipts it
    /// issued; refuse a "receipted, unattested" claim when it holds the
    /// attestation (it will disprove on-chain instead); always agree to fold.
    /// `veto` adds scenario-specific refusals on top.
    pub fn set_hub_policy(&mut self, who: Who, veto: Option<Box<dyn Fn(&ChangeCtx) -> Result<()> + Send + Sync>>) {
        let hub = self.hub.clone();
        let policy = Box::new(move |ctx: &ChangeCtx| -> Result<()> {
            if let Some(v) = &veto {
                v(ctx)?;
            }
            match ctx.change {
                Change::Open { program, stakes, .. } => {
                    if let Some(p) = program.strip_prefix("nreg:") {
                        let params: NRegParams = serde_json::from_str(p)?;
                        anyhow::ensure!(hub.lock().unwrap().issued(params.req_id), "no receipt {} was issued", params.req_id);
                        anyhow::ensure!(stakes[Role::Hub.idx()] <= BOND && stakes[Role::User.idx()] == Amount::ZERO, "bond terms");
                        Ok(())
                    } else if program.starts_with("attestpay:") {
                        anyhow::ensure!(stakes[Role::Hub.idx()] == Amount::ZERO, "the hub does not lock into user-opened payments");
                        Ok(())
                    } else {
                        anyhow::bail!("unknown program")
                    }
                }
                Change::Move { id, .. } => {
                    let c = ctx.current.contract(*id).ok_or_else(|| anyhow!("no contract {id}"))?;
                    let name = downcast(c).program.name().to_string();
                    if let Some(p) = name.strip_prefix("nreg:") {
                        let params: NRegParams = serde_json::from_str(p)?;
                        anyhow::ensure!(!(ctx.has)(&params.attest_label), "I attested {}; disputing on-chain", params.attest_label);
                    }
                    Ok(())
                }
                _ => Ok(()),
            }
        });
        self.channel(who).hub.set_change_policy(policy);
    }

    fn install_hub_policies(&mut self) {
        for who in [Who::Alice, Who::Bob] {
            self.set_hub_policy(who, None);
        }
    }

    // ----- registry interactions (user application steps) -----

    fn hub_receipt(&mut self, who: Who, event: Event) -> Result<Receipt> {
        let h = self.height();
        let r = self.hub.lock().unwrap().receipt(event, h)?;
        let label = receipt_label(r.req_id);
        let party = &mut self.channel(who).user;
        party.know_key(&label, r.pk.clone());
        party.learn_reveal(&label, r.reveal.clone())?;
        Ok(r)
    }

    /// Everyone who may need `attest(name, owner)` learns its key.
    fn share_attest_key(&mut self, name: &str, owner: &XOnlyPublicKey, users: &[Who]) -> (String, lngap_lamport::PublicKey, u32) {
        let label = attest_label(name, owner);
        let pk = self.hub.lock().unwrap().attest_pk(name, owner);
        let value = attest_value(name, owner);
        for who in [Who::Alice, Who::Bob] {
            self.channel(who).hub.know_key(&label, pk.clone());
        }
        for who in users {
            self.channel(*who).user.know_key(&label, pk.clone());
            self.interested.entry(label.clone()).or_default().insert(*who);
        }
        (label, pk, value)
    }

    fn nreg_params(&mut self, r: &Receipt, name: &str, owner: &XOnlyPublicKey, who: Who) -> String {
        let (attest_label, attest_pk, attest_value) = self.share_attest_key(name, owner, &[who]);
        NReg::new(NRegParams { req_id: r.req_id, receipt_pk: r.pk.clone(), attest_label, attest_pk, attest_value, d_receipt: r.deadline })
            .program_name()
    }

    /// Install Alice's honest behaviour for a bond: claim from `d_receipt`
    /// if unattested; fold the bond once attested.
    fn install_bond_policies(&mut self, who: Who, id: u32, attest_label: String, d_receipt: u32) {
        let l1 = attest_label.clone();
        let party = &mut self.channel(who).user;
        party.set_move_policy(id, Box::new(move |ctx: &MoveCtx| (ctx.height >= d_receipt && !(ctx.has)(&l1)).then(|| vec![true])));
        let l2 = attest_label;
        party.set_cancel_policy(id, Box::new(move |ctx: &MoveCtx| (ctx.has)(&l2)));
    }

    /// Alice registers `alice`: commit receipted, bond opened.
    pub fn register(&mut self) -> Result<Receipt> {
        let ev = self.alice_name.commit_event();
        let r = self.hub_receipt(Who::Alice, ev)?;
        let owner = self.alice_key();
        let program = self.nreg_params(&r, "alice", &owner, Who::Alice);
        let deadline = r.deadline + self.alice.params().deadline_offset();
        self.install_bond_policies(Who::Alice, ID_BOND, attest_label("alice", &owner), r.deadline);
        let msgs = self.alice.user.open_contract_with_deadline(ID_BOND, &program, [Amount::ZERO, BOND], deadline)?;
        self.alice.bus(msgs)?;
        self.registering = true;
        self.say(format!("alice sent commit (receipt {}, by {}) and opened bond contract {ID_BOND}", r.req_id, r.deadline));
        Ok(r)
    }

    /// Bob offers to buy `alice` for PRICE: leg 1 in Bob's channel.
    pub fn bob_offers(&mut self, h_sale: u32) -> Result<()> {
        let kb = self.bob_key();
        let (label, pk, value) = self.share_attest_key("alice", &kb, &[Who::Bob, Who::Alice]);
        let program = AttestPay::new(AttestPayParams { prover: Role::Hub, attest_label: label.clone(), attest_pk: pk, attest_value: value }).program_name();
        // the hub presents the attestation as soon as it holds it
        let l = label.clone();
        self.bob.hub.set_move_policy(ID_LEG1, Box::new(move |ctx: &MoveCtx| (ctx.has)(&l).then(|| vec![true])));
        let msgs = self.bob.user.open_contract_with_deadline(ID_LEG1, &program, [PRICE, Amount::ZERO], h_sale)?;
        self.bob.bus(msgs)?;
        self.say(format!("bob opened leg 1 (contract {ID_LEG1}): {PRICE} to the hub if attest(alice, K_B) by {h_sale}"));
        Ok(())
    }

    /// Alice signs the transfer, the hub receipts it, opens leg 2, and Alice opens the transfer bond.
    pub fn alice_sells(&mut self, h_sale: u32) -> Result<Receipt> {
        let kb = self.bob_key();
        let ev = self.alice_name.transfer_event(&kb, h_sale);
        let r = self.hub_receipt(Who::Alice, ev)?;
        let (label, pk, value) = self.share_attest_key("alice", &kb, &[Who::Alice]);
        // leg 2: hub locks PRICE for Alice, gated on the same attestation
        let program = AttestPay::new(AttestPayParams { prover: Role::User, attest_label: label.clone(), attest_pk: pk, attest_value: value }).program_name();
        let l = label.clone();
        self.alice.user.set_move_policy(ID_LEG2, Box::new(move |ctx: &MoveCtx| (ctx.has)(&l).then(|| vec![true])));
        let msgs = self.alice.hub.open_contract_with_deadline(ID_LEG2, &program, [Amount::ZERO, PRICE], h_sale)?;
        self.alice.bus(msgs)?;
        // transfer bond
        let program = self.nreg_params(&r, "alice", &kb, Who::Alice);
        let deadline = r.deadline + self.alice.params().deadline_offset();
        self.install_bond_policies(Who::Alice, ID_TBOND, label, r.deadline);
        let msgs = self.alice.user.open_contract_with_deadline(ID_TBOND, &program, [Amount::ZERO, BOND], deadline)?;
        self.alice.bus(msgs)?;
        self.say(format!("alice signed transfer alice -> K_B valid until {h_sale} (receipt {}, by {}); leg 2 ({ID_LEG2}) and transfer bond ({ID_TBOND}) opened", r.req_id, r.deadline));
        Ok(r)
    }

    // ----- clock -----

    pub fn step(&mut self) -> Result<u32> {
        self.rt.mine(1)?;
        let h = self.height();
        let txs = self.rt.block_txs(h)?;
        // anchors are external to both channels; label them for the logs
        let anchors: Vec<_> = self.hub.lock().unwrap().anchors.iter().map(|a| a.1.txid).collect();
        for tx in &txs {
            if anchors.contains(&tx.compute_txid()) {
                self.alice.external_roles.insert(tx.compute_txid(), "anchor".into());
            }
        }
        self.alice.deliver(h, &txs)?;
        self.bob.deliver(h, &txs)?;
        let stmts = {
            let chain: Arc<dyn lngap_channel::chain::Chain> = self.rt.clone();
            self.hub.lock().unwrap().on_block(h, &txs, &*chain)?
        };
        for (label, value, reveal) in stmts {
            self.relay_statement(&label, value, reveal)?;
        }
        self.application_steps()?;
        self.alice.settle_offchain()?;
        self.bob.settle_offchain()?;
        Ok(h)
    }

    pub fn steps(&mut self, n: u32) -> Result<()> {
        for _ in 0..n {
            self.step()?;
        }
        Ok(())
    }

    pub fn step_until(&mut self, max: u32, mut pred: impl FnMut(&NamesWorld) -> bool) -> Result<u32> {
        for i in 0..max {
            if pred(self) {
                return Ok(i);
            }
            self.step()?;
        }
        anyhow::ensure!(pred(self), "condition not met within {max} blocks");
        Ok(max)
    }

    /// The hub's channel parties learn the statement; interested users get
    /// it by message unless the hub withholds it.
    fn relay_statement(&mut self, label: &str, value: u32, reveal: lngap_lamport::Reveal) -> Result<()> {
        let pk = self.hub.lock().unwrap().statement_pk(label).ok_or_else(|| anyhow!("no key {label}"))?;
        for who in [Who::Alice, Who::Bob] {
            let hp = &mut self.channel(who).hub;
            hp.know_key(label, pk.clone());
            hp.learn_reveal(label, reveal.clone())?;
        }
        let interested: Vec<Who> = self.interested.get(label).map(|s| s.iter().copied().collect()).unwrap_or_default();
        for who in interested {
            if self.withhold_from.contains(&who) {
                self.say(format!("hub WITHHOLDS statement {label} from {who:?}"));
                continue;
            }
            let msg = self.channel(who).hub.statement_msg(label, value)?;
            self.channel(who).bus(vec![msg])?;
        }
        Ok(())
    }

    /// Alice sends the reveal once her commit is anchored.
    fn application_steps(&mut self) -> Result<()> {
        if self.registering && !self.reveal_sent {
            let c = match self.alice_name.commit_event() {
                Event::Commit { c } => c,
                _ => unreachable!(),
            };
            let anchored = self.hub.lock().unwrap().ledger.events.iter().any(|a| matches!(&a.event, Event::Commit { c: cc } if *cc == c));
            if anchored {
                let ev = self.alice_name.reveal_event();
                let r = self.hub_receipt(Who::Alice, ev)?;
                self.reveal_sent = true;
                self.say(format!("alice's commit is anchored; sent reveal (receipt {})", r.req_id));
            }
        }
        Ok(())
    }

    pub fn resolve(&self, name: &str) -> Option<XOnlyPublicKey> {
        self.hub.lock().unwrap().ledger.resolve(name)
    }

    /// Anchor transactions in chain order (genesis first) for the auditor.
    pub fn anchor_txs(&self) -> Result<Vec<(u32, Transaction, bitcoin::OutPoint)>> {
        let anchors = self.hub.lock().unwrap().anchors.clone();
        let mut out = Vec::new();
        for (_, op, _) in anchors {
            if let Some(h) = self.rt.confirmations(&op.txid)? {
                out.push((h, self.rt.get_tx(&op.txid)?, op));
            }
        }
        Ok(out)
    }

    pub fn audit(&self) -> Result<Vec<String>> {
        let anchors = self.anchor_txs()?;
        let hub = self.hub.lock().unwrap();
        let receipts: Vec<_> = hub.receipts.iter().map(|(k, v)| (*k, v.clone())).collect();
        Ok(lngap_names::audit::audit(&hub.anchor_pubkey(), &anchors, &hub.ledger, &receipts))
    }

    pub fn narrative(&self) -> String {
        let mut s = String::new();
        s.push_str("--- world ---\n");
        s.push_str(&self.log.join("\n"));
        s.push_str("\n--- registry ---\n");
        s.push_str(&self.hub.lock().unwrap().log.join("\n"));
        s.push_str("\n=== alice's channel ===\n");
        s.push_str(&self.alice.narrative());
        s.push_str("\n=== bob's channel ===\n");
        s.push_str(&self.bob.narrative());
        s
    }
}

/// Hex-free display helper for program names in logs.
pub trait ProgramName {
    fn program_name(&self) -> String;
}
impl ProgramName for NReg {
    fn program_name(&self) -> String {
        lngap_contract::Program::name(self).to_string()
    }
}
impl ProgramName for AttestPay {
    fn program_name(&self) -> String {
        lngap_contract::Program::name(self).to_string()
    }
}

pub const _STATEMENT_BITS: usize = STATEMENT_BITS;
