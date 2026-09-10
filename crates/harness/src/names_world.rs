//! Two channels (Alice–hub, Bob–hub), one registry operator, one clock.
//! The world mines (anchors in their own blocks, as a hub with a miner
//! would), delivers blocks to every party and to the registry, serves the
//! registry's proof data to everyone (the public ledger), and performs the
//! users' *application* steps (send the reveal once the commit is
//! anchored). It never tells a party what to broadcast.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, ensure, Result};
use bitcoin::key::XOnlyPublicKey;
use bitcoin::{Amount, OutPoint, Transaction};
use bitcoincore_rpc::RpcApi;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_lamport::bits_to_uint;
use lngap_names::anchor::verify_anchor_chain;
use lngap_names::hub::{NamesHub, Receipt};
use lngap_names::programs::{AnchorPayParams, NRegParams};
use lngap_names::registry::Event;
use lngap_names::statements::receipt_label;
use lngap_names::user::NamesUser;
use lngap_names::{registry_programs, AnchorPay, NReg, ServedData};
use lngap_party::draft::{downcast, Change};
use lngap_party::{ChangeCtx, MoveCtx};
use lngap_spv::chain::{MerklePath, RawHeader};
use lngap_spv::HeaderShape;
use tracing::info;

use crate::{init_log, Harness};

/// Contracts carrying a 128-step claim reserve ~27k sat of pre-signed
/// dispute fees per depth (D8: 1000 sat per transaction), so bonds and
/// payments are 40k here.
pub const BOND: Amount = Amount::from_sat(40_000);
pub const PRICE: Amount = Amount::from_sat(40_000);
pub const ID_BOND: u32 = 10;
pub const ID_RBOND: u32 = 11;
pub const ID_LEG1: u32 = 20;
pub const ID_LEG2: u32 = 21;
pub const ID_TBOND: u32 = 22;
/// Blocks after the promised anchor height from which the user may claim.
pub const GRACE: u32 = 2;

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
    /// Proof data everyone can read (the public ledger and chain).
    pub store: ServedData,
    /// Slots whose entry the public ledger shows anchored.
    anchored: Arc<Mutex<HashSet<String>>>,
    pub receipts: HashMap<u32, Receipt>,
    pub genesis: OutPoint,
    pub genesis_height: u32,
    /// An anchor the hub built, to be mined in the next block.
    pending_anchor: Option<Transaction>,
    /// Scenario fault: the hub mines its anchors on a private fork.
    pub fork: bool,
    /// Slots anchored on the fork, with the receipt height (for the refutation data).
    forked: Vec<(String, u32, usize)>,
    reveal_sent: bool,
    pub registering: bool,
    commit_req: Option<u32>,
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
        let store = ServedData::default();
        let alice = Harness::with_regtest(rt.clone(), &format!("{label}/alice"), registry_programs(store.clone()))?;
        let bob = Harness::with_regtest(rt.clone(), &format!("{label}/bob"), registry_programs(store.clone()))?;
        let alice_name = NamesUser::new(&Seed::from_label(&format!("{label}/alice/name")), "alice");
        let bob_user = NamesUser::new(&Seed::from_label(&format!("{label}/bob/name")), "alice");
        let mut w = NamesWorld {
            rt,
            alice,
            bob,
            hub: Arc::new(Mutex::new(hub)),
            alice_name,
            bob_user,
            store,
            anchored: Arc::new(Mutex::new(HashSet::new())),
            receipts: HashMap::new(),
            genesis: op,
            genesis_height,
            pending_anchor: None,
            fork: false,
            forked: Vec::new(),
            reveal_sent: false,
            registering: false,
            commit_req: None,
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
    pub fn slot(req_id: u32) -> String {
        format!("req{req_id}")
    }
    pub fn is_anchored(&self, req_id: u32) -> bool {
        self.anchored.lock().unwrap().contains(&Self::slot(req_id))
    }

    fn raw_header(&self, height: u32) -> Result<RawHeader> {
        let hash = self.rt.rpc.get_block_hash(u64::from(height))?;
        Ok(RawHeader::from_header(&self.rt.rpc.get_block_header(&hash)?))
    }

    /// The hub's change policy on both channels: bonds only for receipts it
    /// issued; refuse a "receipted, not anchored" claim when it can prove
    /// inclusion (it will do so on-chain instead); always agree to fold.
    /// `veto` adds scenario-specific refusals on top.
    pub fn set_hub_policy(&mut self, who: Who, veto: Option<Box<dyn Fn(&ChangeCtx) -> Result<()> + Send + Sync>>) {
        let hub = self.hub.clone();
        let store = self.store.clone();
        let policy = Box::new(move |ctx: &ChangeCtx| -> Result<()> {
            if let Some(v) = &veto {
                v(ctx)?;
            }
            match ctx.change {
                Change::Open { program, stakes, .. } => {
                    if let Some(p) = program.strip_prefix("nreg:") {
                        let params: NRegParams = serde_json::from_str(p)?;
                        let h = hub.lock().unwrap();
                        let r = h.receipts.get(&params.req_id).ok_or_else(|| anyhow!("no receipt {} was issued", params.req_id))?;
                        ensure!(r.shape == params.shape, "bond terms do not match the receipt");
                        ensure!(stakes[Role::Hub.idx()] <= BOND && stakes[Role::User.idx()] == Amount::ZERO, "bond terms");
                        Ok(())
                    } else if program.starts_with("anchorpay:") {
                        ensure!(stakes[Role::Hub.idx()] == Amount::ZERO, "the hub does not lock into user-opened payments");
                        Ok(())
                    } else {
                        anyhow::bail!("unknown program")
                    }
                }
                Change::Move { id, .. } => {
                    let c = ctx.current.contract(*id).ok_or_else(|| anyhow!("no contract {id}"))?;
                    let inst = downcast(c);
                    let name = inst.program.name().to_string();
                    if let Some(p) = name.strip_prefix("nreg:") {
                        let params: NRegParams = serde_json::from_str(p)?;
                        if bits_to_uint(&inst.state) == 0 && store.has(&format!("{}/incl", params.slot)) {
                            anyhow::bail!("I can prove request {} is anchored; answering on-chain", params.req_id);
                        }
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

    /// The user's check before trusting a receipt: walk the anchor chain from
    /// genesis through every anchor it can see (confirmed, and the one in the
    /// mempool if any); the receipt's `prev_anchor` must be that chain's tip.
    fn user_checks_tip(&self, prev_anchor: OutPoint) -> Result<()> {
        let mut txs: Vec<Transaction> = self.anchor_txs()?.into_iter().map(|a| a.1).collect();
        if let Some(p) = &self.pending_anchor {
            txs.push(p.clone());
        }
        let (tip, _) = verify_anchor_chain(self.genesis, &txs)?;
        ensure!(tip == prev_anchor, "the receipt names tip {prev_anchor} but the anchor chain's tip is {tip}");
        Ok(())
    }

    fn hub_receipt(&mut self, who: Who, event: Event) -> Result<Receipt> {
        let h = self.height();
        let cp = self.raw_header(h)?;
        let r = self.hub.lock().unwrap().receipt(event, h, cp.digest(), cp.nbits())?;
        self.user_checks_tip(r.shape.prev_anchor)?;
        let label = receipt_label(r.req_id);
        let party = &mut self.channel(who).user;
        party.know_key(&label, r.pk.clone());
        party.learn_reveal(&label, r.reveal.clone())?;
        self.receipts.insert(r.req_id, r.clone());
        Ok(r)
    }

    fn nreg_program(&self, r: &Receipt) -> String {
        NReg::new(NRegParams { req_id: r.req_id, receipt_pk: r.pk.clone(), d_receipt: r.promised_height + GRACE, shape: r.shape.clone(), slot: Self::slot(r.req_id) }, self.store.clone()).program_name()
    }

    /// Install honest bond behaviour: the user claims from `d_receipt` if
    /// the entry is not anchored and folds the bond once it is, and
    /// refutes the hub's chain if a heavier one is served; the hub answers
    /// a claim with its inclusion proof.
    fn install_bond_policies(&mut self, who: Who, id: u32, req_id: u32, d_receipt: u32) {
        let slot = Self::slot(req_id);
        let anchored = self.anchored.clone();
        let anchored2 = self.anchored.clone();
        let (s1, s2, s3) = (slot.clone(), slot.clone(), slot.clone());
        let store = self.store.clone();
        let store2 = self.store.clone();
        let party = &mut self.channel(who).user;
        party.set_move_policy(
            id,
            Box::new(move |ctx: &MoveCtx| match bits_to_uint(ctx.state) {
                0 => (ctx.height >= d_receipt && !anchored.lock().unwrap().contains(&s1)).then(|| vec![true]),
                2 => store.has(&format!("{s3}/refute")).then(|| vec![true]),
                _ => None,
            }),
        );
        party.set_cancel_policy(id, Box::new(move |ctx: &MoveCtx| bits_to_uint(ctx.state) == 0 && anchored2.lock().unwrap().contains(&s2)));
        self.channel(who).hub.set_move_policy(id, Box::new(move |ctx: &MoveCtx| (bits_to_uint(ctx.state) == 1 && store2.has(&format!("{slot}/incl"))).then(|| vec![true])));
    }

    fn open_bond(&mut self, who: Who, id: u32, r: &Receipt) -> Result<()> {
        let program = self.nreg_program(r);
        let d_receipt = r.promised_height + GRACE;
        let deadline = d_receipt + self.alice.params().deadline_offset() + 40;
        self.install_bond_policies(who, id, r.req_id, d_receipt);
        let msgs = self.channel(who).user.open_contract_with_deadline(id, &program, [Amount::ZERO, BOND], deadline)?;
        self.channel(who).bus(msgs)?;
        Ok(())
    }

    /// Alice registers `alice`: commit receipted, bond opened.
    pub fn register(&mut self) -> Result<Receipt> {
        let ev = self.alice_name.commit_event();
        let r = self.hub_receipt(Who::Alice, ev)?;
        self.open_bond(Who::Alice, ID_BOND, &r)?;
        self.registering = true;
        self.commit_req = Some(r.req_id);
        self.say(format!("alice sent commit (receipt {}, anchor promised at {}) and opened bond contract {ID_BOND}", r.req_id, r.promised_height));
        Ok(r)
    }

    /// Bob offers to buy `alice` for PRICE (an off-chain intent; the
    /// contracts open once Alice signs, since they name the transfer entry).
    pub fn bob_offers(&mut self, h_sale: u32) -> Result<()> {
        self.say(format!("bob offers {PRICE} for alice, transfer valid until {h_sale}"));
        Ok(())
    }

    /// Alice signs the transfer, the hub receipts it; Bob opens leg 1 (hub
    /// proves inclusion to get paid), the hub opens leg 2 (Alice proves
    /// inclusion to get paid), and Alice opens the transfer bond.
    pub fn alice_sells(&mut self, h_sale: u32) -> Result<Receipt> {
        let kb = self.bob_key();
        let ev = self.alice_name.transfer_event(&kb, h_sale);
        let r = self.hub_receipt(Who::Alice, ev)?;
        let slot = Self::slot(r.req_id);
        let (s1, s2) = (slot.clone(), slot.clone());
        // leg 1 in Bob's channel: PRICE to the hub if it proves the transfer anchored
        let program = AnchorPay::new(AnchorPayParams { prover: Role::Hub, shape: r.shape.clone(), slot: slot.clone() }, self.store.clone()).program_name();
        let store = self.store.clone();
        self.bob.hub.set_move_policy(ID_LEG1, Box::new(move |ctx: &MoveCtx| (bits_to_uint(ctx.state) == 0 && store.has(&format!("{s1}/incl"))).then(|| vec![true])));
        let store = self.store.clone();
        self.bob.user.set_move_policy(ID_LEG1, Box::new(move |ctx: &MoveCtx| (bits_to_uint(ctx.state) == 1 && store.has(&format!("{s2}/refute"))).then(|| vec![true])));
        let msgs = self.bob.user.open_contract_with_deadline(ID_LEG1, &program, [PRICE, Amount::ZERO], h_sale)?;
        self.bob.bus(msgs)?;
        // leg 2 in Alice's channel: the hub locks PRICE for Alice, gated on the same proof
        let program = AnchorPay::new(AnchorPayParams { prover: Role::User, shape: r.shape.clone(), slot: slot.clone() }, self.store.clone()).program_name();
        let store = self.store.clone();
        let s3 = slot.clone();
        self.alice.user.set_move_policy(ID_LEG2, Box::new(move |ctx: &MoveCtx| (bits_to_uint(ctx.state) == 0 && store.has(&format!("{s3}/incl"))).then(|| vec![true])));
        let msgs = self.alice.hub.open_contract_with_deadline(ID_LEG2, &program, [Amount::ZERO, PRICE], h_sale)?;
        self.alice.bus(msgs)?;
        // the transfer bond
        self.open_bond(Who::Alice, ID_TBOND, &r)?;
        self.say(format!("alice signed transfer alice -> K_B valid until {h_sale} (receipt {}, anchor promised at {}); leg 1 ({ID_LEG1}), leg 2 ({ID_LEG2}) and transfer bond ({ID_TBOND}) opened", r.req_id, r.promised_height));
        Ok(r)
    }

    // ----- clock -----

    pub fn step(&mut self) -> Result<u32> {
        let anchor = self.pending_anchor.take();
        let h = match (&anchor, self.fork) {
            (Some(tx), false) => {
                let h = self.rt.mine_with(std::slice::from_ref(tx))?;
                self.alice.external_roles.insert(tx.compute_txid(), "anchor".into());
                self.bob.external_roles.insert(tx.compute_txid(), "anchor".into());
                h
            }
            (Some(tx), true) => {
                // the hub's private fork: mine the anchor block, let the hub see it, then orphan it
                let h = self.rt.mine_with(std::slice::from_ref(tx))?;
                let fork_txs = self.rt.block_txs(h)?;
                let fork_hash = self.rt.rpc.get_block_hash(u64::from(h))?;
                self.hub_sees(h, &fork_txs)?;
                self.say(format!("hub mined its anchor on a PRIVATE FORK at {h} ({})", fork_hash));
                self.rt.rpc.invalidate_block(&fork_hash)?;
                self.rt.mine(1)?;
                h
            }
            (None, _) => {
                self.rt.mine(1)?;
                self.height()
            }
        };
        let txs = self.rt.block_txs(h)?;
        self.alice.deliver(h, &txs)?;
        self.bob.deliver(h, &txs)?;
        if !(anchor.is_some() && self.fork) {
            self.hub_sees(h, &txs)?;
        }
        self.serve_refutations()?;
        self.application_steps()?;
        self.alice.settle_offchain()?;
        self.bob.settle_offchain()?;
        Ok(h)
    }

    /// The registry sees a block: anchors due are built; confirmed anchors
    /// have their proof data served.
    fn hub_sees(&mut self, h: u32, txs: &[Transaction]) -> Result<()> {
        let (next, mut confirmed) = self.hub.lock().unwrap().on_block(h, txs)?;
        self.pending_anchor = next;
        // requests the hub promised for this anchor but left out: the hub still
        // serves "proof data" for them (a path to the empty leaf), which is
        // what a hub trying to bluff its way through would present
        let anchored_now = self.hub.lock().unwrap().anchors.last().is_some_and(|a| a.height == h && a.tx.is_some());
        if anchored_now {
            let omitted: Vec<u32> = self.hub.lock().unwrap().receipts.iter().filter(|(_, r)| r.promised_height == h && r.anchored_at.is_none()).map(|(id, _)| *id).collect();
            confirmed.extend(omitted);
        }
        for req_id in confirmed {
            self.serve_inclusion(req_id, h, txs)?;
        }
        Ok(())
    }

    /// Build and serve the inclusion proof data for a request anchored at `h`.
    fn serve_inclusion(&mut self, req_id: u32, h: u32, txs: &[Transaction]) -> Result<()> {
        let r = self.receipts.get(&req_id).ok_or_else(|| anyhow!("no receipt {req_id}"))?.clone();
        let n = r.shape.chain.n_headers as u32;
        let headers: Vec<RawHeader> = (h + 1 - n..=h).map(|x| self.raw_header(x)).collect::<Result<_>>()?;
        let txids: Vec<bitcoin::Txid> = txs.iter().map(|t| t.compute_txid()).collect();
        let anchor_txid = self.hub.lock().unwrap().anchors.last().and_then(|a| a.tx.as_ref().map(|t| t.compute_txid())).ok_or_else(|| anyhow!("no anchor"))?;
        let index = txids.iter().position(|t| *t == anchor_txid).ok_or_else(|| anyhow!("anchor not in its block"))?;
        let path = MerklePath::for_tx(&txids, index);
        ensure!(path.sides == r.shape.merkle_sides, "the anchor's position in its block differs from the promised one");
        let data = self.hub.lock().unwrap().inclusion_data(req_id, headers, path.siblings)?;
        let slot = Self::slot(req_id);
        self.store.put(&format!("{slot}/incl"), r.shape.data(&data));
        // the public ledger shows the entry iff the hub actually included it —
        // and, for the users' nodes, iff the anchor is in their chain (not on the hub's private fork)
        let included = self.hub.lock().unwrap().ledger.as_of(h).path(r.shape.key).leaf != lngap_spv::ledger::EMPTY_LEAF;
        if included && !self.fork {
            self.anchored.lock().unwrap().insert(slot.clone());
        }
        if self.fork {
            let receipt_height = h - n;
            self.forked.push((slot.clone(), receipt_height, n as usize));
        }
        self.say(format!("proof data for request {req_id} served ({})", if !included { "entry NOT in the anchored ledger" } else if self.fork { "entry anchored on the hub's fork only" } else { "entry anchored" }));
        Ok(())
    }

    /// Serve heavier-chain refutations for fork-anchored slots once the real chain is one longer.
    fn serve_refutations(&mut self) -> Result<()> {
        let h = self.height();
        for (slot, receipt_height, n) in self.forked.clone() {
            let key = format!("{slot}/refute");
            if self.store.has(&key) || h < receipt_height + n as u32 + 1 {
                continue;
            }
            let headers: Vec<RawHeader> = (receipt_height + 1..=receipt_height + n as u32 + 1).map(|x| self.raw_header(x)).collect::<Result<_>>()?;
            let cp = self.raw_header(receipt_height)?;
            let shape = HeaderShape { checkpoint: cp.digest(), nbits: cp.nbits(), n_headers: n + 1 };
            self.store.put(&key, shape.data(&headers));
            self.say(format!("the real chain is heavier than the hub's fork: refutation data served for {slot}"));
        }
        Ok(())
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
        ensure!(pred(self), "condition not met within {max} blocks");
        Ok(max)
    }

    /// Alice sends the reveal once her commit is anchored, with its own bond.
    fn application_steps(&mut self) -> Result<()> {
        if self.registering && !self.reveal_sent {
            let anchored = self.commit_req.is_some_and(|id| self.is_anchored(id));
            if anchored {
                let ev = self.alice_name.reveal_event();
                let r = self.hub_receipt(Who::Alice, ev)?;
                self.open_bond(Who::Alice, ID_RBOND, &r)?;
                self.reveal_sent = true;
                self.say(format!("alice's commit is anchored; sent reveal (receipt {}, anchor promised at {}) and opened bond {ID_RBOND}", r.req_id, r.promised_height));
            }
        }
        Ok(())
    }

    pub fn resolve(&self, name: &str) -> Option<XOnlyPublicKey> {
        self.hub.lock().unwrap().ledger.resolve(name)
    }

    /// Anchor transactions in chain order (after genesis) for the auditor.
    pub fn anchor_txs(&self) -> Result<Vec<(u32, Transaction, OutPoint)>> {
        let anchors = self.hub.lock().unwrap().anchors.clone();
        Ok(anchors.into_iter().filter_map(|a| a.tx.map(|tx| (a.height, tx, a.outpoint))).collect())
    }

    pub fn audit(&self) -> Result<Vec<String>> {
        let anchors = self.anchor_txs()?;
        let hub = self.hub.lock().unwrap();
        let receipts: Vec<_> = hub.receipts.iter().map(|(k, v)| (*k, v.clone())).collect();
        Ok(lngap_names::audit::audit(self.genesis, &anchors, &hub.ledger, &receipts))
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

/// Program names for logs and opens.
pub trait ProgramName {
    fn program_name(&self) -> String;
}
impl ProgramName for NReg {
    fn program_name(&self) -> String {
        lngap_contract::Program::name(self).to_string()
    }
}
impl ProgramName for AnchorPay {
    fn program_name(&self) -> String {
        lngap_contract::Program::name(self).to_string()
    }
}

