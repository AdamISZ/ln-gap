//! Two channels (Alice–hub, Bob–hub), one fact-chain miner M, one registry hub.
//!
//! The world mines Bitcoin blocks (for channel timelocks) and fact-chain blocks
//! (for registry inclusion). The hub promises inclusion by a fact-chain height,
//! submits entries to the miner, and serves proof data once confirmed. Users
//! verify fact-chain blocks natively and fold bonds once entries are confirmed.
//!
//! Stage 2: claims carry ClaimSpecs and disputes run the on-chain bisection.
//! The fact chain has one entry per block (no Merkle tree). W_max = 100;
//! checkpoint refresh happens at cooperative channel updates (not yet
//! implemented — the PoC scenarios are short enough that W stays small).
//! N9 fork mode: the hub's entry is mined on a private fork (see step_fork).

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, ensure, Result};
use bitcoin::key::XOnlyPublicKey;
use bitcoin::Amount;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_factchain::{ChainClient, Miner};
use lngap_lamport::bits_to_uint;
use lngap_names::registry::{Event, N};
use lngap_names::ServedData;
use lngap_names_fc::{
    registry_programs, AnchorPayFc, AnchorPayFcParams, FcHub, FcPromise, NRegFc, NRegFcParams,
    NamesUser,
};
use lngap_party::draft::{downcast, Change};
use lngap_party::{ChangeCtx, MoveCtx};
use lngap_contract::Contract;
use tracing::info;

use crate::{init_log, Harness};

/// Bond size. Without the bisection fee reserve (stage 1 has no dispute chain),
/// this could be smaller, but we keep 40k for comparison with the old design.
pub const BOND: Amount = Amount::from_sat(40_000);
pub const PRICE: Amount = Amount::from_sat(40_000);
pub const ID_BOND: u32 = 10;
pub const ID_RBOND: u32 = 11;
pub const ID_LEG1: u32 = 20;
pub const ID_LEG2: u32 = 21;
pub const ID_TBOND: u32 = 22;
pub const GRACE: u32 = 2;
/// Maximum headers between checkpoint and claim (the W_max bound).
pub const W_MAX: u32 = 100;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Who {
    Alice,
    Bob,
}

pub struct FcWorld {
    pub rt: Arc<Regtest>,
    pub alice: Harness,
    pub bob: Harness,
    pub hub: Arc<Mutex<FcHub>>,
    /// The fact-chain miner (entity M, not a channel participant).
    pub miner: Miner,
    /// Scenario fault (N9): the hub's entry is mined on a private fork only
    /// the hub sees; the real chain advances past it and the world serves a
    /// heavier-chain refutation.
    pub fork: bool,
    /// The hub's private-fork miner (starts from genesis like the real miner).
    pub fork_miner: Miner,
    /// Requests anchored on the fork: (req_id, checkpoint_height, n_headers on the fork).
    forked: Vec<(u32, u32, usize)>,
    /// The fact-chain genesis digest and height.
    pub fc_genesis_digest: [u8; 20],
    pub fc_genesis_height: u32,
    /// Each party's fact-chain client.
    pub alice_fc: ChainClient,
    pub bob_fc: ChainClient,
    pub hub_fc: ChainClient,
    /// Request IDs confirmed on the fact chain (shared with policies).
    confirmed: Arc<Mutex<HashSet<u32>>>,
    /// Promises issued by the hub.
    pub promises: HashMap<u32, FcPromise>,
    /// The entry currently being mined (one per block, stage 1).
    pub pending_entry: Option<Vec<u8>>,
    /// The event for the pending entry (for the ledger).
    pending_event: Option<Event>,
    pub alice_name: NamesUser,
    pub bob_user: NamesUser,
    /// Whether Alice has sent her reveal yet.
    reveal_sent: bool,
    pub registering: bool,
    commit_req: Option<u32>,
    /// Served proof data for claims (shared with NRegFc programs).
    pub store: ServedData,
    pub log: Vec<String>,
}

impl FcWorld {
    pub fn new(label: &str) -> Result<FcWorld> {
        init_log();
        let rt = Arc::new(Regtest::start()?);

        // Fact-chain genesis
        let genesis_block = lngap_factchain::genesis();
        let fc_genesis_digest = genesis_block.header.digest();
        let fc_genesis_height = 0;

        // Miner starts from genesis
        let miner = Miner::new(fc_genesis_digest, fc_genesis_height);

        // Hub
        let hub = Arc::new(Mutex::new(FcHub::new()));

        // Channels
        let store_confirmed = Arc::new(Mutex::new(HashSet::new()));
        let store = ServedData::default();
        let reg = registry_programs(store.clone());
        let alice = Harness::with_regtest(rt.clone(), &format!("{label}/alice"), reg)?;
        let bob = Harness::with_regtest(rt.clone(), &format!("{label}/bob"), registry_programs(store.clone()))?;

        // Fact-chain clients (all start from genesis)
        let alice_fc = ChainClient::from_checkpoint(fc_genesis_height, fc_genesis_digest);
        let bob_fc = ChainClient::from_checkpoint(fc_genesis_height, fc_genesis_digest);
        let hub_fc = ChainClient::from_checkpoint(fc_genesis_height, fc_genesis_digest);

        let alice_name = NamesUser::new(
            &Seed::from_label(&format!("{label}/alice/name")),
            "alice",
        );
        let bob_user = NamesUser::new(
            &Seed::from_label(&format!("{label}/bob/name")),
            "alice",
        );

        let mut w = FcWorld {
            rt,
            alice,
            bob,
            hub,
            miner,
            fork: false,
            fork_miner: Miner::new(fc_genesis_digest, fc_genesis_height),
            forked: Vec::new(),
            fc_genesis_digest,
            fc_genesis_height,
            alice_fc,
            bob_fc,
            hub_fc,
            confirmed: store_confirmed,
            promises: HashMap::new(),
            pending_entry: None,
            pending_event: None,
            alice_name,
            bob_user,
            reveal_sent: false,
            registering: false,
            commit_req: None,
            store,
            log: Vec::new(),
        };
        w.install_hub_policies();
        w.sync_heights();
        Ok(w)
    }

    fn say(&mut self, s: String) {
        info!(world = "fc-names", "{s}");
        self.log.push(format!("[world @ {}] {s}", self.height()));
    }

    pub fn height(&self) -> u32 {
        self.rt.height().unwrap()
    }

    /// Fact-chain height (genesis + blocks mined).
    pub fn fc_height(&self) -> u32 {
        self.fc_genesis_height + self.alice_fc.chain_length() as u32
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

    pub fn is_confirmed(&self, req_id: u32) -> bool {
        self.confirmed.lock().unwrap().contains(&req_id)
    }

    // ----- hub policies -----

    /// The hub's change policy: bonds only for promises it made, on their terms.
    pub fn set_hub_policy(
        &mut self,
        who: Who,
        veto: Option<Box<dyn Fn(&ChangeCtx) -> Result<()> + Send + Sync>>,
    ) {
        let hub = self.hub.clone();
        let policy = Box::new(move |ctx: &ChangeCtx| -> Result<()> {
            if let Some(v) = &veto {
                v(ctx)?;
            }
            match ctx.change {
                Change::Open { program, stakes, .. } => {
                    if let Some(p) = program.strip_prefix("nreg-fc:") {
                        let params: NRegFcParams = serde_json::from_str(p)?;
                        let h = hub.lock().unwrap();
                        let r = h.promises.get(&params.req_id).ok_or_else(|| {
                            anyhow!("no promise {} was made", params.req_id)
                        })?;
                        ensure!(
                            r.checkpoint == params.checkpoint
                                && r.checkpoint_height == params.checkpoint_height
                                && r.h_max + GRACE == params.claim_from,
                            "bond terms do not match the promise"
                        );
                        ensure!(
                            stakes[Role::Hub.idx()] <= BOND && stakes[Role::User.idx()] == Amount::ZERO,
                            "bond terms"
                        );
                        Ok(())
                    } else if program.starts_with("anchorpay-fc:") {
                        ensure!(
                            stakes[Role::Hub.idx()] == Amount::ZERO,
                            "the hub does not lock into user-opened payments"
                        );
                        Ok(())
                    } else {
                        anyhow::bail!("unknown program")
                    }
                }
                Change::Move { id, .. } => {
                    // The hub answers a claim with its move (state → Refuted)
                    // if the entry is confirmed on the fact chain.
                    let c = ctx.current.contract(*id).ok_or_else(|| anyhow!("no contract {id}"))?;
                    let inst = downcast(c);
                    let name = inst.program.name().to_string();
                    if let Some(p) = name.strip_prefix("nreg-fc:") {
                        let params: NRegFcParams = serde_json::from_str(p)?;
                        if bits_to_uint(&inst.state) == 1 {
                            // Claimed state: the hub should answer if the entry is confirmed
                            let h = hub.lock().unwrap();
                            if h.is_confirmed(params.req_id) {
                                return Ok(());
                            }
                            anyhow::bail!("entry not confirmed; cannot prove inclusion");
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

    // ----- registry interactions -----

    /// Request → promise. The hub promises inclusion by h_max (in Bitcoin
    /// height, since the fact chain advances 1:1 with Bitcoin in the PoC).
    fn hub_promise(&mut self, event: Event, window_from: Option<u32>) -> Result<FcPromise> {
        let btc_h = self.height();
        let fc_h = self.fc_height();
        let checkpoint = self.hub_fc.tip();
        let checkpoint_height = self.hub_fc.tip_height();
        let h_max = btc_h + W_MAX;
        let p = self.hub.lock().unwrap().promise(
            event.clone(),
            h_max,
            checkpoint,
            checkpoint_height,
        )?;
        if !self.hub.lock().unwrap().faults.no_submit
            && self.hub.lock().unwrap().faults.omit_req != Some(p.req_id)
        {
            self.pending_entry = Some(p.entry.to_vec());
            self.pending_event = Some(event);
        }
        self.user_checks_promise(&p, window_from)?;
        self.promises.insert(p.req_id, p.clone());
        Ok(p)
    }

    /// The user's checks before opening a bond: the reveal window.
    fn user_checks_promise(&self, _p: &FcPromise, window_from: Option<u32>) -> Result<()> {
        if let Some(h1) = window_from {
            ensure!(
                _p.h_max <= h1 + N as u32 + W_MAX,
                "the promised h_max is outside the reveal window"
            );
        }
        Ok(())
    }
    fn nreg_program(&self, p: &FcPromise) -> String {
        NRegFc::new(
            NRegFcParams {
                req_id: p.req_id,
                claim_from: p.h_max + GRACE,
                checkpoint: p.checkpoint,
                checkpoint_height: p.checkpoint_height,
                h_max: p.h_max,
            },
            self.store.clone(),
        )
        .name()
        .to_string()
    }

    /// Install honest bond behaviour: the user claims from `claim_from` if
    /// the entry is not confirmed, folds the bond once it is, and refutes the
    /// hub's chain when heavier-chain data is served (N9). The hub answers a
    /// claim (state 1 → 2) when its inclusion proof data exists — in fork
    /// mode that data covers the hub's fork, not the users' chain.
    fn install_bond_policies(&mut self, who: Who, id: u32, req_id: u32, claim_from: u32) {
        let confirmed = self.confirmed.clone();
        let confirmed2 = self.confirmed.clone();
        let store = self.store.clone();
        let store2 = self.store.clone();
        let party = &mut self.channel(who).user;
        party.set_move_policy(
            id,
            Box::new(move |ctx: &MoveCtx| {
                match bits_to_uint(ctx.state) {
                    0 => {
                        (ctx.height >= claim_from
                            && !confirmed.lock().unwrap().contains(&req_id))
                            .then(|| vec![true])
                    }
                    2 => {
                        // Refuted: refute with the heavier real chain, once the
                        // world has served the refutation data (N9).
                        store.has(&format!("{req_id}/refute")).then(|| vec![true])
                    }
                    _ => None,
                }
            }),
        );
        party.set_cancel_policy(
            id,
            Box::new(move |_ctx: &MoveCtx| {
                confirmed2.lock().unwrap().contains(&req_id)
            }),
        );
        // Hub move policy: answer a claim (state 1 → 2) if the entry is confirmed
        self.channel(who).hub.set_move_policy(
            id,
            Box::new(move |ctx: &MoveCtx| {
                (bits_to_uint(ctx.state) == 1 && store2.has(&format!("{req_id}/incl")))
                    .then(|| vec![true])
            }),
        );
    }

    fn open_bond(&mut self, who: Who, id: u32, p: &FcPromise) -> Result<()> {
        let program = self.nreg_program(p);
        let claim_from = p.h_max + GRACE;
        let deadline = claim_from + self.alice.params().deadline_offset() + 40;
        self.install_bond_policies(who, id, p.req_id, claim_from);
        let msgs = self
            .channel(who)
            .user
            .open_contract_with_deadline(id, &program, [Amount::ZERO, BOND], deadline)?;
        self.channel(who).bus(msgs)?;
        Ok(())
    }

    /// Alice registers `alice`: commit requested, promise checked, bond opened.
    pub fn register(&mut self) -> Result<FcPromise> {
        let ev = self.alice_name.commit_event();
        let p = self.hub_promise(ev, None)?;
        self.open_bond(Who::Alice, ID_BOND, &p)?;
        self.registering = true;
        self.commit_req = Some(p.req_id);
        self.say(format!(
            "alice sent commit (request {}, h_max {}) and opened bond contract {ID_BOND}",
            p.req_id, p.h_max
        ));
        Ok(p)
    }

    /// Bob offers to buy `alice` for PRICE.
    pub fn bob_offers(&mut self, h_sale: u32) -> Result<()> {
        self.say(format!("bob offers {PRICE} for alice, transfer valid until {h_sale}"));
        Ok(())
    }

    /// Alice signs the transfer; Bob opens leg 1, the hub opens leg 2,
    /// and Alice opens the transfer bond.
    pub fn alice_sells(&mut self, h_sale: u32) -> Result<FcPromise> {
        let kb = self.bob_key();
        let ev = self.alice_name.transfer_event(&kb, h_sale);
        let r = self.hub_promise(ev, None)?;

        // leg 1 in Bob's channel: PRICE to the hub if it proves inclusion
        let program = AnchorPayFc::new(AnchorPayFcParams {
            prover: Role::Hub,
            checkpoint: r.checkpoint,
            checkpoint_height: r.checkpoint_height,
            h_max: r.h_max,
        })
        .name()
        .to_string();
        let confirmed1 = self.confirmed.clone();
        self.bob.hub.set_move_policy(
            ID_LEG1,
            Box::new(move |ctx: &MoveCtx| {
                (bits_to_uint(ctx.state) == 0 && confirmed1.lock().unwrap().contains(&r.req_id))
                    .then(|| vec![true])
            }),
        );
        let msgs = self
            .bob
            .user
            .open_contract_with_deadline(ID_LEG1, &program, [PRICE, Amount::ZERO], h_sale)?;
        self.bob.bus(msgs)?;

        // leg 2 in Alice's channel: the hub locks PRICE for Alice
        let program = AnchorPayFc::new(AnchorPayFcParams {
            prover: Role::User,
            checkpoint: r.checkpoint,
            checkpoint_height: r.checkpoint_height,
            h_max: r.h_max,
        })
        .name()
        .to_string();
        let confirmed2 = self.confirmed.clone();
        self.alice.user.set_move_policy(
            ID_LEG2,
            Box::new(move |ctx: &MoveCtx| {
                (bits_to_uint(ctx.state) == 0 && confirmed2.lock().unwrap().contains(&r.req_id))
                    .then(|| vec![true])
            }),
        );
        let msgs = self
            .alice
            .hub
            .open_contract_with_deadline(ID_LEG2, &program, [Amount::ZERO, PRICE], h_sale)?;
        self.alice.bus(msgs)?;

        // the transfer bond
        self.open_bond(Who::Alice, ID_TBOND, &r)?;
        self.say(format!(
            "alice signed transfer alice -> K_B valid until {h_sale} (request {}, h_max {}); leg 1 ({ID_LEG1}), leg 2 ({ID_LEG2}) and transfer bond ({ID_TBOND}) opened",
            r.req_id, r.h_max
        ));
        Ok(r)
    }

    // ----- clock -----

    pub fn step(&mut self) -> Result<u32> {
        // 1. Mine a Bitcoin block (for channel timelocks)
        self.rt.mine(1)?;
        let btc_h = self.height();
        let txs = self.rt.block_txs(btc_h)?;
        self.alice.deliver(btc_h, &txs)?;
        self.bob.deliver(btc_h, &txs)?;

        // 2. Mine a fact-chain block (if there's a pending entry)
        if self.fork {
            self.step_fork()?;
        } else if let Some(entry) = self.pending_entry.take() {
            self.miner.submit(entry);
            let block = self.miner.mine_next().expect("mine");
            let fc_h = block.header.height();

            // All clients verify the block
            self.alice_fc.verify_and_append(&block).map_err(|e| anyhow!(e))?;
            self.bob_fc.verify_and_append(&block).map_err(|e| anyhow!(e))?;
            self.hub_fc.verify_and_append(&block).map_err(|e| anyhow!(e))?;

            // Hub checks which promises are confirmed
            self.hub.lock().unwrap().on_block(fc_h, &block.entry);

            // Update the shared confirmed set and serve proof data
            let newly_confirmed: Vec<u32> = {
                let hub = self.hub.lock().unwrap();
                hub.promises.keys()
                    .filter(|id| hub.is_confirmed(**id))
                    .copied()
                    .collect()
            };
            for req_id in &newly_confirmed {
                self.confirmed.lock().unwrap().insert(*req_id);
            }
            for req_id in &newly_confirmed {
                let fc = self.hub_fc.clone();
                self.serve_inclusion(*req_id, &fc)?;
            }

            // Update the ledger (the world knows the event)
            if let Some(ref event) = self.pending_event {
                let mut ledger = self.hub.lock().unwrap().ledger.clone();
                ledger.events.push(lngap_names::registry::Anchored {
                    event: event.clone(),
                    height: fc_h,
                });
                self.hub.lock().unwrap().set_ledger(ledger);
            }
            self.pending_event = None;

            self.say(format!(
                "fact-chain block {} mined (entry {} bytes)",
                fc_h,
                block.entry.len()
            ));
        }

        // 3. Application steps (reveal after commit confirmed)
        self.application_steps()?;

        // 4. Settle off-chain
        self.alice.settle_offchain()?;
        self.bob.settle_offchain()?;

        Ok(btc_h)
    }

    /// Alice sends the reveal once her commit is confirmed on the fact chain.
    fn application_steps(&mut self) -> Result<()> {
        if self.registering && !self.reveal_sent {
            let anchored = self
                .commit_req
                .is_some_and(|id| self.is_confirmed(id));
            if anchored {
                let ev = self.alice_name.reveal_event();
                let p = self.hub_promise(ev, None)?;
                self.open_bond(Who::Alice, ID_RBOND, &p)?;
                self.reveal_sent = true;
                self.say(format!(
                    "alice's commit is confirmed; sent reveal (request {}, h_max {}) and opened bond {ID_RBOND}",
                    p.req_id, p.h_max
                ));
            }
        }
        Ok(())
    }

    pub fn steps(&mut self, n: u32) -> Result<()> {
        for _ in 0..n {
            self.step()?;
        }
        Ok(())
    }

    /// Build and serve the inclusion proof data for a confirmed request.
    /// Converts the fact-chain headers to ClaimData format and stores it
    /// so the NRegFc program's claim_data() can serve it.
    fn serve_inclusion(&mut self, req_id: u32, client: &ChainClient) -> Result<()> {
        let hub = self.hub.lock().unwrap();
        let (shape, data) = hub.inclusion_data(req_id, client)?;
        drop(hub);
        // Convert FactData (headers + entry) to ClaimData (Vec<Vec<u32>>)
        let fc_shape = lngap_factchain::claim::FactChainShape::from_fact_shape(&shape);
        let raw_headers: Vec<[u8; lngap_factchain::HEADER_BYTES]> = data.headers.iter().map(|h| h.0).collect();
        let claim_data = fc_shape.data(&raw_headers);
        self.store.put(&format!("{req_id}/incl"), claim_data);
        self.say(format!("proof data for request {req_id} served ({} headers)", raw_headers.len()));
        Ok(())
    }

    /// N9 fork mode: the real chain advances with an empty block every step;
    /// the hub's entry is mined on a private fork only the hub sees. Once the
    /// real chain is one header longer than the fork, the world serves the
    /// heavier-chain refutation data.
    fn step_fork(&mut self) -> Result<()> {
        // The real chain advances (empty block: no entry)
        self.miner.submit(vec![]);
        let block = self.miner.mine_next().expect("mine");
        self.alice_fc.verify_and_append(&block).map_err(|e| anyhow!(e))?;
        self.bob_fc.verify_and_append(&block).map_err(|e| anyhow!(e))?;

        // The hub's private fork: mine the pending entry there; only the hub sees it
        if let Some(entry) = self.pending_entry.take() {
            let entry_len = entry.len();
            self.fork_miner.submit(entry);
            let fblock = self.fork_miner.mine_next().expect("mine");
            let fh = fblock.header.height();
            self.hub_fc.verify_and_append(&fblock).map_err(|e| anyhow!(e))?;
            self.hub.lock().unwrap().on_block(fh, &fblock.entry);
            self.say(format!(
                "hub mined its entry on a PRIVATE FORK at fact-chain height {fh} ({entry_len} bytes)"
            ));

            let newly: Vec<u32> = {
                let hub = self.hub.lock().unwrap();
                hub.promises
                    .keys()
                    .filter(|id| hub.is_confirmed(**id))
                    .copied()
                    .collect()
            };
            for req_id in newly {
                if self.forked.iter().any(|(id, _, _)| *id == req_id) {
                    continue;
                }
                // The inclusion proof covers the fork (the hub's chain view)
                let fc = self.hub_fc.clone();
                self.serve_inclusion(req_id, &fc)?;
                let (cp_h, conf_h) = {
                    let hub = self.hub.lock().unwrap();
                    let cp = hub.promises.get(&req_id).map(|p| p.checkpoint_height).unwrap_or(0);
                    (cp, hub.confirmed_height(req_id).unwrap_or(cp + 1))
                };
                self.forked.push((req_id, cp_h, (conf_h - cp_h) as usize));
            }
            // The fork entry never lands on the real chain: no ledger update,
            // and the users' confirmed set stays empty.
            self.pending_event = None;
        }

        self.serve_refutations()?;
        Ok(())
    }

    /// Serve the heavier-chain refutation for fork-anchored requests once the
    /// real chain is one header longer than the hub's fork.
    fn serve_refutations(&mut self) -> Result<()> {
        for (req_id, cp_height, n) in self.forked.clone() {
            let key = format!("{req_id}/refute");
            if self.store.has(&key) {
                continue;
            }
            if self.alice_fc.tip_height() < cp_height + n as u32 + 1 {
                continue;
            }
            let p = self
                .promises
                .get(&req_id)
                .ok_or_else(|| anyhow!("no promise {req_id}"))?
                .clone();
            let shape = lngap_factchain::FactShape {
                checkpoint: p.checkpoint,
                difficulty_bits: lngap_factchain::DIFFICULTY_BITS,
                n_headers: n + 1,
            };
            // The real chain, from the users' client. (PoC: the checkpoint is
            // genesis, so build_data's client-relative indexing lines up.)
            let data = shape.build_data(&self.alice_fc, &p.entry);
            let fc_shape = lngap_factchain::claim::FactChainShape::from_fact_shape(&shape);
            let raw_headers: Vec<[u8; lngap_factchain::HEADER_BYTES]> = data.headers.iter().map(|h| h.0).collect();
            self.store.put(&key, fc_shape.data(&raw_headers));
            self.say(format!(
                "the real chain is heavier than the hub's fork: refutation data served for request {req_id} ({} headers)",
                raw_headers.len()
            ));
        }
        Ok(())
    }

    pub fn step_until(
        &mut self,
        max: u32,
        mut pred: impl FnMut(&FcWorld) -> bool,
    ) -> Result<u32> {
        for i in 0..max {
            if pred(self) {
                return Ok(i);
            }
            self.step()?;
        }
        ensure!(pred(self), "condition not met within {max} blocks");
        Ok(max)
    }

    pub fn resolve(&self, name: &str) -> Option<XOnlyPublicKey> {
        self.hub.lock().unwrap().resolve(name)
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
