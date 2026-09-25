//! The fee lock scenarios FL1-FL3 (ATTESTATION_FEES.md; D49, D52): the
//! mover pays the slot's proposer for the attestation of exactly its head,
//! atomically, in a REAL channel.
//!
//! The channel is a `ChannelParty` pair on regtest (the party layer
//! downcasts every contract to a game instance, so the lock is driven at
//! the channel level); beside it the D51 roster venue. The hub is the
//! payee — "the proposer's node" — and the user the payer: the user's
//! entry at slot 1 has a head, the head has a point sum under slot 1's
//! (member 1's) table, and the lock is a channel output paying the hub
//! iff a scalar for that point appears, which is iff member 1 attests
//! exactly that head at exactly that slot.
//!
//! - FL1: cooperative — the venue seals the entry, the hub settles
//!   in-channel with the revealed scalar sum, cooperative close;
//! - FL2: on-chain — the hub force-closes and completes the pre-signed
//!   `claim` with the scalar sum; the user extracts it from the confirmed
//!   witness;
//! - FL3: timeout — the venue seals slot 1 EMPTY: the empty head's
//!   scalars do not complete the pre-signature, and after `expiry` the
//!   user's `timeout` sweep refunds the lock.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, ensure, Result};
use bitcoin::secp256k1::SecretKey;
use bitcoin::{Amount, Txid};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::chain::Chain;
use lngap_channel::commit::OutputKind;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::presign::GraphKey;
use lngap_channel::protocol::{funding_tree, run_bus, ChannelParty, Policy};
use lngap_channel::sweep::{build_sweep, SweepInput};
use lngap_channel::{ChannelParams, ChannelState, FeeLock, PartyKeys, Role};
use lngap_factchain::entry_head;
use lngap_factchain::slot::SlotEntry;
use lngap_pos::fee::{fee_lock, lock_point, lock_secret};
use lngap_pos::{genesis, Member, PosClient, PosMiner, Registry, SealedBlock};

use super::{Report, Scenario};

const FUNDING: Amount = Amount::from_sat(200_000);
const HALF: Amount = Amount::from_sat(100_000);
const CONTRIB: Amount = Amount::from_sat(100_500);
/// The attestation fee the mover offers.
const FEE: Amount = Amount::from_sat(5_000);
const LOCK_ID: u32 = 1;
/// The slot the user's entry is due in (its proposer: member 1).
const SLOT: u32 = 1;
const SEED: [u8; 32] = [0x77; 32];
const K: u8 = 5;
const REGISTRY_SLOTS: u32 = 16;
/// The lock's refund height, relative to the channel's funding height.
const EXPIRY_AFTER: u32 = 20;

fn members() -> Vec<Member> {
    (0..K).map(|i| Member::new([SEED[0] + i; 32])).collect()
}

/// The user's entry for `slot` (the fee lock does not care what it says;
/// its HEAD is what the lock is over).
fn entry_for(slot: u32) -> (Vec<u8>, [u8; 48]) {
    let e = SlotEntry { game_id: 1, depth: slot as u8, mover: 0, mv: 4, state: 0x1234, sigs: vec![[0x11; 20]; 21] }.encode();
    let head = entry_head(&e);
    (e, head)
}

/// A channel between the user (the payer) and the hub (the payee, the
/// proposer's node), and the roster venue beside it.
struct FeeWorld {
    rt: Arc<Regtest>,
    user: ChannelParty,
    hub: ChannelParty,
    miner: PosMiner,
    registry: Registry,
    client: PosClient,
    sealed: HashMap<u32, SealedBlock>,
    /// The scalars the payee handed the user, by lock id (the out-of-band
    /// delivery the payer's settlement policy reads).
    delivered: Arc<Mutex<HashMap<u32, SecretKey>>>,
    /// What the hub expects each lock to be over (the entry the mover
    /// handed the proposer's node), by lock id: (slot, head).
    expected: Arc<Mutex<HashMap<u32, (u32, [u8; 48])>>>,
    funding_height: u32,
    /// (height, role, txid, broadcaster, vsize) of each channel broadcast.
    seen: Vec<(u32, String, Txid, Role, usize)>,
    log: Vec<String>,
}

impl FeeWorld {
    fn open() -> Result<FeeWorld> {
        let rt = Arc::new(Regtest::start()?);
        let members = members();
        let (gen, _t0) = genesis(&members[0].attester);
        let gen_digest = gen.header.digest();
        let mut miner = PosMiner::new(members, gen_digest, 0);
        let registry = miner.registry(REGISTRY_SLOTS)?;
        let client = PosClient::from_checkpoint(0, gen_digest);

        let params = ChannelParams::regtest(FUNDING);
        let user_keys = PartyKeys::from_seed(Role::User, Seed::from_label("fl/user"));
        let hub_keys = PartyKeys::from_seed(Role::Hub, Seed::from_label("fl/hub"));
        let pubs = [user_keys.public(), hub_keys.public()];
        let (u_op, u_prev) = rt.fund(&pubs[0].payout_spk, CONTRIB)?;
        let (h_op, h_prev) = rt.fund(&pubs[1].payout_spk, CONTRIB)?;
        let ftree = funding_tree(&pubs);
        let mut ftx = build_funding_tx(&[(u_op, u_prev.clone()), (h_op, h_prev.clone())], ftree.script_pubkey(), FUNDING);
        let funding = (bitcoin::OutPoint { txid: ftx.compute_txid(), vout: 0 }, ftx.output[0].clone());
        let initial = ChannelState { seq: 0, balances: [HALF, HALF], contracts: vec![] };

        let delivered: Arc<Mutex<HashMap<u32, SecretKey>>> = Arc::default();
        let expected: Arc<Mutex<HashMap<u32, (u32, [u8; 48])>>> = Arc::default();
        // the payer accepts a lock's removal only as a settlement it has
        // been handed the secret for, or as its own refund
        let d = delivered.clone();
        let payer_policy: Policy = Box::new(move |old: &ChannelState, new: &ChannelState| {
            for c in &old.contracts {
                if new.contract(c.id()).is_none() {
                    let lock = FeeLock::find(old, c.id()).ok_or_else(|| anyhow!("not a fee lock"))?;
                    if new.balances[lock.payee().idx()] > old.balances[lock.payee().idx()] {
                        let d = d.lock().unwrap();
                        FeeLock::accept_settlement(old, new, c.id(), d.get(&c.id()))?;
                    } else {
                        ensure!(new.balances == lock.refunded(old).balances, "a refund must return exactly the lock");
                    }
                }
            }
            Ok(())
        });
        // the payee accepts a lock only over the head it was handed for
        // that slot, under the SCHEDULED member's table
        let e = expected.clone();
        let reg = registry.clone();
        let payee_policy: Policy = Box::new(move |old: &ChannelState, new: &ChannelState| {
            for c in &new.contracts {
                if old.contract(c.id()).is_none() {
                    let lock = FeeLock::find(new, c.id()).ok_or_else(|| anyhow!("not a fee lock"))?;
                    let (slot, head) = *e.lock().unwrap().get(&c.id()).ok_or_else(|| anyhow!("no entry was handed in for lock {}", c.id()))?;
                    ensure!(lock.payer == Role::User && lock.value == FEE, "unexpected lock terms");
                    ensure!(lock.lock == lock_point(reg.table(slot), &head), "the lock is not over the handed-in head under slot {slot}'s table");
                }
            }
            Ok(())
        });
        let user_rev = [user_keys.revocation_hash(0), user_keys.revocation_hash(1)];
        let hub_rev = [hub_keys.revocation_hash(0), hub_keys.revocation_hash(1)];
        let chain: Arc<dyn Chain> = rt.clone();
        let mut user = ChannelParty::new(user_keys, pubs[1].clone(), params, funding.clone(), initial.clone(), hub_rev, chain.clone(), payer_policy)?;
        let mut hub = ChannelParty::new(hub_keys, pubs[0].clone(), params, funding, initial, user_rev, chain, payee_policy)?;
        let m1 = user.initial_commit_sigs()?;
        let m2 = hub.initial_commit_sigs()?;
        run_bus(&mut user, &mut hub, vec![m1, m2])?;
        ensure!(user.ready_to_fund() && hub.ready_to_fund());
        let prevouts = [u_prev, h_prev];
        sign_funding_input(&mut ftx, 0, &prevouts, &user.keys.payout_tree(), &user.keys.payout)?;
        sign_funding_input(&mut ftx, 1, &prevouts, &hub.keys.payout_tree(), &hub.keys.payout)?;
        let (_txid, funding_height) = rt.send_and_confirm(&ftx)?;
        let mut w = FeeWorld { rt, user, hub, miner, registry, client, sealed: HashMap::new(), delivered, expected, funding_height, seen: Vec::new(), log: Vec::new() };
        w.say(format!("channel funded: 100,000 / 100,000 sat; the venue: {K} members in round robin, slot {SLOT}'s proposer is member {}", w.registry.proposer(SLOT)));
        Ok(w)
    }

    fn say(&mut self, s: String) {
        let h = self.rt.height().unwrap();
        self.log.push(format!("[fee @ {h} / seq {}] {s}", self.user.current_seq()));
    }

    fn height(&self) -> u32 {
        self.rt.height().unwrap()
    }

    fn expiry(&self) -> u32 {
        self.funding_height + EXPIRY_AFTER
    }

    fn lock(&self) -> FeeLock {
        FeeLock::find(self.user.current_state(), LOCK_ID).cloned().expect("the lock is live")
    }

    /// Mine `n` blocks one at a time, both parties reacting; record every
    /// channel broadcast that confirms.
    fn advance(&mut self, n: u32) -> Result<()> {
        for _ in 0..n {
            self.rt.mine(1)?;
            let h = self.height();
            let txs = self.rt.block_txs(h)?;
            for tx in txs.iter().skip(1) {
                let txid = tx.compute_txid();
                let hit = self.user.broadcasts.iter().map(|b| (b, Role::User)).chain(self.hub.broadcasts.iter().map(|b| (b, Role::Hub))).find(|(b, _)| b.txid == txid);
                if let Some((b, by)) = hit {
                    self.seen.push((h, b.role.clone(), txid, by, tx.vsize()));
                    self.log.push(format!("[fee @ {h} / seq {}] {by} broadcast `{}` ({} vB) — confirmed", self.user.current_seq(), b.role, tx.vsize()));
                }
            }
            self.user.on_block(h, &txs)?;
            self.hub.on_block(h, &txs)?;
        }
        Ok(())
    }

    fn advance_to(&mut self, h: u32) -> Result<()> {
        while self.height() < h {
            self.advance(1)?;
        }
        Ok(())
    }

    /// The user hands its entry for `SLOT` to the proposer's node and
    /// offers the fee lock over its head: a channel update.
    fn offer_lock(&mut self) -> Result<[u8; 48]> {
        let (_e, head) = entry_for(SLOT);
        self.expected.lock().unwrap().insert(LOCK_ID, (SLOT, head));
        let lock = fee_lock(LOCK_ID, Role::User, FEE, &self.registry, SLOT, &head, self.expiry());
        let memo = lock.memo.clone();
        let st = lock.offered(self.user.current_state())?;
        let msgs = self.user.propose(st)?;
        run_bus(&mut self.user, &mut self.hub, msgs)?;
        ensure!(self.user.current_seq() == self.hub.current_seq() && self.user.pending_seq().is_none());
        self.say(format!("user offers a fee lock of {} sat to the hub: {memo}; both hold the pre-signed claim (the user's half an adaptor pre-signature)", FEE.to_sat()));
        Ok(head)
    }

    /// One Bitcoin block, one venue slot: the scheduled member seals the
    /// user's entry (or an empty block).
    fn seal(&mut self, with_entry: bool) -> Result<()> {
        self.advance(1)?;
        let slot = self.sealed.len() as u32 + 1;
        if with_entry {
            let (e, _) = entry_for(slot);
            self.miner.submit(e);
        }
        let (block, _t) = self.miner.seal_next(slot).map_err(|e| anyhow!(e))?;
        self.client.verify_and_append(&block, &self.registry).map_err(|e| anyhow!(e))?;
        let p = self.miner.proposer_at(slot);
        self.say(if with_entry {
            format!("slot {slot} sealed by member {p} with the user's entry; attested — the head's scalars are now public")
        } else {
            format!("slot {slot} sealed EMPTY by member {p}: the user's entry was not attested")
        });
        self.sealed.insert(slot, block);
        Ok(())
    }

    /// The hub settles the lock in-channel: it sums the sealed block's
    /// head scalars, hands the secret to the user, and proposes the
    /// settled state.
    fn settle_in_channel(&mut self) -> Result<()> {
        let lock = self.lock();
        let t = lock_secret(&self.sealed[&SLOT]);
        ensure!(lock.opens(&t), "the attestation's scalar sum opens the lock");
        self.delivered.lock().unwrap().insert(LOCK_ID, t);
        let st = lock.settled(self.hub.current_state());
        let msgs = self.hub.propose(st)?;
        run_bus(&mut self.hub, &mut self.user, msgs)?;
        ensure!(self.user.current_seq() == self.hub.current_seq() && FeeLock::find(self.user.current_state(), LOCK_ID).is_none());
        self.say(format!("hub settles the lock in-channel: the scalar sum opens it, the user is handed the secret and accepts; balances {} / {}", self.user.current_state().balances[0].to_sat(), self.user.current_state().balances[1].to_sat()));
        Ok(())
    }

    fn coop_close(&mut self) -> Result<()> {
        let msgs = self.user.propose_close()?;
        run_bus(&mut self.user, &mut self.hub, msgs)?;
        self.advance(1)?;
        self.say("cooperative close".to_string());
        Ok(())
    }

    /// The hub force-closes, waits out its delay, completes the pre-signed
    /// claim with the sealed block's scalar sum and broadcasts it; the user
    /// extracts the secret from the confirmed witness.
    fn claim_on_chain(&mut self) -> Result<()> {
        let lock = self.lock();
        let t = lock_secret(&self.sealed[&SLOT]);
        let seq = self.hub.current_seq();
        self.hub.force_close()?;
        self.say("hub force-closes with the lock live".to_string());
        self.advance(1)?;
        // the claim leaf on the hub's own commitment carries its delay
        let delay = u32::from(self.hub.params.to_self_delay);
        self.advance(delay)?;
        let key = GraphKey { version: Role::Hub, contract_id: LOCK_ID, label: "claim".into() };
        let pubs = self.hub.pubkeys.clone();
        let tx = {
            let rec = self.hub.record_mut(seq).ok_or_else(|| anyhow!("no record"))?;
            let ptx = rec.graph.get_mut(&key).ok_or_else(|| anyhow!("no claim skeleton"))?;
            ensure!(ptx.finalize(&[]).is_err(), "before completion the claim is not broadcastable");
            ptx.complete(&t, &pubs)?;
            ptx.finalize(&[])?
        };
        self.hub.broadcast(&tx, "fee_claim")?;
        self.say(format!("hub completes the pre-signed claim with the scalar sum and broadcasts it ({} vB)", tx.vsize()));
        self.advance(1)?;
        // the payer learns the secret from the chain
        let h = self.height();
        let confirmed = self.rt.block_txs(h)?.into_iter().find(|x| x.compute_txid() == tx.compute_txid()).ok_or_else(|| anyhow!("the claim did not confirm"))?;
        let extracted = self.user.record(seq).ok_or_else(|| anyhow!("no record"))?.graph[&key].extract_secret(&confirmed)?;
        ensure!(lock.opens(&extracted) && extracted == t, "the user extracts the attestation's scalar sum from the confirmed claim");
        self.say("user extracts the secret from the confirmed claim's witness: it is the attestation's scalar sum".to_string());
        Ok(())
    }

    /// FL3's negative: the empty block's scalars do not complete the
    /// pre-signature.
    fn claim_fails(&mut self) -> Result<()> {
        let seq = self.hub.current_seq();
        let key = GraphKey { version: Role::Hub, contract_id: LOCK_ID, label: "claim".into() };
        let pubs = self.hub.pubkeys.clone();
        let wrong = lock_secret(&self.sealed[&SLOT]);
        let rec = self.hub.record_mut(seq).ok_or_else(|| anyhow!("no record"))?;
        let ptx = rec.graph.get_mut(&key).ok_or_else(|| anyhow!("no claim skeleton"))?;
        ensure!(ptx.complete(&wrong, &pubs).is_err(), "the empty head's scalars must not complete the pre-signature");
        ensure!(ptx.finalize(&[]).is_err(), "the claim stays unbroadcastable");
        self.say("hub tries to complete the claim with the empty block's scalar sum: it does not open the lock; the claim stays unsigned".to_string());
        Ok(())
    }

    /// After `expiry`, the user force-closes and sweeps the lock through
    /// `timeout`.
    fn timeout_on_chain(&mut self) -> Result<()> {
        let lock = self.lock();
        self.advance_to(lock.expiry)?;
        let seq = self.user.current_seq();
        self.user.force_close()?;
        self.say("user force-closes after the lock's expiry".to_string());
        self.advance(1)?;
        let delay = u32::from(self.user.params.to_self_delay);
        self.advance(delay)?;
        let c = self.user.my_commitment(seq).ok_or_else(|| anyhow!("no commitment"))?.clone();
        let o = c.output(OutputKind::Contract(LOCK_ID)).ok_or_else(|| anyhow!("no lock output"))?;
        let input = SweepInput { outpoint: c.outpoint(o), prevout: c.txout(o), tree: &o.tree, leaf: "timeout", before_sig: vec![] };
        let tx = build_sweep(&[input], self.user.my_payout_spk(), self.user.params.presign_fee, &self.user.keys.payment, bitcoin::absolute::LockTime::from_height(lock.expiry)?)?;
        self.user.broadcast(&tx, "fee_timeout")?;
        self.say(format!("user sweeps the lock through `timeout` ({} vB)", tx.vsize()));
        self.advance(1)?;
        Ok(())
    }

    fn balances(&self) -> [Amount; 2] {
        [self.rt.balance_of(&self.user.my_payout_spk()).unwrap(), self.rt.balance_of(&self.hub.my_payout_spk()).unwrap()]
    }
}

fn report(w: &FeeWorld, sc: &Scenario) -> Report {
    println!(
        "=== {}: {:?} ({} vB in {} txs)",
        sc.id,
        w.seen.iter().map(|s| s.1.clone()).collect::<Vec<_>>(),
        w.seen.iter().map(|s| s.4).sum::<usize>(),
        w.seen.len()
    );
    Report {
        id: sc.id.into(),
        title: sc.title.into(),
        expected: sc.expected.into(),
        txs: w.seen.iter().map(|s| (s.0, s.1.clone(), s.2.to_string(), s.3.name().to_string())).collect(),
        balances: w.balances(),
        narrative: w.log.join("\n"),
    }
}

fn roles(w: &FeeWorld) -> Vec<String> {
    w.seen.iter().map(|s| s.1.clone()).collect()
}

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

pub const FL1: Scenario = Scenario {
    id: "FL1",
    title: "fee lock: the proposer is paid in-channel for attesting exactly the mover's head",
    expected: "the user locks 5,000 sat to the point sum of its head under slot 1's (member 1's) table; member 1 seals the entry; the hub sums the revealed scalars, hands the secret to the user and settles in-channel; cooperative close — nothing on Bitcoin but the close: user 94,500, hub 104,500",
    run: || {
        let mut w = FeeWorld::open()?;
        w.offer_lock()?;
        w.seal(true)?;
        w.settle_in_channel()?;
        ensure!(w.user.current_state().balances == [sat(95_000), sat(105_000)]);
        w.coop_close()?;
        ensure!(roles(&w) == vec!["coop_close".to_string()], "{:?}", roles(&w));
        ensure!(w.balances() == [sat(94_500), sat(104_500)], "{:?}", w.balances());
        Ok(report(&w, &FL1))
    },
};

pub const FL2: Scenario = Scenario {
    id: "FL2",
    title: "fee lock: the on-chain claim completes the payer's pre-signature with the attestation's scalars",
    expected: "the lock is live; member 1 seals the entry; the hub force-closes, waits out its delay, completes the pre-signed claim with the scalar sum and broadcasts it; the user extracts the secret from the confirmed witness (D49): commitment, the user's to_remote claim, the hub's to_local claim and the fee claim",
    run: || {
        let mut w = FeeWorld::open()?;
        w.offer_lock()?;
        w.seal(true)?;
        w.claim_on_chain()?;
        let r = roles(&w);
        ensure!(r.len() == 4 && r[0] == "commitment_1" && r.contains(&"claim_to_remote".to_string()) && r.contains(&"claim_to_local".to_string()) && r.contains(&"fee_claim".to_string()), "{r:?}");
        // user: to_remote 95,000 - 1,000; hub: to_local 99,000 - 1,000 + the claim 5,000 - 1,000
        ensure!(w.balances() == [sat(94_000), sat(102_000)], "{:?}", w.balances());
        Ok(report(&w, &FL2))
    },
};

pub const FL3: Scenario = Scenario {
    id: "FL3",
    title: "fee lock: no attestation of the head — the claim cannot be completed and the payer's timeout refunds it",
    expected: "the lock is live; member 1 seals slot 1 EMPTY (the entry dropped): the empty head's scalar sum does not complete the pre-signature; after expiry the user force-closes and sweeps the lock through `timeout`: commitment, the hub's to_remote claim, the user's to_local claim and the timeout sweep",
    run: || {
        let mut w = FeeWorld::open()?;
        w.offer_lock()?;
        w.seal(false)?;
        w.claim_fails()?;
        w.timeout_on_chain()?;
        let r = roles(&w);
        ensure!(r.len() == 4 && r[0] == "commitment_1" && r.contains(&"claim_to_remote".to_string()) && r.contains(&"claim_to_local".to_string()) && r.contains(&"fee_timeout".to_string()), "{r:?}");
        // user: to_local 94,000 - 1,000 + the refund 5,000 - 1,000; hub: to_remote 100,000 - 1,000
        ensure!(w.balances() == [sat(97_000), sat(99_000)], "{:?}", w.balances());
        Ok(report(&w, &FL3))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![FL1, FL2, FL3]
}
