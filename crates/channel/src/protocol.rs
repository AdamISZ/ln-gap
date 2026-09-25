//! The per-party channel state machine: update protocol (Lightning's
//! ordering), revocation, force-close, cooperative close, penalty, and the
//! block-by-block watch loop for channel-level events.

use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use anyhow::{anyhow, bail, ensure, Context, Result};
use bitcoin::script::Builder;
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::{Amount, OutPoint, Sequence, Transaction, TxOut, Txid};
use lngap_btc::hash160;
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::{sign_tapscript, verify_tapscript};
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_tx, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_btc::Hash160;
use tracing::{info, warn};

use crate::chain::{Broadcast, Chain};
use crate::commit::{build_commitment, CommitCtx, Commitment, OutputKind};
use crate::presign::{GraphKey, GraphSig, PresignedTx};
use crate::sweep::{build_sweep, SweepInput};
use crate::{ChannelParams, ChannelState, PartyKeys, PartyPubKeys, Role};

/// Protocol messages. All carried over an in-memory bus in the PoC.
#[derive(Clone, Debug)]
pub enum Msg {
    /// Proposer -> responder: the new state. Always followed by `CommitSigs`.
    Propose { state: ChannelState },
    /// Signatures on the receiver's commitment for `seq` and on every
    /// pre-signed graph transaction of both versions.
    CommitSigs { seq: u64, commit_sig: Signature, graph_sigs: Vec<(GraphKey, GraphSig)> },
    /// Revocation of `seq`, plus the sender's revocation hash for `seq + 2`.
    RevokeAndAck { seq: u64, secret: [u8; 32], next_rev_hash: Hash160 },
    /// Cooperative close: proposer's signature on the close tx built with `fee`.
    CloseRequest { fee: Amount, sig: Signature },
    CloseSig { sig: Signature },
}

#[derive(Clone, Debug)]
pub struct Envelope {
    pub from: Role,
    pub to: Role,
    pub msg: Msg,
}

/// Everything a party holds about one channel state.
#[derive(Debug)]
pub struct StateRecord {
    pub state: ChannelState,
    /// Both commitment versions, indexed by broadcaster.
    pub commits: [Commitment; 2],
    /// The counterparty's signature on *my* version.
    pub remote_commit_sig: Option<Signature>,
    /// Pre-signed graphs off both versions' contract outputs.
    pub graph: BTreeMap<GraphKey, PresignedTx>,
    /// I hold everything needed to enforce this state unilaterally.
    pub signed_by_remote: bool,
    pub revoked_by_me: bool,
    /// The counterparty's revocation secret: they can no longer broadcast this.
    pub remote_secret: Option<[u8; 32]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Closing {
    /// I broadcast my commitment for `seq`.
    Local { seq: u64, confirmed_at: Option<u32> },
    /// The counterparty's commitment for `seq` confirmed.
    Remote { seq: u64, confirmed_at: u32, revoked: bool },
    Cooperative { txid: Txid },
}

/// Chain events the contract layer cares about, produced by `on_block`.
#[derive(Clone, Debug)]
pub enum ChainEvent {
    LocalCommitConfirmed { seq: u64, height: u32 },
    RemoteCommitConfirmed { seq: u64, height: u32 },
    RemoteRevokedCommitConfirmed { seq: u64, height: u32 },
    /// A watched outpoint was spent by `tx` in the block at `height`.
    OutputSpent { outpoint: OutPoint, tx: Transaction, height: u32 },
}

/// Scripted misbehaviour for scenarios. The honest code path never sets these.
#[derive(Clone, Copy, Debug, Default)]
pub struct Faults {
    /// Ignore every incoming message (a hub that "stops signing").
    pub stop_responding: bool,
}

pub type Policy = Box<dyn Fn(&ChannelState, &ChannelState) -> Result<()> + Send + Sync>;

pub struct ChannelParty {
    pub me: Role,
    pub keys: PartyKeys,
    pub pubkeys: [PartyPubKeys; 2],
    pub params: ChannelParams,
    pub funding: (OutPoint, TxOut),
    pub funding_tree: TapTree,
    states: BTreeMap<u64, StateRecord>,
    current: u64,
    pending: Option<(u64, bool)>,
    remote_rev_hashes: BTreeMap<u64, Hash160>,
    policy: Policy,
    chain: Arc<dyn Chain>,
    pub closing: Option<Closing>,
    swept: HashSet<OutPoint>,
    /// Every outpoint seen spent in a confirmed block.
    spent_on_chain: HashSet<OutPoint>,
    watched: HashSet<OutPoint>,
    pub broadcasts: Vec<Broadcast>,
    pub faults: Faults,
    close_pending: Option<(Transaction, Amount)>,
    /// Sweep fee for single-signer transactions.
    sweep_fee: Amount,
}

/// The funding output: a single 2-of-2 leaf over both funding keys.
pub fn funding_tree(keys: &[PartyPubKeys; 2]) -> TapTree {
    TapTree::new(vec![Leaf::new(
        "funding",
        Builder::new().two_of_two(&keys[0].funding, &keys[1].funding).into_script(),
        Timelock::NONE,
    )])
    .expect("one leaf")
}

impl ChannelParty {
    /// Construct a party for a channel whose funding outpoint is known
    /// (the funding tx is built but not yet broadcast). `remote_rev_hashes`
    /// are the counterparty's revocation hashes for states 0 and 1.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        keys: PartyKeys,
        remote_pub: PartyPubKeys,
        params: ChannelParams,
        funding: (OutPoint, TxOut),
        initial: ChannelState,
        remote_rev_hashes: [Hash160; 2],
        chain: Arc<dyn Chain>,
        policy: Policy,
    ) -> Result<ChannelParty> {
        ensure!(initial.seq == 0, "initial state must be seq 0");
        let me = keys.role;
        let mut pubkeys = [keys.public(), keys.public()];
        pubkeys[me.other().idx()] = remote_pub;
        let funding_tree = funding_tree(&pubkeys);
        ensure!(funding.1.script_pubkey == funding_tree.script_pubkey(), "funding output does not match keys");
        ensure!(funding.1.value == params.funding_amount, "funding value mismatch");
        let mut p = ChannelParty {
            me,
            keys,
            pubkeys,
            params,
            funding,
            funding_tree,
            states: BTreeMap::new(),
            current: 0,
            pending: None,
            remote_rev_hashes: [(0, remote_rev_hashes[0]), (1, remote_rev_hashes[1])].into_iter().collect(),
            policy,
            chain,
            closing: None,
            swept: HashSet::new(),
            spent_on_chain: HashSet::new(),
            watched: HashSet::new(),
            broadcasts: Vec::new(),
            faults: Faults::default(),
            close_pending: None,
            sweep_fee: params.presign_fee,
        };
        let rec = p.build_record(initial)?;
        p.states.insert(0, rec);
        Ok(p)
    }

    // ----- accessors -----

    pub fn current_seq(&self) -> u64 {
        self.current
    }
    pub fn current_state(&self) -> &ChannelState {
        &self.states[&self.current].state
    }
    pub fn record(&self, seq: u64) -> Option<&StateRecord> {
        self.states.get(&seq)
    }
    pub fn record_mut(&mut self, seq: u64) -> Option<&mut StateRecord> {
        self.states.get_mut(&seq)
    }
    pub fn pending_seq(&self) -> Option<u64> {
        self.pending.map(|(s, _)| s)
    }
    pub fn my_commitment(&self, seq: u64) -> Option<&Commitment> {
        self.states.get(&seq).map(|r| &r.commits[self.me.idx()])
    }
    pub fn remote_commitment(&self, seq: u64) -> Option<&Commitment> {
        self.states.get(&seq).map(|r| &r.commits[self.me.other().idx()])
    }
    pub fn commit_ctx<'a>(&'a self, seq: u64, broadcaster: Role) -> Result<CommitCtx<'a>> {
        let rev_hash = if broadcaster == self.me {
            self.keys.revocation_hash(seq)
        } else {
            *self.remote_rev_hashes.get(&seq).ok_or_else(|| anyhow!("no remote revocation hash for {seq}"))?
        };
        Ok(CommitCtx { params: &self.params, keys: &self.pubkeys, broadcaster, seq, rev_hash })
    }
    pub fn my_payout_spk(&self) -> bitcoin::ScriptBuf {
        self.pubkeys[self.me.idx()].payout_spk.clone()
    }
    pub fn chain(&self) -> &Arc<dyn Chain> {
        &self.chain
    }
    /// Ask the watch loop to report spends of `op`.
    pub fn watch(&mut self, op: OutPoint) {
        self.watched.insert(op);
    }
    /// Has this outpoint already been swept by me, or spent on-chain by anyone?
    pub fn is_swept(&self, op: &OutPoint) -> bool {
        self.swept.contains(op) || self.spent_on_chain.contains(op)
    }
    pub fn is_spent_on_chain(&self, op: &OutPoint) -> bool {
        self.spent_on_chain.contains(op)
    }
    pub fn mark_swept(&mut self, op: OutPoint) {
        self.swept.insert(op);
    }

    /// Broadcast a transaction and log it under `role`.
    pub fn broadcast(&mut self, tx: &Transaction, role: &str) -> Result<Txid> {
        let txid = match self.chain.broadcast(tx) {
            Ok(t) => t,
            // Both parties may legitimately race to broadcast the same
            // pre-signed transaction (Settle, Split); the second is a no-op.
            Err(e) if format!("{e:#}").contains("already") => {
                info!(party = %self.me, %role, "already broadcast by the counterparty");
                tx.compute_txid()
            }
            Err(e) => return Err(e).with_context(|| format!("{} broadcasting {role}", self.me)),
        };
        info!(party = %self.me, %role, %txid, "broadcast");
        self.broadcasts.push(Broadcast { txid, role: role.to_string(), by: self.me });
        Ok(txid)
    }

    // ----- building states -----

    fn build_record(&self, state: ChannelState) -> Result<StateRecord> {
        state.check_invariant(self.params.funding_amount)?;
        let seq = state.seq;
        let mut commits = Vec::new();
        let mut graph = BTreeMap::new();
        let (mut t_build, mut t_sign) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
        for r in Role::BOTH {
            let ctx = self.commit_ctx(seq, r)?;
            let c = build_commitment(&state, &ctx, self.funding.clone())?;
            for o in &c.outputs {
                if let OutputKind::Contract(id) = o.kind {
                    let contract = state.contract(id).expect("contract exists");
                    let t0 = std::time::Instant::now();
                    let txs = contract.graph(&ctx, c.outpoint(o), &c.txout(o))?;
                    t_build += t0.elapsed();
                    let t0 = std::time::Instant::now();
                    for mut ptx in txs {
                        ptx.sign_as(self.me, &self.keys.payment)?;
                        let key = GraphKey { version: r, contract_id: id, label: ptx.label.clone() };
                        ensure!(!graph.contains_key(&key), "duplicate graph label {key}");
                        graph.insert(key, ptx);
                    }
                    t_sign += t0.elapsed();
                }
            }
            commits.push(c);
        }
        if !graph.is_empty() {
            info!(party = %self.me, seq, txs = graph.len(), build_ms = t_build.as_millis(), sign_ms = t_sign.as_millis(), "built and signed the pre-signed graphs of both versions");
        }
        let commits: [Commitment; 2] = commits.try_into().expect("two versions");
        Ok(StateRecord {
            state,
            commits,
            remote_commit_sig: None,
            graph,
            signed_by_remote: false,
            revoked_by_me: false,
            remote_secret: None,
        })
    }

    /// My signatures for the counterparty: on their commitment and every graph tx.
    fn commit_sigs_for(&self, seq: u64) -> Result<Msg> {
        let rec = self.states.get(&seq).ok_or_else(|| anyhow!("no record {seq}"))?;
        let their = &rec.commits[self.me.other().idx()];
        let leaf = self.funding_tree.leaf("funding")?;
        let commit_sig = sign_tapscript(&self.keys.funding, &their.tx, 0, std::slice::from_ref(&self.funding.1), &leaf.script)?;
        let graph_sigs = rec
            .graph
            .iter()
            .map(|(k, p)| (k.clone(), p.my_sig(self.me).expect("signed at build")))
            .collect();
        Ok(Msg::CommitSigs { seq, commit_sig, graph_sigs })
    }

    fn accept_commit_sigs(&mut self, seq: u64, commit_sig: Signature, graph_sigs: Vec<(GraphKey, GraphSig)>) -> Result<()> {
        let t0 = std::time::Instant::now();
        let n = graph_sigs.len();
        let r = self.accept_commit_sigs_inner(seq, commit_sig, graph_sigs);
        if n > 0 {
            info!(party = %self.me, seq, sigs = n, verify_ms = t0.elapsed().as_millis(), "verified the counterparty's graph signatures");
        }
        r
    }
    fn accept_commit_sigs_inner(&mut self, seq: u64, commit_sig: Signature, graph_sigs: Vec<(GraphKey, GraphSig)>) -> Result<()> {
        let them = self.me.other();
        let leaf = self.funding_tree.leaf("funding")?.clone();
        let funding_prevout = self.funding.1.clone();
        let their_funding_key = self.pubkeys[them.idx()].funding;
        let pubkeys = self.pubkeys.clone();
        let rec = self.states.get_mut(&seq).ok_or_else(|| anyhow!("CommitSigs for unknown state {seq}"))?;
        let mine = &rec.commits[self.me.idx()];
        verify_tapscript(&their_funding_key, &commit_sig, &mine.tx, 0, std::slice::from_ref(&funding_prevout), &leaf.script)
            .map_err(|e| anyhow!("commitment signature for state {seq} invalid: {e}"))?;
        rec.remote_commit_sig = Some(commit_sig);
        for (k, sig) in graph_sigs {
            let p = rec.graph.get_mut(&k).ok_or_else(|| anyhow!("signature for unknown graph tx {k}"))?;
            p.add_sig(them, sig, &pubkeys)?;
        }
        for (k, p) in &rec.graph {
            ensure!(p.fully_signed(), "graph tx {k} not fully signed after CommitSigs");
        }
        rec.signed_by_remote = true;
        Ok(())
    }

    fn revoke(&mut self, seq: u64) -> Result<Msg> {
        let rec = self.states.get_mut(&seq).ok_or_else(|| anyhow!("revoke unknown {seq}"))?;
        rec.revoked_by_me = true;
        Ok(Msg::RevokeAndAck {
            seq,
            secret: self.keys.revocation_secret(seq),
            next_rev_hash: self.keys.revocation_hash(seq + 2),
        })
    }

    fn env(&self, msg: Msg) -> Envelope {
        Envelope { from: self.me, to: self.me.other(), msg }
    }

    // ----- the protocol -----

    /// Opening: my signatures for state 0. Exchange before broadcasting funding.
    pub fn initial_commit_sigs(&self) -> Result<Envelope> {
        Ok(self.env(self.commit_sigs_for(0)?))
    }

    /// State 0 is enforceable: safe to broadcast the funding transaction.
    pub fn ready_to_fund(&self) -> bool {
        self.states.get(&0).map(|r| r.signed_by_remote).unwrap_or(false)
    }

    /// Propose `new_state` (seq = current + 1). Returns `Propose` + `CommitSigs`.
    pub fn propose(&mut self, new_state: ChannelState) -> Result<Vec<Envelope>> {
        ensure!(self.closing.is_none(), "channel is closing");
        ensure!(self.pending.is_none(), "an update is already pending");
        ensure!(new_state.seq == self.current + 1, "propose seq {} but current is {}", new_state.seq, self.current);
        ensure!(self.remote_rev_hashes.contains_key(&new_state.seq), "missing counterparty revocation hash");
        (self.policy)(self.current_state(), &new_state)?;
        let rec = self.build_record(new_state.clone())?;
        self.states.insert(new_state.seq, rec);
        self.pending = Some((new_state.seq, true));
        let sigs = self.commit_sigs_for(new_state.seq)?;
        Ok(vec![self.env(Msg::Propose { state: new_state }), self.env(sigs)])
    }

    /// Handle one message; returns replies. A party with `stop_responding`
    /// set drops everything.
    pub fn handle(&mut self, env: Envelope) -> Result<Vec<Envelope>> {
        ensure!(env.to == self.me, "misrouted message");
        if self.faults.stop_responding {
            warn!(party = %self.me, "faulty: ignoring {}", msg_name(&env.msg));
            return Ok(vec![]);
        }
        match env.msg {
            Msg::Propose { state } => {
                ensure!(self.closing.is_none(), "channel is closing");
                ensure!(self.pending.is_none(), "update already pending");
                ensure!(state.seq == self.current + 1, "proposed seq {} but current is {}", state.seq, self.current);
                (self.policy)(self.current_state(), &state).context("update rejected by policy")?;
                let rec = self.build_record(state.clone())?;
                self.states.insert(state.seq, rec);
                self.pending = Some((state.seq, false));
                Ok(vec![])
            }
            Msg::CommitSigs { seq, commit_sig, graph_sigs } => {
                if seq == 0 {
                    self.accept_commit_sigs(0, commit_sig, graph_sigs)?;
                    return Ok(vec![]);
                }
                let (pseq, mine) = self.pending.ok_or_else(|| anyhow!("CommitSigs with no pending update"))?;
                ensure!(pseq == seq, "CommitSigs for {seq} but pending is {pseq}");
                self.accept_commit_sigs(seq, commit_sig, graph_sigs)?;
                let prev = seq - 1;
                let revoke = self.revoke(prev)?;
                self.current = seq;
                if mine {
                    // proposer: responder already revoked; I revoke and we're done
                    self.pending = None;
                    Ok(vec![self.env(revoke)])
                } else {
                    // responder: revoke old state, then sign the proposer's new state
                    let sigs = self.commit_sigs_for(seq)?;
                    Ok(vec![self.env(revoke), self.env(sigs)])
                }
            }
            Msg::RevokeAndAck { seq, secret, next_rev_hash } => {
                let expected = self.remote_rev_hashes.get(&seq).ok_or_else(|| anyhow!("revocation for unknown {seq}"))?;
                ensure!(hash160(&secret) == *expected, "revocation secret for {seq} does not match its hash");
                let rec = self.states.get_mut(&seq).ok_or_else(|| anyhow!("revocation for unknown state {seq}"))?;
                rec.remote_secret = Some(secret);
                self.remote_rev_hashes.insert(seq + 2, next_rev_hash);
                if let Some((pseq, false)) = self.pending {
                    if pseq == seq + 1 {
                        self.pending = None;
                    }
                }
                Ok(vec![])
            }
            Msg::CloseRequest { fee, sig } => {
                ensure!(self.pending.is_none(), "cannot close with a pending update");
                let tx = self.close_tx(fee)?;
                let leaf = self.funding_tree.leaf("funding")?;
                verify_tapscript(&self.pubkeys[self.me.other().idx()].funding, &sig, &tx, 0, std::slice::from_ref(&self.funding.1), &leaf.script)?;
                let mine = sign_tapscript(&self.keys.funding, &tx, 0, std::slice::from_ref(&self.funding.1), &leaf.script)?;
                self.closing = Some(Closing::Cooperative { txid: tx.compute_txid() });
                Ok(vec![self.env(Msg::CloseSig { sig: mine })])
            }
            Msg::CloseSig { sig } => {
                let (mut tx, _fee) = self.close_pending.take().ok_or_else(|| anyhow!("CloseSig without a pending close"))?;
                let leaf = self.funding_tree.leaf("funding")?;
                verify_tapscript(&self.pubkeys[self.me.other().idx()].funding, &sig, &tx, 0, std::slice::from_ref(&self.funding.1), &leaf.script)?;
                let mine = sign_tapscript(&self.keys.funding, &tx, 0, std::slice::from_ref(&self.funding.1), &leaf.script)?;
                let sigs = self.order_sigs(mine, sig);
                tx.input[0].witness = WitnessStack::new()
                    .push(sigs.0.as_ref().to_vec())
                    .push(sigs.1.as_ref().to_vec())
                    .build(&leaf.script, &self.funding_tree.control_block("funding")?);
                let txid = self.broadcast(&tx, "coop_close")?;
                self.closing = Some(Closing::Cooperative { txid });
                Ok(vec![])
            }
        }
    }

    /// (user sig, hub sig) from (mine, theirs).
    fn order_sigs(&self, mine: Signature, theirs: Signature) -> (Signature, Signature) {
        match self.me {
            Role::User => (mine, theirs),
            Role::Hub => (theirs, mine),
        }
    }

    // ----- closing -----

    fn close_tx(&self, fee: Amount) -> Result<Transaction> {
        let st = self.current_state();
        ensure!(st.contracts.is_empty(), "resolve contracts before a cooperative close");
        let half = fee / 2;
        let outs: Vec<TxOut> = Role::BOTH
            .iter()
            .filter_map(|r| {
                let v = st.balance(*r).checked_sub(half)?;
                (v >= self.params.dust).then(|| TxOut { value: v, script_pubkey: self.pubkeys[r.idx()].payout_spk.clone() })
            })
            .collect();
        Ok(build_tx(&[(self.funding.0, Sequence::ENABLE_RBF_NO_LOCKTIME)], outs, bitcoin::absolute::LockTime::ZERO))
    }

    pub fn propose_close(&mut self) -> Result<Vec<Envelope>> {
        ensure!(self.pending.is_none(), "cannot close with a pending update");
        let fee = self.params.commit_fee;
        let tx = self.close_tx(fee)?;
        let leaf = self.funding_tree.leaf("funding")?;
        let sig = sign_tapscript(&self.keys.funding, &tx, 0, std::slice::from_ref(&self.funding.1), &leaf.script)?;
        self.close_pending = Some((tx, fee));
        Ok(vec![self.env(Msg::CloseRequest { fee, sig })])
    }

    /// Broadcast my commitment for the current state.
    pub fn force_close(&mut self) -> Result<Txid> {
        let seq = self.current;
        self.force_close_at(seq)
    }

    /// Broadcast my commitment for `seq`. Honest parties only use `current`;
    /// scenarios use an old seq to test the penalty.
    pub fn force_close_at(&mut self, seq: u64) -> Result<Txid> {
        let rec = self.states.get(&seq).ok_or_else(|| anyhow!("no state {seq}"))?;
        ensure!(rec.signed_by_remote, "state {seq} is not signed by the counterparty");
        let theirs = rec.remote_commit_sig.expect("signed");
        let mut tx = rec.commits[self.me.idx()].tx.clone();
        let leaf = self.funding_tree.leaf("funding")?;
        let mine = sign_tapscript(&self.keys.funding, &tx, 0, std::slice::from_ref(&self.funding.1), &leaf.script)?;
        let sigs = self.order_sigs(mine, theirs);
        tx.input[0].witness = WitnessStack::new()
            .push(sigs.0.as_ref().to_vec())
            .push(sigs.1.as_ref().to_vec())
            .build(&leaf.script, &self.funding_tree.control_block("funding")?);
        let txid = self.broadcast(&tx, &format!("commitment_{seq}"))?;
        self.closing = Some(Closing::Local { seq, confirmed_at: None });
        Ok(txid)
    }

    // ----- watch loop -----

    /// Process a confirmed block. Performs channel-level reactions (penalty,
    /// balance claims) and returns events for the contract layer.
    pub fn on_block(&mut self, height: u32, txs: &[Transaction]) -> Result<Vec<ChainEvent>> {
        let mut events = Vec::new();
        for tx in txs {
            let spends_funding = tx.input.iter().any(|i| i.previous_output == self.funding.0);
            if spends_funding {
                events.extend(self.on_funding_spent(tx, height)?);
            }
            for i in &tx.input {
                self.spent_on_chain.insert(i.previous_output);
                if self.watched.contains(&i.previous_output) {
                    events.push(ChainEvent::OutputSpent { outpoint: i.previous_output, tx: tx.clone(), height });
                }
            }
        }
        // delayed to_local after my own force-close
        if let Some(Closing::Local { seq, confirmed_at: Some(h) }) = self.closing.clone() {
            if height + 1 >= h + u32::from(self.params.to_self_delay) {
                self.claim_to_local(seq)?;
            }
        }
        Ok(events)
    }

    fn on_funding_spent(&mut self, tx: &Transaction, height: u32) -> Result<Vec<ChainEvent>> {
        let txid = tx.compute_txid();
        if let Some(Closing::Cooperative { txid: c }) = &self.closing {
            if *c == txid {
                info!(party = %self.me, %txid, "cooperative close confirmed");
                return Ok(vec![]);
            }
        }
        let me = self.me;
        let found = self.states.iter().find_map(|(seq, rec)| {
            if rec.commits[me.idx()].txid() == txid {
                Some((*seq, true))
            } else if rec.commits[me.other().idx()].txid() == txid {
                Some((*seq, false))
            } else {
                None
            }
        });
        match found {
            Some((seq, true)) => {
                info!(party = %me, seq, height, "my commitment confirmed");
                self.closing = Some(Closing::Local { seq, confirmed_at: Some(height) });
                Ok(vec![ChainEvent::LocalCommitConfirmed { seq, height }])
            }
            Some((seq, false)) => {
                let revoked = self.states[&seq].remote_secret.is_some();
                if revoked {
                    warn!(party = %me, seq, height, "counterparty broadcast a REVOKED commitment; sweeping everything");
                    self.closing = Some(Closing::Remote { seq, confirmed_at: height, revoked: true });
                    self.penalty(seq)?;
                    Ok(vec![ChainEvent::RemoteRevokedCommitConfirmed { seq, height }])
                } else {
                    info!(party = %me, seq, height, "counterparty's commitment confirmed");
                    self.closing = Some(Closing::Remote { seq, confirmed_at: height, revoked: false });
                    self.claim_to_remote(seq)?;
                    Ok(vec![ChainEvent::RemoteCommitConfirmed { seq, height }])
                }
            }
            None => {
                warn!(party = %me, %txid, "funding spent by an unknown transaction");
                Ok(vec![])
            }
        }
    }

    /// Sweep every output of the counterparty's revoked commitment `seq`.
    fn penalty(&mut self, seq: u64) -> Result<()> {
        let secret = self.states[&seq].remote_secret.ok_or_else(|| anyhow!("no secret"))?;
        let c = self.remote_commitment(seq).ok_or_else(|| anyhow!("no commitment"))?.clone();
        let mut inputs = Vec::new();
        for o in &c.outputs {
            let (leaf, before) = match o.kind {
                OutputKind::ToRemote => ("claim", vec![]),
                OutputKind::ToLocal | OutputKind::Contract(_) => ("revoke", vec![secret.to_vec()]),
            };
            inputs.push(SweepInput { outpoint: c.outpoint(o), prevout: c.txout(o), tree: &o.tree, leaf, before_sig: before });
        }
        let tx = build_sweep(&inputs, self.my_payout_spk(), self.sweep_fee, &self.keys.payment, bitcoin::absolute::LockTime::ZERO)?;
        for i in &inputs {
            self.swept.insert(i.outpoint);
        }
        self.broadcast(&tx, &format!("revoke_sweep_{seq}"))?;
        Ok(())
    }

    /// Claim my balance on the counterparty's commitment (no delay).
    fn claim_to_remote(&mut self, seq: u64) -> Result<()> {
        let c = self.remote_commitment(seq).ok_or_else(|| anyhow!("no commitment"))?.clone();
        let Some(o) = c.output(OutputKind::ToRemote) else { return Ok(()) };
        let op = c.outpoint(o);
        if self.is_swept(&op) {
            return Ok(());
        }
        let input = SweepInput { outpoint: op, prevout: c.txout(o), tree: &o.tree, leaf: "claim", before_sig: vec![] };
        let tx = build_sweep(&[input], self.my_payout_spk(), self.sweep_fee, &self.keys.payment, bitcoin::absolute::LockTime::ZERO)?;
        self.swept.insert(op);
        self.broadcast(&tx, "claim_to_remote")?;
        Ok(())
    }

    /// Claim my delayed balance on my own commitment.
    fn claim_to_local(&mut self, seq: u64) -> Result<()> {
        let c = self.my_commitment(seq).ok_or_else(|| anyhow!("no commitment"))?.clone();
        let Some(o) = c.output(OutputKind::ToLocal) else { return Ok(()) };
        let op = c.outpoint(o);
        if self.is_swept(&op) {
            warn!(party = %self.me, seq, "my to_local is already spent (penalised?); nothing to claim");
            return Ok(());
        }
        let input = SweepInput { outpoint: op, prevout: c.txout(o), tree: &o.tree, leaf: "delayed", before_sig: vec![] };
        let tx = build_sweep(&[input], self.my_payout_spk(), self.sweep_fee, &self.keys.delayed, bitcoin::absolute::LockTime::ZERO)?;
        self.swept.insert(op);
        self.broadcast(&tx, "claim_to_local")?;
        Ok(())
    }
}

fn msg_name(m: &Msg) -> &'static str {
    match m {
        Msg::Propose { .. } => "Propose",
        Msg::CommitSigs { .. } => "CommitSigs",
        Msg::RevokeAndAck { .. } => "RevokeAndAck",
        Msg::CloseRequest { .. } => "CloseRequest",
        Msg::CloseSig { .. } => "CloseSig",
    }
}

/// Deliver messages between two parties until nothing is left to send.
/// Returns an error if either party rejects a message.
pub fn run_bus(a: &mut ChannelParty, b: &mut ChannelParty, initial: Vec<Envelope>) -> Result<()> {
    let mut queue: std::collections::VecDeque<Envelope> = initial.into();
    let mut steps = 0;
    while let Some(env) = queue.pop_front() {
        steps += 1;
        ensure!(steps < 1000, "message bus did not quiesce");
        let target = if a.me == env.to { &mut *a } else if b.me == env.to { &mut *b } else { bail!("no such party") };
        let replies = target.handle(env)?;
        queue.extend(replies);
    }
    Ok(())
}
