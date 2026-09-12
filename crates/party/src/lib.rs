//! A party (user or hub): a channel, a Lamport key store, the programs it
//! knows, statements it holds, and the protocol
//! behaviour for contracts — off-chain negotiation of contract changes, and
//! on-chain reaction to commitments, Moves, deadlines and challenge windows.
//! The same code runs for both roles.

pub mod dispute;
pub mod draft;

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex};

use anyhow::{anyhow, bail, ensure, Context, Result};
use bitcoin::{Amount, OutPoint, Transaction, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_btc::{hash160, Hash160};
use lngap_channel::chain::Chain;
use lngap_channel::presign::GraphKey;
use lngap_channel::protocol::{ChainEvent, ChannelParty, Closing, Envelope, Policy};
use lngap_channel::{ChannelParams, ChannelState, PartyKeys, PartyPubKeys, Role};
use lngap_contract::instance::key_label;
use lngap_contract::leaves::move_witness_args;
use lngap_contract::onchain::{check_claim, decode_claim, parse_move_witness, MoveReveals};
use lngap_contract::{Claim, ContractInstance, Extra, ProgramRegistry, CODE_BITS};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::{uint_to_bits, PublicKey, Reveal, PREIMAGE_LEN};
use tracing::{info, warn};

use dispute::{parse_p_inner, parse_p_round, parse_p_sched, parse_q_inner, parse_q_round, terminal_witness, DisputeLive, Stage};
use draft::{apply_change, downcast, fill_my_keys, merge_keys, same_state, Change, MyKeys, StateSpec};
use lngap_channel::sweep::{build_sweep, SweepInput};

/// Messages between parties: channel messages plus the contract-change
/// negotiation that precedes a channel update, plus statements.
#[derive(Clone, Debug)]
pub enum PartyMsg {
    Chan(Envelope),
    /// Proposer -> responder: intended change and resulting state with the
    /// proposer's Lamport keys filled in; for a Move, the reveals of any
    /// extra statements the Move leaf requires.
    Draft { spec: StateSpec, change: Change, extra_reveals: Vec<(String, Reveal)> },
    /// Responder -> proposer: the responder's keys (prover and challenger halves).
    DraftKeys { seq: u64, keys: MyKeys },
    /// Responder -> proposer: the draft is refused.
    Reject { seq: u64, reason: String },
    /// A Lamport-signed statement handed over.
    Statement { label: String, reveal: Reveal },
}

#[derive(Clone, Debug)]
pub struct PEnvelope {
    pub from: Role,
    pub to: Role,
    pub msg: PartyMsg,
}

/// Scripted misbehaviour for scenarios. Honest parties leave everything unset.
#[derive(Clone, Default)]
pub struct Faults {
    /// Ignore every message once the channel reaches this seq.
    pub stop_from_seq: Option<u64>,
    /// Never make an on-chain Move (still settles/splits).
    pub passive_onchain: bool,
    /// Alter the claim committed in my next on-chain Move.
    pub cheat_move: Option<Arc<dyn Fn(&Claim) -> Claim + Send + Sync>>,
    /// Alter the bisection claim's end state committed in my on-chain Move.
    pub cheat_claim: Option<Arc<dyn Fn(&[u32]) -> Vec<u32> + Send + Sync>>,
    /// In dispute rounds, commit these states instead of the honest ones
    /// (index → state); a lying prover's "computation".
    pub cheat_midstates: Option<Arc<dyn Fn(u32, &[u32]) -> Vec<u32> + Send + Sync>>,
    /// Load this data instead of the honest data (step index → words).
    pub cheat_load: Option<Arc<dyn Fn(usize, &[u32]) -> Vec<u32> + Send + Sync>>,
    /// Dispute an honest claim (a griefing challenger).
    pub dispute_anyway: bool,
    /// Stop responding in dispute rounds.
    pub silent_in_rounds: bool,
    /// Stop responding once the dispute reaches the inner level.
    pub silent_in_inner: bool,
    /// Publish these schedule words instead of the honest ones (index → word).
    pub cheat_schedule: Option<Arc<dyn Fn(u32, u32) -> u32 + Send + Sync>>,
    /// Alter inner round states (round index → state); the alteration
    /// propagates through the rest of the prover's "computation".
    pub cheat_inner: Option<Arc<dyn Fn(u32, &[u32; 8]) -> [u32; 8] + Send + Sync>>,
    /// Re-commit this state instead of the committed one (a lying re-commitment).
    pub cheat_recommit: Option<Arc<dyn Fn(bool, &[u32]) -> Vec<u32> + Send + Sync>>,
}

impl std::fmt::Debug for Faults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Faults(stop_from_seq={:?}, passive_onchain={}, cheat={}, cheat_claim={}, dispute_anyway={}, silent_in_rounds={}, silent_in_inner={}, cheat_schedule={}, cheat_inner={}, cheat_load={}, cheat_recommit={})",
            self.stop_from_seq,
            self.passive_onchain,
            self.cheat_move.is_some(),
            self.cheat_claim.is_some(),
            self.dispute_anyway,
            self.silent_in_rounds,
            self.silent_in_inner,
            self.cheat_schedule.is_some(),
            self.cheat_inner.is_some(),
            self.cheat_load.is_some(),
            self.cheat_recommit.is_some()
        )
    }
}

/// What a move policy sees when asked for a move.
pub struct MoveCtx<'a> {
    pub height: u32,
    pub contract_id: u32,
    pub state: &'a [bool],
    /// Does this party hold the reveal for a statement label?
    pub has: &'a dyn Fn(&str) -> bool,
}
pub type MovePolicy = Box<dyn Fn(&MoveCtx) -> Option<Vec<bool>> + Send + Sync>;
/// Should I propose folding this contract now (e.g. a bond I no longer need)?
pub type CancelPolicy = Box<dyn Fn(&MoveCtx) -> bool + Send + Sync>;

/// What the change-acceptance policy sees for a counterparty's draft.
pub struct ChangeCtx<'a> {
    pub height: u32,
    pub change: &'a Change,
    pub current: &'a ChannelState,
    pub has: &'a dyn Fn(&str) -> bool,
}
pub type ChangePolicy = Box<dyn Fn(&ChangeCtx) -> Result<()> + Send + Sync>;

/// A contract output that is on-chain, at some depth of its graph.
#[derive(Clone, Debug)]
struct Live {
    id: u32,
    seq: u64,
    version: Role,
    depth: u32,
    outpoint: OutPoint,
    prevout: TxOut,
    tree: TapTree,
    confirmed_at: u32,
    state: Vec<bool>,
    claim_code: Option<u8>,
    code_reveal: Option<Reveal>,
    prior_state_reveal: Option<Reveal>,
    last_state_reveal: Option<Reveal>,
    resolved: bool,
    dispute: Option<DisputeLive>,
}

/// A statement key this party may need to learn preimages for.
#[derive(Debug)]
struct Watched {
    pk: PublicKey,
    found: Vec<Option<[u8; PREIMAGE_LEN]>>,
}

pub struct Party {
    pub role: Role,
    pub channel: ChannelParty,
    keystore: KeyStore,
    pub programs: ProgramRegistry,
    expected: Arc<Mutex<Option<ChannelState>>>,
    pending_draft: Option<StateSpec>,
    pending_change: Option<(u64, Change)>,
    waiting_since: Option<u32>,
    moves: HashMap<u32, VecDeque<Vec<bool>>>,
    move_policies: HashMap<u32, MovePolicy>,
    cancel_policies: HashMap<u32, CancelPolicy>,
    change_policy: Option<ChangePolicy>,
    /// Statements held: reveals under their labels.
    reveals: HashMap<String, Reveal>,
    /// Statement keys known (for verifying and learning reveals).
    watched: HashMap<String, Watched>,
    by_hash: HashMap<Hash160, (String, usize)>,
    live: Vec<Live>,
    height: u32,
    cancel_tried: HashSet<u32>,
    pub faults: Faults,
    pub log: Vec<String>,
    /// How many blocks an update may stall before force-closing.
    pub stall_blocks: u32,
}

impl Party {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        role: Role,
        seed: Seed,
        remote_pub: PartyPubKeys,
        params: ChannelParams,
        funding: (OutPoint, TxOut),
        initial: ChannelState,
        remote_rev_hashes: [Hash160; 2],
        chain: Arc<dyn Chain>,
        programs: ProgramRegistry,
    ) -> Result<Party> {
        let keys = PartyKeys::from_seed(role, seed.child("channel"));
        let expected: Arc<Mutex<Option<ChannelState>>> = Arc::new(Mutex::new(None));
        let exp = expected.clone();
        let policy: Policy = Box::new(move |_old, new| {
            let e = exp.lock().unwrap();
            match &*e {
                Some(st) if same_state(st, new) => Ok(()),
                Some(_) => bail!("proposed state differs from the agreed draft"),
                None => bail!("no draft was agreed for seq {}", new.seq),
            }
        });
        let channel = ChannelParty::new(keys, remote_pub, params, funding, initial, remote_rev_hashes, chain, policy)?;
        Ok(Party {
            role,
            channel,
            keystore: KeyStore::new(seed.child("lamport")),
            programs,
            expected,
            pending_draft: None,
            pending_change: None,
            waiting_since: None,
            moves: HashMap::new(),
            move_policies: HashMap::new(),
            cancel_policies: HashMap::new(),
            change_policy: None,
            reveals: HashMap::new(),
            watched: HashMap::new(),
            by_hash: HashMap::new(),
            live: Vec::new(),
            height: 0,
            cancel_tried: HashSet::new(),
            faults: Faults::default(),
            log: Vec::new(),
            stall_blocks: 2,
        })
    }

    pub fn height(&self) -> u32 {
        self.height
    }
    pub fn set_height(&mut self, h: u32) {
        self.height = h;
    }
    pub fn keystore(&mut self) -> &mut KeyStore {
        &mut self.keystore
    }

    fn say(&mut self, s: String) {
        info!(party = %self.role, "{s}");
        self.log.push(format!("[{} @ {}] {s}", self.role, self.height));
    }

    fn env(&self, msg: PartyMsg) -> PEnvelope {
        PEnvelope { from: self.role, to: self.role.other(), msg }
    }

    // ----- statements -----

    /// Register a statement key I may need to reveal or learn (its hashes
    /// are baked into leaves; its preimages may arrive by message or on-chain).
    pub fn know_key(&mut self, label: &str, pk: PublicKey) {
        if self.watched.contains_key(label) {
            return;
        }
        for (i, b) in pk.bits.iter().enumerate() {
            self.by_hash.insert(b.h0, (label.to_string(), i));
            self.by_hash.insert(b.h1, (label.to_string(), i));
        }
        let n = pk.n_bits();
        self.watched.insert(label.to_string(), Watched { pk, found: vec![None; n] });
    }

    /// Store a reveal received from someone (verified against the known key).
    pub fn learn_reveal(&mut self, label: &str, reveal: Reveal) -> Result<()> {
        if let Some(w) = self.watched.get(label) {
            w.pk.decode_bits(&reveal).with_context(|| format!("reveal for {label} does not match its key"))?;
        }
        if !self.reveals.contains_key(label) {
            self.say(format!("learned statement {label}"));
        }
        self.reveals.insert(label.to_string(), reveal);
        Ok(())
    }

    pub fn has_reveal(&self, label: &str) -> bool {
        self.reveals.contains_key(label) || self.keystore.is_revealed(label)
    }

    /// The reveal for `extra`: from my own key store if I own the key
    /// (revealing it), else from statements I hold.
    fn reveal_for(&mut self, extra: &Extra) -> Result<Reveal> {
        if let Ok(pk) = self.keystore.public(&extra.label) {
            if pk == extra.pk {
                return self.keystore.reveal_uint(&extra.label, extra.value);
            }
        }
        let r = self.reveals.get(&extra.label).cloned().ok_or_else(|| anyhow!("I do not hold the statement {}", extra.label))?;
        ensure!(extra.pk.decode_uint(&r)? == extra.value, "held statement {} does not say {}", extra.label, extra.value);
        Ok(r)
    }

    /// Hand a statement to the counterparty (revealing my own key if I own it).
    pub fn statement_msg(&mut self, label: &str, value: u32) -> Result<PEnvelope> {
        let pk = self.keystore.public(label).or_else(|_| self.watched.get(label).map(|w| w.pk.clone()).ok_or_else(|| anyhow!("unknown key {label}")))?;
        let reveal = self.reveal_for(&Extra { label: label.to_string(), pk, value })?;
        Ok(self.env(PartyMsg::Statement { label: label.to_string(), reveal }))
    }

    /// Scan a transaction's witnesses for preimages of watched keys.
    fn scan_witnesses(&mut self, tx: &Transaction) {
        let mut completed = Vec::new();
        for input in &tx.input {
            for el in input.witness.iter() {
                if el.len() != PREIMAGE_LEN {
                    continue;
                }
                let h = hash160(el);
                if let Some((label, i)) = self.by_hash.get(&h).cloned() {
                    if self.reveals.contains_key(&label) {
                        continue;
                    }
                    let w = self.watched.get_mut(&label).expect("watched");
                    let mut p = [0u8; PREIMAGE_LEN];
                    p.copy_from_slice(el);
                    w.found[i] = Some(p);
                    if w.found.iter().all(Option::is_some) {
                        completed.push((label, Reveal { preimages: w.found.iter().map(|x| x.unwrap()).collect() }));
                    }
                }
            }
        }
        for (label, r) in completed {
            self.say(format!("learned statement {label} from an on-chain witness ({})", tx.compute_txid()));
            self.reveals.insert(label, r);
        }
    }

    // ----- application intent -----

    /// Queue the moves this party intends to make in contract `id`, in
    /// order. They are played off-chain while the channel cooperates and
    /// on-chain otherwise.
    pub fn queue_moves(&mut self, id: u32, moves: Vec<Vec<bool>>) {
        self.moves.entry(id).or_default().extend(moves);
    }
    /// A dynamic move policy for contract `id`, consulted when the queue is empty.
    pub fn set_move_policy(&mut self, id: u32, p: MovePolicy) {
        self.move_policies.insert(id, p);
    }
    /// A policy for proposing to fold contract `id` cooperatively.
    pub fn set_cancel_policy(&mut self, id: u32, p: CancelPolicy) {
        self.cancel_policies.insert(id, p);
    }
    /// Policy for accepting the counterparty's drafts (default: any valid
    /// change, and Cancel only once the party on turn missed its deadline).
    pub fn set_change_policy(&mut self, p: ChangePolicy) {
        self.change_policy = Some(p);
    }
    fn peek_move(&self, id: u32, state: &[bool]) -> Option<Vec<bool>> {
        if let Some(m) = self.moves.get(&id).and_then(|q| q.front().cloned()) {
            return Some(m);
        }
        let p = self.move_policies.get(&id)?;
        let has = |l: &str| self.has_reveal(l);
        p(&MoveCtx { height: self.height, contract_id: id, state, has: &has })
    }
    fn pop_move(&mut self, id: u32) {
        if let Some(q) = self.moves.get_mut(&id) {
            q.pop_front();
        }
    }

    fn deadline(&self) -> u32 {
        self.height + self.channel.params.deadline_offset()
    }

    /// Propose an off-chain change. Starts the draft/keys/update exchange.
    pub fn propose_change(&mut self, change: Change) -> Result<Vec<PEnvelope>> {
        ensure!(self.channel.closing.is_none(), "channel is closing");
        ensure!(self.channel.pending_seq().is_none() && self.pending_draft.is_none(), "an update is in flight");
        let mut spec = apply_change(self.channel.current_state(), &change, &self.programs)?;
        fill_my_keys(&mut spec, self.role, &mut self.keystore, &self.programs)?;
        let mut extra_reveals = Vec::new();
        if let Change::Move { id, .. } = &change {
            let inst = downcast(self.channel.current_state().contract(*id).ok_or_else(|| anyhow!("no contract {id}"))?).clone();
            for e in inst.move_extras(1).expects {
                let r = self.reveal_for(&e).with_context(|| format!("cannot move in contract {id}"))?;
                extra_reveals.push((e.label, r));
            }
        }
        self.say(format!("propose seq {}: {}", spec.seq, self.describe_change(&change)));
        self.pending_draft = Some(spec.clone());
        self.pending_change = Some((spec.seq, change.clone()));
        self.waiting_since = Some(self.height);
        Ok(vec![self.env(PartyMsg::Draft { spec, change, extra_reveals })])
    }

    pub fn pay(&mut self, amount: Amount) -> Result<Vec<PEnvelope>> {
        self.propose_change(Change::Pay { from: self.role, amount })
    }

    pub fn open_contract(&mut self, id: u32, program: &str, stakes: [Amount; 2]) -> Result<Vec<PEnvelope>> {
        let deadline = self.deadline();
        self.open_contract_with_deadline(id, program, stakes, deadline)
    }

    pub fn open_contract_with_deadline(&mut self, id: u32, program: &str, stakes: [Amount; 2], deadline: u32) -> Result<Vec<PEnvelope>> {
        self.propose_change(Change::Open { id, program: program.to_string(), stakes, deadline })
    }

    pub fn propose_close(&mut self) -> Result<Vec<PEnvelope>> {
        Ok(self.channel.propose_close()?.into_iter().map(PartyMsg::Chan).map(|m| self.env(m)).collect())
    }

    /// Off-chain autonomy: if it is my turn in a contract and I have a move,
    /// propose it; if a contract is terminal, propose folding it; if the
    /// counterparty missed its deadline, propose cancelling. Called by the
    /// harness between blocks; returns messages to deliver.
    pub fn poll(&mut self) -> Result<Vec<PEnvelope>> {
        if self.channel.closing.is_some() || self.channel.pending_seq().is_some() || self.pending_draft.is_some() {
            return Ok(vec![]);
        }
        if self.faults.stop_from_seq.is_some_and(|s| self.channel.current_seq() >= s) {
            return Ok(vec![]);
        }
        let contracts: Vec<(u32, Option<Role>, Vec<bool>, u32)> = self.channel.current_state().contracts.iter().map(|c| {
            let i = downcast(c);
            (i.id, i.turn(), i.state.clone(), i.deadline)
        }).collect();
        for (id, turn, state, deadline) in contracts {
            if let Some(p) = self.cancel_policies.get(&id) {
                let has = |l: &str| self.has_reveal(l);
                if p(&MoveCtx { height: self.height, contract_id: id, state: &state, has: &has }) && !self.cancel_tried.contains(&id) {
                    self.cancel_tried.insert(id);
                    return self.propose_change(Change::Cancel { id });
                }
            }
            match turn {
                Some(r) if r == self.role => {
                    if let Some(mv) = self.peek_move(id, &state) {
                        let deadline = self.deadline();
                        return self.propose_change(Change::Move { id, mv, deadline });
                    }
                }
                Some(_) if self.height >= deadline && !self.cancel_tried.contains(&id) => {
                    self.cancel_tried.insert(id);
                    return self.propose_change(Change::Cancel { id });
                }
                None => return self.propose_change(Change::Resolve { id }),
                _ => {}
            }
        }
        Ok(vec![])
    }

    // ----- messages -----

    pub fn handle(&mut self, env: PEnvelope) -> Result<Vec<PEnvelope>> {
        ensure!(env.to == self.role, "misrouted");
        if self.faults.stop_from_seq.is_some_and(|s| self.channel.current_seq() >= s) {
            warn!(party = %self.role, "faulty: dropping message");
            return Ok(vec![]);
        }
        let out = match env.msg {
            PartyMsg::Chan(e) => {
                let replies = self.channel.handle(e)?;
                replies.into_iter().map(|m| self.env(PartyMsg::Chan(m))).collect()
            }
            PartyMsg::Draft { spec, change, extra_reveals } => match self.on_draft(spec, change, extra_reveals) {
                Ok(v) => v,
                Err(e) => {
                    let seq = self.channel.current_seq() + 1;
                    self.say(format!("rejecting draft seq {seq}: {e:#}"));
                    vec![self.env(PartyMsg::Reject { seq, reason: format!("{e:#}") })]
                }
            },
            PartyMsg::DraftKeys { seq, keys } => self.on_draft_keys(seq, keys)?,
            PartyMsg::Reject { seq, reason } => {
                self.say(format!("draft seq {seq} rejected by counterparty: {reason}"));
                let was_move = matches!(self.pending_change, Some((_, Change::Move { .. })));
                self.pending_draft = None;
                self.pending_change = None;
                self.waiting_since = None;
                if was_move && self.channel.closing.is_none() {
                    // a valid move refused off-chain is enforced on-chain
                    self.say(format!("counterparty refuses my move; force-closing at state {} to make it on-chain", self.channel.current_seq()));
                    self.channel.force_close()?;
                }
                vec![]
            }
            PartyMsg::Statement { label, reveal } => {
                if let Err(e) = self.learn_reveal(&label, reveal) {
                    self.say(format!("ignoring bad statement {label}: {e:#}"));
                }
                vec![]
            }
        };
        self.after_update_progress();
        Ok(out)
    }

    fn on_draft(&mut self, spec: StateSpec, change: Change, extra_reveals: Vec<(String, Reveal)>) -> Result<Vec<PEnvelope>> {
        ensure!(self.channel.pending_seq().is_none() && self.pending_draft.is_none(), "draft while an update is in flight");
        let mine = apply_change(self.channel.current_state(), &change, &self.programs).context("counterparty's change is invalid")?;
        ensure!(mine.same_modulo_keys(&spec), "counterparty's draft does not match its stated change");
        let p = &self.channel.params;
        let min_deadline = self.height + u32::from(p.to_self_delay) + u32::from(p.delta);
        match &change {
            Change::Open { deadline, .. } | Change::Move { deadline, .. } => {
                ensure!(*deadline >= min_deadline, "deadline {deadline} too close (min {min_deadline})");
            }
            _ => {}
        }
        // extras the Move leaf would require: the mover must show them now
        let mut learned = Vec::new();
        if let Change::Move { id, .. } = &change {
            let inst = downcast(self.channel.current_state().contract(*id).ok_or_else(|| anyhow!("no contract {id}"))?).clone();
            for e in inst.move_extras(1).expects {
                let (_, r) = extra_reveals.iter().find(|(l, _)| *l == e.label).ok_or_else(|| anyhow!("draft lacks the statement {}", e.label))?;
                ensure!(e.pk.decode_uint(r)? == e.value, "statement {} in draft does not say {}", e.label, e.value);
                learned.push((e.label.clone(), r.clone()));
            }
        }
        // a Move into a depth that carries a claim: recompute the claim from the
        // served data; an invalid claim is refused here and must go on-chain,
        // where its committed end state can be disputed
        if let Change::Move { id, .. } = &change {
            let inst = downcast(self.channel.current_state().contract(*id).ok_or_else(|| anyhow!("no contract {id}"))?).clone();
            if let Some(spec) = inst.claim_spec(1) {
                ensure!(spec.valid(&inst.claim_data(1)), "the move's claim does not hold on the served data");
            }
        }
        // application policy
        let has = |l: &str| self.has_reveal(l);
        let cctx = ChangeCtx { height: self.height, change: &change, current: self.channel.current_state(), has: &has };
        match &self.change_policy {
            Some(pol) => pol(&cctx)?,
            None => default_change_policy(&cctx)?,
        }
        for (l, r) in learned {
            self.learn_reveal(&l, r)?;
        }
        let mut full = spec;
        let keys = fill_my_keys(&mut full, self.role, &mut self.keystore, &self.programs)?;
        ensure!(full.contracts.iter().all(|c| c.complete()), "draft incomplete after adding my keys");
        let seq = full.seq;
        let state = full.into_state(&self.programs)?;
        *self.expected.lock().unwrap() = Some(state);
        self.pending_change = Some((seq, change.clone()));
        self.waiting_since = Some(self.height);
        self.say(format!("accept draft seq {seq}: {}", self.describe_change(&change)));
        Ok(vec![self.env(PartyMsg::DraftKeys { seq, keys })])
    }

    fn on_draft_keys(&mut self, seq: u64, keys: MyKeys) -> Result<Vec<PEnvelope>> {
        let mut spec = self.pending_draft.take().ok_or_else(|| anyhow!("DraftKeys without a pending draft"))?;
        ensure!(spec.seq == seq, "DraftKeys for {seq} but draft is {}", spec.seq);
        merge_keys(&mut spec, self.role.other(), keys)?;
        let state = spec.into_state(&self.programs)?;
        *self.expected.lock().unwrap() = Some(state.clone());
        let msgs = self.channel.propose(state)?;
        Ok(msgs.into_iter().map(|m| self.env(PartyMsg::Chan(m))).collect())
    }

    /// Bookkeeping once an update completes.
    fn after_update_progress(&mut self) {
        if let Some((seq, change)) = self.pending_change.clone() {
            if self.channel.current_seq() >= seq {
                if let Change::Move { id, .. } = change {
                    if self.channel.current_state().contract(id).is_some() {
                        let was_me = matches!(self.pending_change_mover(&change), Some(r) if r == self.role);
                        if was_me {
                            self.pop_move(id);
                        }
                    }
                }
                self.pending_change = None;
                *self.expected.lock().unwrap() = None;
                self.say(format!("state {seq} signed by both"));
            }
        }
        if self.channel.pending_seq().is_none() && self.pending_draft.is_none() {
            self.waiting_since = None;
        }
    }

    fn pending_change_mover(&self, change: &Change) -> Option<Role> {
        if let Change::Move { id, .. } = change {
            let prev = self.channel.record(self.channel.current_seq() - 1)?;
            let c = prev.state.contract(*id)?;
            return downcast(c).turn();
        }
        None
    }

    // ----- chain -----

    /// Process a confirmed block: learn statements from witnesses, then
    /// channel-level reactions, then contract reactions, then timers.
    pub fn on_block(&mut self, height: u32, txs: &[Transaction]) -> Result<()> {
        self.height = height;
        for tx in txs {
            self.scan_witnesses(tx);
        }
        let events = self.channel.on_block(height, txs)?;
        for ev in events {
            self.on_event(ev)?;
        }
        self.tick()
    }

    fn on_event(&mut self, ev: ChainEvent) -> Result<()> {
        match ev {
            ChainEvent::LocalCommitConfirmed { seq, height } => self.on_commit_confirmed(seq, self.role, height),
            ChainEvent::RemoteCommitConfirmed { seq, height } => self.on_commit_confirmed(seq, self.role.other(), height),
            ChainEvent::RemoteRevokedCommitConfirmed { seq, .. } => {
                self.say(format!("counterparty broadcast revoked state {seq}: penalty sweep sent"));
                Ok(())
            }
            ChainEvent::OutputSpent { outpoint, tx, height } => self.on_output_spent(outpoint, tx, height),
        }
    }

    fn on_commit_confirmed(&mut self, seq: u64, version: Role, height: u32) -> Result<()> {
        let rec = self.channel.record(seq).ok_or_else(|| anyhow!("no record {seq}"))?;
        let commit = &rec.commits[version.idx()];
        let mut new_live = Vec::new();
        for o in &commit.outputs {
            if let lngap_channel::commit::OutputKind::Contract(id) = o.kind {
                let inst = downcast(rec.state.contract(id).expect("contract"));
                new_live.push(Live {
                    id,
                    seq,
                    version,
                    depth: 0,
                    outpoint: commit.outpoint(o),
                    prevout: commit.txout(o),
                    tree: o.tree.clone(),
                    confirmed_at: height,
                    state: inst.state.clone(),
                    claim_code: None,
                    code_reveal: None,
                    prior_state_reveal: None,
                    last_state_reveal: None,
                    resolved: false,
                    dispute: None,
                });
            }
        }
        let who = if version == self.role { "my" } else { "counterparty's" };
        self.say(format!("{who} commitment for state {seq} confirmed with {} contract output(s)", new_live.len()));
        for l in new_live {
            let inst = self.instance(&l);
            self.say(format!("contract {} on-chain at depth 0: state {}, turn {:?}, deadline {}", l.id, inst.program.describe_state_bits(&l.state), inst.turn(), inst.deadline));
            self.channel.watch(l.outpoint);
            self.live.push(l);
        }
        Ok(())
    }

    fn instance(&self, l: &Live) -> Arc<ContractInstance> {
        let rec = self.channel.record(l.seq).expect("record");
        let c = rec.state.contract(l.id).expect("contract");
        Arc::new(downcast(c).clone())
    }

    fn on_output_spent(&mut self, outpoint: OutPoint, tx: Transaction, height: u32) -> Result<()> {
        if let Some(idx) = self.live.iter().position(|l| l.dispute.as_ref().is_some_and(|d| d.outpoint == outpoint && d.stage != Stage::Resolved)) {
            return self.on_dispute_output_spent(idx, tx, height);
        }
        let Some(idx) = self.live.iter().position(|l| l.outpoint == outpoint && !l.resolved) else { return Ok(()) };
        let vin = tx.input.iter().position(|i| i.previous_output == outpoint).expect("spends it");
        let leaf = self.live[idx].tree.identify_leaf(&tx.input[vin].witness).map(|l| l.name.clone());
        let id = self.live[idx].id;
        let txid = tx.compute_txid();
        match leaf.as_deref() {
            Some(name) if name.starts_with("move_") => {
                let d: u32 = name[5..].parse()?;
                self.on_move_confirmed(idx, d, &tx, height)
            }
            Some("dispute") => self.on_dispute_started(idx, &tx, height),
            Some(name) => {
                self.live[idx].resolved = true;
                self.say(format!("contract {id} resolved by {name} ({txid})"));
                Ok(())
            }
            None => {
                self.live[idx].resolved = true;
                self.say(format!("contract {id} output spent by an unrecognised leaf ({txid})"));
                Ok(())
            }
        }
    }

    fn on_move_confirmed(&mut self, idx: usize, d: u32, tx: &Transaction, height: u32) -> Result<()> {
        let inst = self.instance(&self.live[idx]);
        let keys = inst.depth_keys(d).clone();
        let extras = inst.move_extras(d).expects;
        let extra_bits: Vec<usize> = extras.iter().map(|e| e.pk.n_bits()).collect();
        let claim_params = inst.claim_keys(d).map(|c| c.end.params);
        let reveals = parse_move_witness(&tx.input[0].witness, inst.program.n_move_bits(), inst.program.n_state_bits(), &extra_bits, claim_params)?;
        for (e, r) in extras.iter().zip(&reveals.extras) {
            self.learn_reveal(&e.label, r.clone())?;
        }
        let prior = self.live[idx].state.clone();
        let claim = decode_claim(&*inst.program, &keys, prior, &reveals)?;
        let ctx = self.channel.commit_ctx(self.live[idx].seq, self.live[idx].version)?;
        let tree = inst.depth_tree(&ctx, d)?;
        {
            let l = &mut self.live[idx];
            l.depth = d;
            l.outpoint = OutPoint { txid: tx.compute_txid(), vout: 0 };
            l.prevout = tx.output[0].clone();
            l.tree = tree;
            l.confirmed_at = height;
            l.prior_state_reveal = l.last_state_reveal.take();
            l.last_state_reveal = Some(reveals.state.clone());
            l.state = claim.new.clone();
            l.claim_code = Some(claim.code);
            l.code_reveal = Some(reveals.code.clone());
        }
        let op = self.live[idx].outpoint;
        self.channel.watch(op);
        let id = self.live[idx].id;
        let outcome = inst.program.outcome_by_code(claim.code).map(|o| o.name).unwrap_or_else(|_| "?".into());
        self.say(format!(
            "contract {id}: move_{d} by {} confirmed: move {}, claimed state {}, claimed outcome {outcome}",
            keys.prover,
            inst.program.describe_move_bits(&claim.mv),
            inst.program.describe_state_bits(&claim.new)
        ));
        // a bisection claim: the end state the prover committed
        if let (Some(spec), Some(end_sig)) = (inst.claim_spec(d), reveals.claim_end.clone()) {
            let ckeys = inst.claim_keys(d).expect("claim keys");
            let msg = ckeys.end.verify(&end_sig)?;
            let end = lngap_contract::claim::state_from_msg(&msg);
            let data = self.claim_data(&inst, d);
            let my_states = spec.states(&data);
            let honest = my_states.last().unwrap().clone();
            let valid = spec.valid(&data);
            let ok = end == honest && valid;
            self.say(format!(
                "contract {id}: claimed end state {}.. is {}{}",
                hex::encode(&msg[..4]),
                if end == honest { "correct" } else { "WRONG" },
                if valid { "" } else { "; a predicate of the claim FAILS" }
            ));
            let l = &mut self.live[idx];
            l.dispute = Some(DisputeLive {
                depth: d,
                prover: keys.prover,
                spec: spec.clone(),
                data,
                stage: Stage::Resolved, // becomes WaitP(1) when the dispute tx confirms
                known: [(spec.n_steps(), (end, end_sig))].into_iter().collect(),
                path: vec![],
                outpoint: l.outpoint,
                prevout: l.prevout.clone(),
                tree: l.tree.clone(),
                confirmed_at: height,
                trees: vec![],
                my_states,
                responded: false,
                re_cur: None,
                re_next: None,
                blocks: HashMap::new(),
                sched: HashMap::new(),
                inner_known: HashMap::new(),
                inner_path: vec![],
                my_sched: None,
                my_inner: None,
            });
            if keys.prover != self.role && (!ok || self.faults.dispute_anyway) {
                self.say(format!("contract {id}: disputing the claim"));
                let l = self.live[idx].clone();
                return self.broadcast_graph(&l, &format!("d{d}/dispute"), &[]);
            }
        }
        if keys.prover == self.role {
            return Ok(());
        }
        match check_claim(&*inst.program, &claim) {
            Ok(()) => {
                self.say(format!("contract {id}: counterparty's move_{d} is consistent with the program"));
                self.disprove(idx, d, &claim, &reveals, false)
            }
            Err(reason) => {
                self.say(format!("contract {id}: counterparty's move_{d} is INVALID ({reason}); disproving"));
                self.disprove(idx, d, &claim, &reveals, true)
            }
        }
    }

    /// Use the first disprove leaf whose native check fires and whose needs
    /// I can satisfy. With `expect_one` a consistent claim may still be
    /// refutable by a statement I hold (e.g. an attestation).
    fn disprove(&mut self, idx: usize, d: u32, claim: &Claim, reveals: &MoveReveals, expect_one: bool) -> Result<()> {
        let inst = self.instance(&self.live[idx]);
        let specs = inst.disprove_specs(d);
        let mut chosen = None;
        for s in &specs {
            if !(s.detects)(claim) {
                continue;
            }
            let mut needs = Vec::new();
            let mut ok = true;
            for e in &s.needs {
                match self.reveal_for(e) {
                    Ok(r) => needs.push(r),
                    Err(_) => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                chosen = Some((s.clone(), needs));
                break;
            }
        }
        let Some((spec, needs)) = chosen else {
            if expect_one {
                self.say(format!("contract {}: no disprove leaf applies — cannot punish", self.live[idx].id));
            }
            return Ok(());
        };
        let l = &self.live[idx];
        let leaf_name = format!("disprove_{}", spec.name);
        let leaf = l.tree.leaf(&leaf_name)?.clone();
        let fee = self.channel.params.presign_fee;
        let mut tx = build_spend(l.outpoint, &Timelock::NONE, vec![TxOut { value: l.prevout.value - fee, script_pubkey: self.channel.my_payout_spk() }]);
        let sig = sign_tapscript(&self.channel.keys.payment, &tx, 0, std::slice::from_ref(&l.prevout), &leaf.script)?;
        let mut w = WitnessStack::new();
        w.push(sig.as_ref().to_vec()).extend(spec.witness_args(l.prior_state_reveal.as_ref(), &reveals.mv, &reveals.state, &reveals.code, &needs));
        tx.input[0].witness = w.build(&leaf.script, &l.tree.control_block(&leaf_name)?);
        let op = l.outpoint;
        let id = l.id;
        self.channel.mark_swept(op);
        self.channel.broadcast(&tx, &leaf_name)?;
        self.say(format!("contract {id}: broadcast {leaf_name} taking {} sats", tx.output[0].value));
        Ok(())
    }

    /// Timers: force-close on stall or missed counterparty deadline; make my
    /// on-chain move when it is my turn; settle after the deadline; split
    /// after the challenge window.
    fn tick(&mut self) -> Result<()> {
        let height = self.height;
        if self.channel.closing.is_none() {
            if let Some(h0) = self.waiting_since {
                if height >= h0 + self.stall_blocks {
                    self.say(format!("counterparty stalled since height {h0}; force-closing at state {}", self.channel.current_seq()));
                    self.channel.force_close()?;
                }
            }
            if self.channel.closing.is_none() {
                let grace = self.stall_blocks;
                let overdue: Vec<u32> = self.channel.current_state().contracts.iter().map(|c| downcast(c)).filter(|i| i.turn().is_some_and(|t| t != self.role) && height >= i.deadline + grace).map(|i| i.id).collect();
                if let Some(id) = overdue.first() {
                    self.say(format!("contract {id}: counterparty missed its deadline and did not cancel; force-closing to settle"));
                    self.channel.force_close()?;
                }
            }
        }
        for idx in 0..self.live.len() {
            if self.live[idx].resolved {
                continue;
            }
            if self.live[idx].dispute.as_ref().is_some_and(|d| d.stage != Stage::Resolved) {
                self.dispute_tick(idx)?;
                continue;
            }
            if self.channel.is_swept(&self.live[idx].outpoint) {
                continue;
            }
            self.tick_live(idx)?;
        }
        Ok(())
    }

    fn timelock_ready(&self, l: &Live, tl: &Timelock) -> bool {
        let csv_ok = match tl.csv {
            Some(n) => self.height + 1 >= l.confirmed_at + u32::from(n),
            None => true,
        };
        let cltv_ok = match tl.cltv {
            Some(h) => self.height >= h,
            None => true,
        };
        csv_ok && cltv_ok
    }

    fn tick_live(&mut self, idx: usize) -> Result<()> {
        let inst = self.instance(&self.live[idx]);
        let l = self.live[idx].clone();
        let params = self.channel.params;
        if l.depth == 0 {
            let my_turn = inst.turn() == Some(self.role);
            if my_turn && !self.faults.passive_onchain && self.height < inst.deadline {
                if let Some(mv) = self.peek_move(l.id, &l.state) {
                    let leaf = l.tree.leaf("move_1")?;
                    if self.timelock_ready(&l, &leaf.timelock) {
                        return self.broadcast_move(idx, 1, mv);
                    }
                    return Ok(());
                }
            }
            if self.height >= inst.deadline && self.timelock_ready(&l, &Timelock::csv(params.to_self_delay)) {
                let r = inst.resolution();
                self.say(format!("contract {}: deadline {} passed with no move; broadcasting settle (R(s) = {})", l.id, inst.deadline, r.name));
                return self.broadcast_graph(&l, "settle", &[]);
            }
            return Ok(());
        }
        let d = l.depth;
        let prover = inst.prover_at(d);
        let code = l.claim_code.expect("depth ≥ 1 has a claim");
        let my_move = prover != self.role && inst.program.turn_bits(&l.state)? == Some(self.role) && d < inst.max_depth() && !self.faults.passive_onchain;
        if my_move {
            if let Some(mv) = self.peek_move(l.id, &l.state) {
                let leaf = l.tree.leaf(&format!("move_{}", d + 1))?;
                if self.timelock_ready(&l, &leaf.timelock) {
                    return self.broadcast_move(idx, d + 1, mv);
                }
            }
        }
        let outcome = inst.program.outcome_by_code(code)?;
        let window = inst.window(&params, d, &outcome);
        if self.timelock_ready(&l, &Timelock::csv(window)) {
            self.say(format!("contract {}: challenge window ({window} blocks) after move_{d} passed; broadcasting split_{}", l.id, outcome.name));
            let extra = l.code_reveal.as_ref().expect("code reveal stored with the claim").consumption_order();
            return self.broadcast_graph(&l, &format!("split_{d}_{}", outcome.name), &extra);
        }
        Ok(())
    }

    fn broadcast_graph(&mut self, l: &Live, label: &str, extra: &[Vec<u8>]) -> Result<()> {
        let key = GraphKey { version: l.version, contract_id: l.id, label: label.to_string() };
        let rec = self.channel.record(l.seq).ok_or_else(|| anyhow!("no record"))?;
        let ptx = rec.graph.get(&key).ok_or_else(|| anyhow!("no graph tx {key}"))?;
        let tx = ptx.finalize(extra)?;
        self.channel.mark_swept(l.outpoint);
        self.channel.broadcast(&tx, label)?;
        Ok(())
    }

    fn broadcast_move(&mut self, idx: usize, d: u32, mv: Vec<bool>) -> Result<()> {
        let l = self.live[idx].clone();
        let inst = self.instance(&l);
        let new = inst.program.transition_bits(&l.state, &mv, self.role).context("my own move is invalid")?;
        let code = inst.program.resolution_bits(&new)?.code;
        let mut claim = Claim { prior: l.state.clone(), mv, new, code, mover: self.role };
        if let Some(cheat) = &self.faults.cheat_move {
            claim = cheat(&claim);
            self.say(format!("contract {}: CHEATING in move_{d}: claiming move {} state {} code {}", l.id, inst.program.describe_move_bits(&claim.mv), inst.program.describe_state_bits(&claim.new), claim.code));
        }
        let mut extras = Vec::new();
        for e in inst.move_extras(d).expects {
            match self.reveal_for(&e) {
                Ok(r) => extras.push(r),
                Err(err) => {
                    self.say(format!("contract {}: cannot move_{d}: {err:#}", l.id));
                    return Ok(());
                }
            }
        }
        let ks = inst.keys_seq;
        let mv_r = self.keystore.reveal_bits(&key_label(l.id, ks, d, "move"), &claim.mv)?;
        let st_r = self.keystore.reveal_bits(&key_label(l.id, ks, d, "state"), &claim.new)?;
        let code_r = self.keystore.reveal_bits(&key_label(l.id, ks, d, "code"), &uint_to_bits(u32::from(claim.code), CODE_BITS))?;
        // the claim's end state (signed with the Winternitz key), before borrowing the record
        let end_sig = match inst.claim_spec(d) {
            Some(spec) => {
                let data = self.claim_data(&inst, d);
                let mut end = spec.states(&data).last().unwrap().clone();
                if let Some(cheat) = &self.faults.cheat_claim {
                    end = cheat(&end);
                    self.say(format!("contract {}: CHEATING: claiming a false end state", l.id));
                }
                Some(self.keystore.sign_wots(&lngap_contract::claim::end_label(l.id, ks, d), &lngap_contract::claim::words_bytes(&end))?)
            }
            None => None,
        };
        let key = GraphKey { version: l.version, contract_id: l.id, label: format!("move_{d}") };
        let rec = self.channel.record(l.seq).ok_or_else(|| anyhow!("no record"))?;
        let ptx = rec.graph.get(&key).ok_or_else(|| anyhow!("no graph tx {key}"))?;
        let tx = ptx.finalize(&move_witness_args(&mv_r, &st_r, &code_r, &extras, end_sig.as_ref()))?;
        self.pop_move(l.id);
        self.channel.mark_swept(l.outpoint);
        self.say(format!("contract {}: broadcasting move_{d}: {} -> state {}, outcome code {}", l.id, inst.program.describe_move_bits(&claim.mv), inst.program.describe_state_bits(&claim.new), claim.code));
        self.channel.broadcast(&tx, &format!("move_{d}"))?;
        Ok(())
    }

    /// Narrative log lines so far.
    pub fn narrative(&self) -> &[String] {
        &self.log
    }
    pub fn closing(&self) -> Option<&Closing> {
        self.channel.closing.as_ref()
    }

    fn describe_change(&self, c: &Change) -> String {
        match c {
            Change::Pay { from, amount } => format!("{from} pays {amount}"),
            Change::Open { id, program, stakes, deadline } => format!("open contract {id} ({program}) stakes {}/{} deadline {deadline}", stakes[0], stakes[1]),
            Change::Move { id, mv, deadline } => {
                let m = self.channel.current_state().contract(*id).map(|c| downcast(c).program.describe_move_bits(mv)).unwrap_or_default();
                format!("move in contract {id}: {m} (deadline {deadline})")
            }
            Change::Resolve { id } => format!("resolve contract {id}"),
            Change::Cancel { id } => format!("cancel contract {id} (fold R(s))"),
        }
    }
}

/// Default acceptance: any valid Pay/Open/Move/Resolve; Cancel only if the
/// party on turn has missed its deadline (then R(s) is enforceable anyway).
pub fn default_change_policy(ctx: &ChangeCtx) -> Result<()> {
    if let Change::Cancel { id } = ctx.change {
        let c = ctx.current.contract(*id).ok_or_else(|| anyhow!("no contract {id}"))?;
        let i = downcast(c);
        ensure!(i.turn().is_some() && ctx.height >= i.deadline, "cancel refused: contract {id} has not expired");
    }
    Ok(())
}

/// Deliver messages between two parties until quiescent.
pub fn run_bus(a: &mut Party, b: &mut Party, initial: Vec<PEnvelope>) -> Result<()> {
    let mut queue: VecDeque<PEnvelope> = initial.into();
    let mut steps = 0;
    while let Some(env) = queue.pop_front() {
        steps += 1;
        ensure!(steps < 10_000, "bus did not quiesce");
        let target = if a.role == env.to { &mut *a } else { &mut *b };
        queue.extend(target.handle(env)?);
    }
    Ok(())
}

// ----- bisection disputes -----

impl Party {
    /// The prover data for a claim at `depth` as this party knows it (the
    /// program's honest data; a lying prover's `cheat_load` applies to what
    /// it will commit).
    fn claim_data(&self, inst: &ContractInstance, depth: u32) -> lngap_contract::ClaimData {
        let spec = inst.claim_spec(depth).expect("claim");
        let mut data = inst.claim_data(depth);
        if inst.prover_at(depth) == self.role {
            if let Some(cheat) = &self.faults.cheat_load {
                for (k, step) in spec.data_steps().iter().enumerate() {
                    data[k] = cheat(*step, &data[k]);
                }
            }
        }
        data
    }

    /// The `dispute` transaction confirmed: the chain's first output waits for the prover's round 1.
    fn on_dispute_started(&mut self, idx: usize, tx: &Transaction, height: u32) -> Result<()> {
        let l = self.live[idx].clone();
        let inst = self.instance(&l);
        let d = l.depth;
        let ctx = self.channel.commit_ctx(l.seq, l.version)?;
        let trees = inst.dispute_trees(&ctx, d)?;
        let disp = self.live[idx].dispute.as_mut().ok_or_else(|| anyhow!("dispute without a claim"))?;
        disp.stage = Stage::WaitP(1);
        disp.outpoint = OutPoint { txid: tx.compute_txid(), vout: 0 };
        disp.prevout = tx.output[0].clone();
        disp.tree = trees[0].clone();
        disp.trees = trees;
        disp.confirmed_at = height;
        disp.responded = false;
        let op = disp.outpoint;
        self.channel.mark_swept(l.outpoint);
        self.channel.watch(op);
        self.say(format!("contract {}: dispute opened at depth {d}; waiting for the prover's round 1", l.id));
        self.dispute_act(idx)
    }

    fn on_dispute_output_spent(&mut self, idx: usize, tx: Transaction, height: u32) -> Result<()> {
        let l = self.live[idx].clone();
        let inst = self.instance(&l);
        let disp = l.dispute.clone().expect("dispute");
        let leaf = disp.tree.identify_leaf(&tx.input[0].witness).map(|x| x.name.clone()).unwrap_or_default();
        let id = l.id;
        let ckeys = inst.claim_keys(disp.depth).expect("claim keys").clone();
        let ck = inst.challenger_keys(disp.depth).expect("challenger keys").clone();
        let rounds = disp.spec.rounds();
        let next_stage;
        match leaf.as_str() {
            n if n.starts_with("p_round_") => {
                let r: u32 = n[8..].parse()?;
                let commits = parse_p_round(&tx, &ckeys, &disp.spec, &disp.path, r)?;
                let dd = self.live[idx].dispute.as_mut().unwrap();
                for (i, st, sig) in commits {
                    dd.known.insert(i, (st, sig));
                }
                next_stage = Stage::WaitQ(r);
                self.say(format!("contract {id}: prover's round {r} commitments confirmed"));
            }
            n if n.starts_with("q_round_") => {
                let check = n.ends_with("_check");
                let r: u32 = n.trim_start_matches("q_round_").trim_end_matches("_check").parse()?;
                let j = parse_q_round(&tx, &ck, r)?;
                let dd = self.live[idx].dispute.as_mut().unwrap();
                dd.path.push(j);
                let (lo, len) = disp.spec.segment(&dd.path);
                next_stage = if r < rounds {
                    Stage::WaitP(r + 1)
                } else if !disp.spec.inner {
                    Stage::Terminal
                } else if check {
                    Stage::CheckReCur
                } else {
                    Stage::ReCur
                };
                self.say(format!("contract {id}: challenger picked segment {j} in round {r}: steps {lo}..{}", lo + len));
                if r == rounds {
                    let dd = self.live[idx].dispute.as_ref().unwrap();
                    let step = dd.isolated();
                    self.say(format!("contract {id}: isolated step {lo} is {}", step.name()));
                }
            }
            n @ ("p_re_cur" | "c_re_cur") => {
                let (cur, blocks) = dispute::parse_re_cur(&tx, &ckeys, n == "p_re_cur")?;
                let dd = self.live[idx].dispute.as_mut().unwrap();
                dd.re_cur = Some(cur);
                for (j, b) in blocks.into_iter().enumerate() {
                    dd.blocks.insert(j, b);
                }
                next_stage = if n == "p_re_cur" { Stage::ReNext } else { Stage::CheckReNext };
                self.say(format!("contract {id}: prover re-committed the step's input state{}", if n == "p_re_cur" { " and block words" } else { "" }));
            }
            n @ ("p_re_next" | "c_re_next") => {
                let next = dispute::parse_re_next(&tx, &ckeys)?;
                let dd = self.live[idx].dispute.as_mut().unwrap();
                dd.re_next = Some(next);
                next_stage = if n == "p_re_next" { Stage::WaitSched } else { Stage::CheckTerminal };
                self.say(format!("contract {id}: prover re-committed the step's output state"));
                if n == "p_re_next" {
                    // both parties now know the committed init and block: compute the inner chain
                    let cheat = if disp.prover == self.role { self.faults.cheat_inner.clone() } else { None };
                    self.live[idx].dispute.as_mut().unwrap().compute_inner(cheat.as_ref().map(|c| c.as_ref() as &dyn Fn(u32, &[u32; 8]) -> [u32; 8]))?;
                }
            }
            "p_sched" => {
                let words = parse_p_sched(&tx, &ckeys)?;
                let dd = self.live[idx].dispute.as_mut().unwrap();
                for (i, w, sig) in words {
                    dd.sched.insert(i, (w, sig));
                }
                next_stage = Stage::WaitInnerP(1);
                self.say(format!("contract {id}: prover's 48 schedule words confirmed"));
            }
            n if n.starts_with("p_inner_") => {
                let r: u32 = n[8..].parse()?;
                let commits = parse_p_inner(&tx, &ckeys, &disp.inner_path, r, disp.spec.inner_search())?;
                let dd = self.live[idx].dispute.as_mut().unwrap();
                let points: Vec<u32> = commits.iter().map(|c| c.0).collect();
                for (i, st, sig) in commits {
                    dd.inner_known.insert(i, (st, sig));
                }
                next_stage = Stage::WaitInnerQ(r);
                self.say(format!("contract {id}: prover's inner round {r} states confirmed (after rounds {points:?})"));
            }
            n if n.starts_with("q_inner_") => {
                let r: u32 = n[8..].parse()?;
                let j = parse_q_inner(&tx, &ck, r)?;
                let dd = self.live[idx].dispute.as_mut().unwrap();
                dd.inner_path.push(j);
                let inner_search = dd.spec.inner_search();
                let (lo, len) = inner_search.segment(&dd.inner_path);
                next_stage = if r < inner_search.rounds() { Stage::WaitInnerP(r + 1) } else { Stage::RoundTerminal };
                self.say(format!("contract {id}: challenger picked segment {j} in inner round {r}: rounds {lo}..{}", lo + len));
            }
            "timeout" => {
                self.live[idx].dispute.as_mut().unwrap().stage = Stage::Resolved;
                self.live[idx].resolved = true;
                self.say(format!("contract {id}: dispute resolved by timeout ({})", tx.compute_txid()));
                return Ok(());
            }
            n if n.starts_with("step_") || n.starts_with("sched_") || n.starts_with("round_") || n.starts_with("block_") || n.starts_with("re_") || n.starts_with("simple_") || n == "compress_copy" => {
                self.live[idx].dispute.as_mut().unwrap().stage = Stage::Resolved;
                self.live[idx].resolved = true;
                self.say(format!("contract {id}: disproved by {n} ({})", tx.compute_txid()));
                return Ok(());
            }
            other => {
                self.say(format!("contract {id}: dispute output spent by unknown leaf {other:?}"));
                return Ok(());
            }
        }
        let dd = self.live[idx].dispute.as_mut().unwrap();
        dd.stage = next_stage;
        dd.outpoint = OutPoint { txid: tx.compute_txid(), vout: 0 };
        dd.prevout = tx.output[0].clone();
        dd.tree = dd.trees[dd.tree_index()].clone();
        dd.confirmed_at = height;
        dd.responded = false;
        let op = dd.outpoint;
        self.channel.watch(op);
        self.dispute_act(idx)
    }

    /// Respond if it is my turn in the dispute (no timelock on responses).
    fn dispute_act(&mut self, idx: usize) -> Result<()> {
        let l = self.live[idx].clone();
        let Some(disp) = l.dispute.clone() else { return Ok(()) };
        if disp.responded || disp.waiting_for() != Some(self.role) || self.channel.is_swept(&disp.outpoint) {
            return Ok(());
        }
        if self.faults.silent_in_rounds {
            self.say(format!("contract {}: FAULT: staying silent in the dispute", l.id));
            return Ok(());
        }
        if self.faults.silent_in_inner && !matches!(disp.stage, Stage::WaitP(_) | Stage::WaitQ(_)) {
            self.say(format!("contract {}: FAULT: staying silent after the level-1 rounds", l.id));
            return Ok(());
        }
        let inst = self.instance(&l);
        let id = l.id;
        let ks = inst.keys_seq;
        let d = disp.depth;
        let keys = inst.claim_keys(d).expect("keys").clone();
        let ctx = self.channel.commit_ctx(l.seq, l.version)?;
        let words = lngap_contract::claim::words_bytes;
        match disp.stage {
            Stage::WaitP(r) => {
                // my round r: commit the k-1 states of the current segment
                let points = disp.spec.round_points(&disp.path);
                let mut sigs = Vec::new();
                for (t, i) in points.iter().enumerate() {
                    let mut st = disp.my_states[*i as usize].clone();
                    if let Some(cheat) = &self.faults.cheat_midstates {
                        st = cheat(*i, &st);
                    }
                    let label = lngap_contract::claim::round_label(id, ks, d, r, t as u32);
                    sigs.push(self.keystore.sign_wots(&label, &words(&st))?);
                }
                self.say(format!("contract {id}: answering dispute round {r} with states at steps {points:?}"));
                let extra = lngap_contract::claim::p_round_witness(&sigs);
                self.live[idx].dispute.as_mut().unwrap().responded = true;
                self.broadcast_dispute_tx(&l, &disp, &format!("p_round_{r}"), &extra)
            }
            Stage::WaitQ(r) => {
                let j = disp.choose_index();
                let label = lngap_contract::claim::index_label(id, ks, d, r);
                let reveal = self.keystore.reveal_uint(&label, j)?;
                self.say(format!("contract {id}: round {r}: first bad segment is {j}"));
                self.live[idx].dispute.as_mut().unwrap().responded = true;
                let mut leaf = format!("q_round_{r}");
                if r == disp.spec.rounds() && disp.spec.inner {
                    let mut path = disp.path.clone();
                    path.push(j);
                    let (_, _, step) = lngap_contract::claim::step_sources(&disp.spec, &path);
                    if matches!(disp.spec.steps[step as usize], lngap_contract::claim::Step::Simple { .. }) {
                        leaf.push_str("_check");
                    }
                }
                self.broadcast_dispute_tx(&l, &disp, &leaf, &lngap_contract::claim::q_round_witness(&reveal))
            }
            Stage::Terminal => {
                // flat: recompute the isolated compression natively; if it really is wrong, disprove it
                let (_, _, step) = disp.isolated_step();
                let cur = disp.state_at(step).ok_or_else(|| anyhow!("no state for step {step}"))?;
                let claimed_next = disp.state_at(step + 1).ok_or_else(|| anyhow!("no state for step {}", step + 1))?;
                let (expect, _) = disp.spec.apply(step as usize, &disp.spec.steps[step as usize], &cur, &[]);
                if expect == claimed_next {
                    self.say(format!("contract {id}: isolated step {step} is correct; nothing to disprove (the prover will time me out)"));
                    self.live[idx].dispute.as_mut().unwrap().responded = true;
                    return Ok(());
                }
                let args = terminal_witness(&disp)?;
                let (leaf_name, _) = lngap_contract::flat::terminal_leaf(&ctx, disp.prover, &keys, &disp.spec, &disp.path);
                self.say(format!("contract {id}: step {step} is wrong"));
                self.broadcast_disproof(idx, &disp, &leaf_name, args)
            }
            Stage::ReCur | Stage::CheckReCur => {
                let (cur_src, _, step) = disp.isolated_step();
                let mut cur = disp.source_value(&cur_src).ok_or_else(|| anyhow!("no committed state {step}"))?;
                if let Some(cheat) = &self.faults.cheat_recommit {
                    cur = cheat(false, &cur);
                    self.say(format!("contract {id}: CHEATING: re-committing a different input state"));
                }
                let sig = self.keystore.sign_wots(&lngap_contract::inner::re_cur_label(id, ks, d), &words(&cur))?;
                let mut extra = sig.consumption_order();
                let leaf = if disp.stage == Stage::ReCur {
                    let (_, block) = lngap_contract::claim::ClaimSpec::compress_inputs(disp.isolated(), &cur, disp.spec.data_for(&disp.data, step as usize), disp.spec.hash);
                    let mut bsigs = Vec::new();
                    for j in 0..disp.spec.hash.block_words() {
                        let w = u32::from_be_bytes(block[4 * j..4 * j + 4].try_into().unwrap());
                        bsigs.push(self.keystore.sign_wots(&lngap_contract::inner::block_label(id, ks, d, j as u32), &w.to_be_bytes())?);
                    }
                    extra = lngap_contract::inner::p_re_cur_witness(&sig, &bsigs);
                    "p_re_cur"
                } else {
                    "c_re_cur"
                };
                self.say(format!("contract {id}: re-committing the input state of step {step}"));
                self.live[idx].dispute.as_mut().unwrap().responded = true;
                self.broadcast_dispute_tx(&l, &disp, leaf, &extra)
            }
            Stage::ReNext | Stage::CheckReNext => {
                let (_, next_src, step) = disp.isolated_step();
                let mut next = disp.source_value(&next_src).ok_or_else(|| anyhow!("no committed state {}", step + 1))?;
                if let Some(cheat) = &self.faults.cheat_recommit {
                    next = cheat(true, &next);
                }
                let sig = self.keystore.sign_wots(&lngap_contract::inner::re_next_label(id, ks, d), &words(&next))?;
                let leaf = if disp.stage == Stage::ReNext { "p_re_next" } else { "c_re_next" };
                self.say(format!("contract {id}: re-committing the output state of step {step}"));
                self.live[idx].dispute.as_mut().unwrap().responded = true;
                self.broadcast_dispute_tx(&l, &disp, leaf, &sig.consumption_order())
            }
            Stage::WaitSched => {
                if !disp.spec.has_schedule() {
                    // No schedule stage for n4bit; skip directly to inner rounds
                    // This should not be reached for n4bit, but handle gracefully
                    self.live[idx].dispute.as_mut().unwrap().stage = Stage::WaitInnerP(1);
                    return self.dispute_act(idx);
                }
                let mine = disp.my_sched.as_ref().expect("inner computation");
                let mut sigs = Vec::new();
                 let bw = disp.spec.hash.block_words() as u32;
                 for i in bw..disp.spec.inner_rounds() {
                    let mut w = mine[i as usize];
                    if let Some(cheat) = &self.faults.cheat_schedule {
                        w = cheat(i, w);
                    }
                    sigs.push(self.keystore.sign_wots(&lngap_contract::inner::sched_label(id, ks, d, i), &w.to_be_bytes())?);
                }
                self.say(format!("contract {id}: publishing the 48 schedule words of step {}", disp.isolated_step().2));
                let extra = lngap_contract::inner::p_sched_witness(&sigs);
                self.live[idx].dispute.as_mut().unwrap().responded = true;
                self.broadcast_dispute_tx(&l, &disp, "p_sched", &extra)
            }
            Stage::WaitInnerP(r) => {
                let mine = disp.my_inner.as_ref().expect("inner computation");
                 let points = disp.spec.inner_search().round_points(&disp.inner_path);
                let mut sigs = Vec::new();
                for (t, i) in points.iter().enumerate() {
                    let label = lngap_contract::inner::inner_state_label(id, ks, d, r, t as u32);
                    sigs.push(self.keystore.sign_wots(&label, &lngap_contract::script_hash::state_bytes(&mine[*i as usize]))?);
                }
                self.say(format!("contract {id}: answering inner round {r} with states after rounds {points:?}"));
                let extra = lngap_contract::claim::p_round_witness(&sigs);
                self.live[idx].dispute.as_mut().unwrap().responded = true;
                self.broadcast_dispute_tx(&l, &disp, &format!("p_inner_{r}"), &extra)
            }
            Stage::WaitInnerQ(r) => {
                if r == 1 {
                    if let Some((leaf_name, args)) = disp.recommit_mismatch(&ctx, &keys) {
                        self.say(format!("contract {id}: the prover's re-commitment does not match its earlier commitment"));
                        return self.broadcast_disproof(idx, &disp, &leaf_name, args);
                    }
                    if let Some(j) = disp.first_bad_block() {
                        let (leaf_name, args) = disp.block_disproof(&ctx, &keys, j)?;
                        self.say(format!("contract {id}: block word {j} is wrong"));
                        return self.broadcast_disproof(idx, &disp, &leaf_name, args);
                    }
                    if disp.ckeep_violated() {
                        let (leaf_name, _) = lngap_contract::inner::ckeep_leaf(&ctx, disp.prover, &keys, &disp.spec, disp.isolated());
                        self.say(format!("contract {id}: the compression changed a register it should not have"));
                        return self.broadcast_disproof(idx, &disp, &leaf_name, disp.re_pair_args()?);
                    }
                    if disp.cpred_violated() {
                        let (leaf_name, _) = lngap_contract::inner::cpred_leaf(&ctx, disp.prover, &keys, &disp.spec, disp.isolated());
                        self.say(format!("contract {id}: a predicate of step {} ({}) fails", disp.isolated_step().2, disp.isolated().name()));
                        return self.broadcast_disproof(idx, &disp, &leaf_name, disp.state_and_block_args(false)?);
                    }
                    if disp.ccopy_violated() {
                        let (leaf_name, _) = lngap_contract::inner::ccopy_leaf(&ctx, disp.prover, &keys, &disp.spec, disp.isolated());
                        self.say(format!("contract {id}: step {} copied the wrong block words", disp.isolated_step().2));
                        return self.broadcast_disproof(idx, &disp, &leaf_name, disp.state_and_block_args(true)?);
                    }
                    if let Some(i) = disp.first_bad_sched() {
                        let (leaf_name, args) = disp.sched_disproof(&ctx, &keys, i)?;
                        self.say(format!("contract {id}: schedule word {i} is wrong"));
                        return self.broadcast_disproof(idx, &disp, &leaf_name, args);
                    }
                }
                let j = disp.choose_inner_index();
                let label = lngap_contract::inner::inner_index_label(id, ks, d, r);
                let reveal = self.keystore.reveal_uint(&label, j)?;
                self.say(format!("contract {id}: inner round {r}: first bad segment is {j}"));
                self.live[idx].dispute.as_mut().unwrap().responded = true;
                self.broadcast_dispute_tx(&l, &disp, &format!("q_inner_{r}"), &lngap_contract::claim::q_round_witness(&reveal))
            }
            Stage::RoundTerminal => {
                let (lo, len) = disp.spec.inner_search().segment(&disp.inner_path);
                debug_assert_eq!(len, 1);
                let r = lo;
                let (expect, claimed) = disp.check_round(r)?;
                if expect == claimed {
                    self.say(format!("contract {id}: isolated round {r} is correct; nothing to disprove (the prover will time me out)"));
                    self.live[idx].dispute.as_mut().unwrap().responded = true;
                    return Ok(());
                }
                let (leaf_name, args) = disp.round_disproof(&ctx, &keys, r)?;
                self.say(format!("contract {id}: round {r} is wrong"));
                self.broadcast_disproof(idx, &disp, &leaf_name, args)
            }
            Stage::CheckTerminal => {
                if let Some((leaf_name, args)) = disp.recommit_mismatch(&ctx, &keys) {
                    self.say(format!("contract {id}: the prover's re-commitment does not match its earlier commitment"));
                    return self.broadcast_disproof(idx, &disp, &leaf_name, args);
                }
                let (_, _, step) = disp.isolated_step();
                let cur = &disp.re_cur.as_ref().ok_or_else(|| anyhow!("no re_cur"))?.0;
                let next = &disp.re_next.as_ref().ok_or_else(|| anyhow!("no re_next"))?.0;
                if disp.spec.step_ok(step as usize, disp.isolated(), cur, next, &[]) {
                    self.say(format!("contract {id}: isolated step {step} ({}) is correct; nothing to disprove (the prover will time me out)", disp.isolated().name()));
                    self.live[idx].dispute.as_mut().unwrap().responded = true;
                    return Ok(());
                }
                let (leaf_name, _) = lngap_contract::simple::simple_leaf(&ctx, disp.prover, &keys, disp.spec.n_words, disp.isolated());
                self.say(format!("contract {id}: step {step} ({}) is wrong", disp.isolated().name()));
                self.broadcast_disproof(idx, &disp, &leaf_name, disp.re_pair_args()?)
            }
            Stage::Resolved => Ok(()),
        }
    }

    /// The challenger's disproof transaction for `leaf_name`: pays by size
    /// (the node's min relay fee is 0.1 sat/vB on Core ≥ 30).
    fn broadcast_disproof(&mut self, idx: usize, disp: &DisputeLive, leaf_name: &str, args: Vec<Vec<u8>>) -> Result<()> {
        let leaf = disp.tree.leaf(leaf_name)?.clone();
        let build = |fee: Amount| -> Result<Transaction> {
            let mut tx = build_spend(disp.outpoint, &Timelock::NONE, vec![TxOut { value: disp.prevout.value - fee, script_pubkey: self.channel.my_payout_spk() }]);
            let sig = sign_tapscript(&self.channel.keys.payment, &tx, 0, std::slice::from_ref(&disp.prevout), &leaf.script)?;
            let mut w = WitnessStack::new();
            w.push(sig.as_ref().to_vec()).extend(args.clone());
            tx.input[0].witness = w.build(&leaf.script, &disp.tree.control_block(leaf_name)?);
            Ok(tx)
        };
        let probe = build(self.channel.params.presign_fee)?;
        let fee = Amount::from_sat((probe.vsize() as u64) / 10 + 100).max(self.channel.params.presign_fee);
        let tx = build(fee)?;
        self.say(format!("contract {}: broadcasting {leaf_name} ({} B witness, {} vB)", self.live[idx].id, tx.input[0].witness.size(), tx.vsize()));
        self.channel.mark_swept(disp.outpoint);
        self.live[idx].dispute.as_mut().unwrap().responded = true;
        self.channel.broadcast(&tx, leaf_name)?;
        Ok(())
    }

    fn broadcast_dispute_tx(&mut self, l: &Live, disp: &DisputeLive, label: &str, extra: &[Vec<u8>]) -> Result<()> {
        let key = GraphKey { version: l.version, contract_id: l.id, label: format!("d{}/{label}", disp.depth) };
        let rec = self.channel.record(l.seq).ok_or_else(|| anyhow!("no record"))?;
        let ptx = rec.graph.get(&key).ok_or_else(|| anyhow!("no graph tx {key}"))?;
        let tx = ptx.finalize(extra)?;
        self.channel.mark_swept(disp.outpoint);
        self.channel.broadcast(&tx, label)?;
        Ok(())
    }

    /// Time out a counterparty that has not responded within Δ.
    fn dispute_tick(&mut self, idx: usize) -> Result<()> {
        let l = self.live[idx].clone();
        let Some(disp) = l.dispute.clone() else { return Ok(()) };
        if disp.stage == Stage::Resolved || self.channel.is_swept(&disp.outpoint) {
            return Ok(());
        }
        // my own pending response first
        self.dispute_act(idx)?;
        let Some(who) = disp.waiting_for() else { return Ok(()) };
        if who == self.role {
            return Ok(());
        }
        let n = self.channel.params.delta;
        if self.height + 1 < disp.confirmed_at + u32::from(n) {
            return Ok(());
        }
        if self.channel.is_swept(&disp.outpoint) {
            return Ok(());
        }
        let input = SweepInput { outpoint: disp.outpoint, prevout: disp.prevout.clone(), tree: &disp.tree, leaf: "timeout", before_sig: vec![] };
        let tx = build_sweep(&[input], self.channel.my_payout_spk(), self.channel.params.presign_fee, &self.channel.keys.payment, bitcoin::absolute::LockTime::ZERO)?;
        self.say(format!("contract {}: {who} did not respond within Δ; sweeping the dispute output ({} sat)", l.id, tx.output[0].value));
        self.channel.mark_swept(disp.outpoint);
        self.channel.broadcast(&tx, "dispute_timeout")?;
        Ok(())
    }
}
