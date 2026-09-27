//! One side of the game: its keys, its view of the venue and the chain,
//! and a REPL that plays moves and disputes. Everything the counterparty
//! must supply arrives through the shared directory (its offer, its
//! graph signatures) or through the chain (its refutation's reveal).

use std::collections::{BTreeMap, HashMap};
use std::io::{BufRead, Write};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{anyhow, bail, ensure, Context, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut, Txid};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, PresignedTx, Role};
use lngap_chess::certificate::find_kind;
use lngap_chess::leaf::exhibit_values;
use lngap_chess::{apply, Move};
use lngap_chess_fc::{ChessEntry, ChessState};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_pos::chess;
use lngap_pos::graph::{not_timely_witness, proposer_witness};
use lngap_pos::instance::{self, Game, GameClock, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNKS, HEAD_CHUNK_START};
use lngap_pos::ttt::checked_split_witness;
use lngap_pos::{Registry, SealedBlock};

use crate::store::*;
use serde::Serialize;

/// An entry's authorship message (D43): the 40 state bytes, then the
/// move's two bytes (low first).
fn entry_msg(e: &ChessEntry) -> Vec<u8> {
    let mv = u32::from(e.state.mv.to_u16());
    let mut m = e.state.to_e().to_vec();
    m.extend_from_slice(&(mv as u16).to_le_bytes());
    m
}

fn scriptnum(v: i64) -> Vec<u8> {
    assert!((0..128).contains(&v));
    if v == 0 { vec![] } else { vec![v as u8] }
}

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

/// A confirmed graph transaction's output, by label.
#[derive(Clone, Debug)]
struct Live {
    height: u32,
    op: OutPoint,
    prev: TxOut,
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
    /// The counterparty's per-depth state keys (its offer), for the
    /// native check of a sealed entry.
    their_state_keys: HashMap<u32, WotsPublic>,
    graph: Vec<PresignedTx>,
    /// The Bitcoin height the contract output confirmed at.
    funded_height: u32,
    // ----- the venue as seen -----
    /// The seal a refutation would read, by depth: the first honest one,
    /// else the first seen (a late or rogue seal).
    blocks: BTreeMap<u32, SealedBlock>,
    /// Seal files already read (by path).
    seen_seals: std::collections::BTreeSet<String>,
    flags: BTreeMap<u32, Vec<Option<SecretKey>>>,
    /// My submission awaiting a seal: (depth, entry hex, member, sent at).
    pending: Option<(u32, String, usize, u32)>,
    /// The position after the last sealed LEGAL move, and its depth.
    state: ChessState,
    depth: u32,
    /// Depths whose seal is not a legal continuation (the disprove
    /// family's business), by depth: what was wrong.
    bad_slots: BTreeMap<u32, String>,
    /// Depths whose seal was made after the due time (the venue's
    /// misbehaviour control), or of an unsigned entry (a rogue member).
    late_slots: std::collections::BTreeSet<u32>,
    rogue_slots: std::collections::BTreeSet<u32>,
    // ----- the chain as seen -----
    scanned: u32,
    live: BTreeMap<String, Live>,
    spent: HashMap<OutPoint, (Txid, u32)>,
    /// The pair reveal parsed off a confirmed refutation, by its base
    /// label (`absent_d`, `absent_d/counter`).
    reveals: BTreeMap<String, WotsSig>,
    log: Vec<String>,
}

impl Player {
    pub fn role(&self) -> Role {
        self.me
    }

    pub fn publish_web_port(&self, port: u16) -> Result<()> {
        self.store.write(&Store::web(self.me), &serde_json::json!({ "port": port }))
    }

    fn say(&mut self, s: String) {
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

    /// When move `d` is due (unix seconds).
    fn due(&self, d: u32) -> u32 {
        self.inst.due(d)
    }

    /// Seconds relative to t0, for display.
    fn rel(&self, t: u32) -> i64 {
        i64::from(t) - i64::from(self.inst.t0)
    }

    /// Why a depth-`d` claim is not yet mineable, or `None` if it is: its
    /// median-time-past CLTV (`claim_from`, final once MTP passes it) and
    /// the broadcaster's `to_self_delay` on the contract output.
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

    /// The height from which a spend with a relative lock of `blocks`
    /// off the output of `label` is mineable (the output's block counts).
    fn window_open(&self, label: &str, blocks: u16) -> Result<u32> {
        let l = self.live.get(label).ok_or_else(|| anyhow!("`{label}` is not confirmed"))?;
        Ok(l.height + u32::from(blocks))
    }

    fn need_height(&self, at: u32, what: &str) -> Result<()> {
        let h = self.height();
        ensure!(h >= at, "not broadcast: {what} cannot be mined before height {at} ({} blocks to go) — try again from then", at - h);
        Ok(())
    }


    // ============ setup ============

    pub fn open(dir: PathBuf, me: Role, max_depth: u32) -> Result<Player> {
        let store = Store::new(dir);
        println!("{me}: waiting for the venue's node...");
        let node = wait_for(|| store.read::<NodeInfo>(Store::node()))?;
        let rt = Regtest::attach(&PathBuf::from(node.datadir))?;
        println!("{me}: waiting for the venue's registry...");
        let registry: Registry = wait_for(|| store.read(Store::registry()))?;
        println!("{me}: registry has {} members, threshold {}, depths 0..={}", registry.n(), registry.threshold, registry.max_depth());

        // my keys: the channel keys and the per-depth contract keys
        let label = format!("chess-venue/{}", me.name());
        let keys = PartyKeys::from_seed(me, Seed::from_label(&label));
        let mut ks = KeyStore::new(Seed::from_label(&format!("{label}-ks")));
        let mine = instance::gen_pos_keys(&mut ks, me, CONTRACT_ID, 1, max_depth, Game::Chess)?;
        store.write(&Store::offer(me), &Offer { pubs: keys.public(), keys: mine.clone() })?;
        println!("{me}: offer published; waiting for {}'s offer...", me.other());
        let theirs: Offer = wait_for(|| store.read(&Store::offer(me.other())))?;
        let their_state_keys = theirs.keys.iter().filter_map(|(d, o)| o.state.clone().map(|k| (*d, k))).collect();
        let merged = instance::collect_keys(&mine, &theirs.keys, max_depth)?;
        let mut pubs = [keys.public(), keys.public()];
        pubs[me.other().idx()] = theirs.pubs.clone();

        // the contract: the user proposes it (the venue funds it at the
        // height it announced), both build the same output
        let params = ChannelParams { presign_fee: Amount::from_sat(FEE_SAT), ..ChannelParams::regtest(Amount::from_sat(400_000)) };
        let vparams: VenueParams = wait_for(|| store.read(Store::params()))?;
        let funded: FundedJson = if me == Role::User {
            // the timetable (D55): move 0's time after the setup allowance;
            // settle long after the last claim
            let clock = GameClock { t0: unix_now() + vparams.start_secs, ell: vparams.ell, margin: vparams.margin };
            let deadline = clock.t0 + (max_depth + 1) * clock.ell + clock.margin + 7 * 24 * 3600;
            let probe = PosInstance::new(CONTRACT_ID, Amount::from_sat(POT_SAT), deadline, GAME_ID, Game::Chess, clock, merged.clone(), registry.clone())?;
            let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
            let tree = probe.tree(&ctx)?;
            store.write(Store::contract(), &ContractJson { spk: hex::encode(tree.script_pubkey().as_bytes()), value: POT_SAT, deadline, t0: clock.t0, ell: clock.ell, margin: clock.margin })?;
            println!("{me}: contract proposed ({} sat; move 1 due in {}s, a move every {}s); waiting for the venue to fund it...", POT_SAT, vparams.start_secs + vparams.ell, vparams.ell);
            wait_for(|| store.read(Store::funded()))?
        } else {
            println!("{me}: waiting for the user's contract and the venue's funding...");
            wait_for(|| store.read(Store::funded()))?
        };
        let contract: ContractJson = wait_for(|| store.read(Store::contract()))?;
        let clock = GameClock { t0: contract.t0, ell: contract.ell, margin: contract.margin };
        let inst = PosInstance::new(CONTRACT_ID, Amount::from_sat(POT_SAT), contract.deadline, GAME_ID, Game::Chess, clock, merged, registry.clone())?;
        let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
        let tree = inst.tree(&ctx)?;
        ensure!(hex::encode(tree.script_pubkey().as_bytes()) == funded.spk, "the funded output is not the contract we agreed");
        let op = OutPoint { txid: funded.txid.parse()?, vout: funded.vout };
        let prev = TxOut { value: Amount::from_sat(funded.value), script_pubkey: tree.script_pubkey() };
        print!("{me}: building and signing the pre-signed graph... ");
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
        println!("{me}: signatures published; waiting for {}'s...", me.other());
        let theirs: SigsJson = wait_for(|| store.read(&Store::sigs(me.other())))?;
        for p in graph.iter_mut() {
            let s = theirs.get(&p.label).ok_or_else(|| anyhow!("{} did not sign {}", me.other(), p.label))?;
            let sig = Signature::from_slice(&hex::decode(s)?)?;
            p.add_sig(me.other(), lngap_channel::GraphSig::Full(sig), &pubs).with_context(|| format!("{}'s signature on {}", me.other(), p.label))?;
        }
        store.write(&Store::ready(me), &serde_json::json!({ "ready": true }))?;
        let t1 = i64::from(contract.t0 + contract.ell) - i64::from(unix_now());
        println!("{me}: every skeleton is fully signed. The game is on: white ({}) moves first; move 1 is due in {t1}s.", Role::User);
        Ok(Player {
            me,
            store,
            rt,
            keys,
            ks,
            pubs,
            params,
            scanned: funded.height - 1,
            funded_height: funded.height,
            vparams,
            registry,
            inst,
            their_state_keys,
            graph,
            blocks: BTreeMap::new(),
            seen_seals: Default::default(),
            flags: BTreeMap::new(),
            pending: None,
            state: ChessState::initial(),
            depth: 0,
            bad_slots: BTreeMap::new(),
            late_slots: Default::default(),
            rogue_slots: Default::default(),
            live: BTreeMap::new(),
            spent: HashMap::new(),
            reveals: BTreeMap::new(),
            log: Vec::new(),
        })
    }

    // ============ the venue and the chain, as seen ============

    /// Read new venue seals and flags, resubmit an unsealed move after the
    /// backoff, scan new Bitcoin blocks; print what changed.
    pub fn sync(&mut self) -> Result<()> {
        // venue seals, in the order they were made (D55: keyed by depth)
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
        // flags
        for d in 1..=self.vparams.max_depth {
            if self.flags.contains_key(&d) {
                continue;
            }
            if let Some(f) = self.store.read::<FlagsJson>(&Store::flags(d))? {
                let f = flags_from_json(&f)?;
                let n = f.iter().filter(|x| x.is_some()).count();
                self.flags.insert(d, f);
                self.say(format!("venue: move {d} was due at t+{}s with no signed seal — {n} of {K} members flagged it", self.rel(self.due(d))));
            }
        }
        // my pending submission: sealed, or fall back along the rotation
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
        // the chain
        let h = self.height();
        while self.scanned < h {
            self.scanned += 1;
            let txs = self.rt.block_txs(self.scanned)?;
            for tx in txs.iter().skip(1) {
                self.on_tx(self.scanned, tx)?;
            }
        }
        Ok(())
    }

    /// A seal read off the venue: which depth, by whom, whether honest.
    /// The first seal of a depth is the one a refutation would read; a
    /// second, different head is the D55 equivocation (both signed: the
    /// mover's; an unsigned one: its rogue sealer's).
    fn on_seal(&mut self, b: &BlockJson, block: SealedBlock) -> Result<()> {
        let slot = b.depth;
        let by = block.proposer;
        let when = self.rel(b.sealed_at);
        if let Some(held) = self.blocks.get(&slot) {
            if held.head() == block.head() {
                self.say(format!("venue: move {slot} also sealed by member {by} (t+{when}s): the same head, the same attestation"));
            } else {
                self.say(format!("venue: move {slot}: a SECOND, different head sealed by member {by} (t+{when}s){} — an equivocation at depth {slot}", if b.rogue { ", unsigned (a rogue seal)" } else { "" }));
            }
            return Ok(());
        }
        if b.late {
            self.late_slots.insert(slot);
            self.say(format!("venue: move {slot} sealed LATE by member {by} at t+{when}s (due t+{}s): the members' flags stand; the mover may refute with it, the claimant kills the refutation with the flags", self.rel(self.due(slot))));
        }
        if b.rogue {
            self.rogue_slots.insert(slot);
        }
        self.blocks.insert(slot, block.clone());
        let block = &block;
        let mover = instance::mover_at(slot);
        let e = match ChessEntry::decode(&block.entry) {
            Ok(e) => e,
            Err(err) => {
                self.bad_slots.insert(slot, format!("undecodable entry ({err})"));
                self.say(format!("venue: move {slot} sealed by member {} with an UNDECODABLE entry", block.proposer));
                return Ok(());
            }
        };
        let signed = match self.their_state_keys.get(&slot).or_else(|| None) {
            Some(k) if mover != self.me => refute::check_entry_sig(k, &entry_msg(&e), &e.sigs),
            _ if mover == self.me => self.ks.wots_public(&instance::state_label(CONTRACT_ID, 1, slot)).map(|k| refute::check_entry_sig(&k, &entry_msg(&e), &e.sigs)).unwrap_or(false),
            _ => false,
        };
        if u32::from(e.depth) != slot || e.mover != mover.idx() as u8 || e.game_id != GAME_ID {
            self.bad_slots.insert(slot, "wrong slot / mover / game in the entry".into());
            self.say(format!("venue: move {slot} sealed by member {} with an entry for the WRONG depth or mover (wrong_slot)", block.proposer));
            return Ok(());
        }
        if !signed {
            self.bad_slots.insert(slot, "garbage signature".into());
            self.say(format!("venue: move {slot} sealed by member {} (a ROGUE seal: honest members refused it) with {mover}'s move {} — the signature opens no key (not a move)", block.proposer, e.state.mv));
            return Ok(());
        }
        // a legal continuation of the position?
        if slot != self.depth + 1 {
            self.bad_slots.insert(slot, format!("the game was at depth {}", self.depth));
            self.say(format!("venue: move {slot} sealed {mover}'s move {} but the game is at depth {} — out of sequence", e.state.mv, self.depth));
            return Ok(());
        }
        match apply(&self.state.pos, e.state.mv) {
            Ok(mut pos) => {
                pos.fullmove = 0;
                if pos != e.state.pos {
                    self.bad_slots.insert(slot, "the claimed position is not the move's result".into());
                    self.say(format!("venue: move {slot} sealed {mover}'s move {} with a position that is NOT its result — disprovable", e.state.mv));
                    return Ok(());
                }
                self.state = e.state.clone();
                self.depth = slot;
                let term = lngap_chess::terminal(&self.state.pos).map(|t| format!(" — {t:?}")).unwrap_or_default();
                self.say(format!("venue: move {slot} sealed by member {} at t+{when}s: {mover} played {} (signed, legal){term}", block.proposer, e.state.mv));
            }
            Err(v) => {
                self.bad_slots.insert(slot, format!("{v}"));
                self.say(format!("venue: move {slot} sealed {mover}'s move {} — ILLEGAL ({v}); the absence claim and the disprove family apply", e.state.mv));
            }
        }
        Ok(())
    }

    fn on_tx(&mut self, height: u32, tx: &Transaction) -> Result<()> {
        let txid = tx.compute_txid();
        // a graph transaction confirming
        if let Some(p) = self.graph.iter().find(|p| p.txid() == txid) {
            let label = p.label.clone();
            let live = Live { height, op: OutPoint { txid, vout: 0 }, prev: tx.output[0].clone() };
            let by = if label.ends_with("/refute") || label.ends_with("/counter") { "the mover" } else { "the claimant" };
            self.say(format!("chain: height {height}: `{label}` confirmed ({} vB, by {by})", tx.vsize()));
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
        // spends of live outputs
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

    /// The mover's WOTS reveal, read off the confirmed refutation's
    /// witness: the last three witness arguments are the mover's payment
    /// signature, the proposer index and the proposer signature; below
    /// them ride the `2 × digits` elements of the reveal.
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

    /// The message the depth-`d` refute key signs: `head(d-1) || head(d)`
    /// (the single head at depth 1), from the venue's blocks.
    fn parked_message(&self, d: u32) -> Result<Vec<u8>> {
        let head = |s: u32| -> Result<[u8; 48]> { Ok(self.blocks.get(&s).ok_or_else(|| anyhow!("no venue seal at depth {s}"))?.header.head()) };
        let mut m = Vec::new();
        if d >= 2 {
            m.extend_from_slice(&head(d - 1)?);
        }
        m.extend_from_slice(&head(d)?);
        Ok(m)
    }

    // ============ what can be done now ============

    /// The live, unspent claim-shaped outputs: (base label, depth).
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

    /// The live, unspent refuted outputs: (base label, depth).
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

    fn status(&mut self) -> Result<String> {
        let mut out = String::new();
        let h = self.height();
        let now = self.rel(unix_now());
        let next = self.depth + 1;
        out += &format!("--- {} | t+{now}s | height {h}, MTP t+{}s | game depth {} | side to move: {} ({}), move {next} due t+{}s | venue {} members, threshold {}\n", self.me, self.rel(self.rt.mtp().unwrap_or(0)), self.depth, if self.state.pos.side == lngap_chess::Colour::White { "white" } else { "black" }, instance::mover_at(next), self.rel(self.due(next)), self.registry.n(), self.registry.threshold);
        out += &format!("{}\n", self.state.pos);
        if let Some(t) = lngap_chess::terminal(&self.state.pos) {
            out += &format!("    terminal: {t:?}\n");
        }
        for l in self.mempool_labels() {
            out += &format!("    in the mempool, confirms at the next block: `{l}`\n");
        }
        for (s, why) in &self.bad_slots {
            out += &format!("    move {s}: not a legal move ({why})\n");
        }
        for (s, f) in &self.flags {
            out += &format!("    move {s}: flagged (no signed seal by its due time) by {} of {K}\n", f.iter().filter(|x| x.is_some()).count());
        }
        for a in self.actions() {
            if a.enabled {
                out += &format!("    you may `{}`{}\n", a.name, if a.hint.is_empty() { String::new() } else { format!(": {}", a.hint) });
            } else if !a.hint.is_empty() {
                out += &format!("    `{}`: {}\n", a.name, a.hint);
            }
        }
        Ok(out.trim_end().to_string())
    }

    // ============ what can be done now, as data ============

    /// The actions and whether each is available now, with a reason.
    fn actions(&self) -> Vec<ActionView> {
        let h = self.height();
        let now = unix_now();
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let terminal = lngap_chess::terminal(&self.state.pos).is_some();
        let delta = self.params.delta;
        let delta2 = self.params.delta + self.params.delta_prime;
        let mut v = Vec::new();
        // move: before its due time; the effective deadline leaves room for
        // one fallback (D55)
        let due = self.due(d);
        v.push(if terminal {
            ActionView::no("move", "the game is over")
        } else if mover != self.me {
            ActionView::no("move", &format!("{mover} to move (move {d}, due t+{}s)", self.rel(due)))
        } else if now > due {
            ActionView::no("move", &format!("your move {d} was due at t+{}s: you are stalled", self.rel(due)))
        } else if let Some((pd, _, to, at)) = self.pending.as_ref().filter(|p| p.0 == d) {
            ActionView::no("move", &format!("your move {pd} is with member {to} (sent t+{}s); fallback to the next member after {}s", self.rel(*at), self.vparams.backoff))
        } else {
            let left = i64::from(due) - i64::from(now);
            let safe = left - i64::from(self.vparams.backoff) * 2;
            ActionView::ok("move", &format!("move {d} is due in {left}s (t+{}s); submit within {}s to leave room for a fallback", self.rel(due), safe.max(0)))
        });
        // claim: the earliest move of the opponent's whose due time passed
        // with no TIMELY signed seal — none, not a move, or only a late or
        // rogue seal (the members' flags stand) — and is not yet claimed
        let claimable = (1..=d)
            .filter(|s| instance::mover_at(*s) != self.me && self.due(*s) < now)
            .find(|s| {
                let untimely = self.blocks.get(s).map(|_| self.bad_slots.contains_key(s) || self.late_slots.contains(s) || self.rogue_slots.contains(s)).unwrap_or(true);
                let claimed = self.live.contains_key(&format!("absent_{s}")) || self.mempool_labels().contains(&format!("absent_{s}"));
                untimely && !claimed
            });
        v.push(match claimable {
            None if mover == self.me => ActionView::no("claim", &format!("move {d} is your own")),
            None if self.due(d) >= now => ActionView::no("claim", &format!("{mover}'s move {d} is due at t+{}s", self.rel(self.due(d)))),
            None => ActionView::no("claim", "nothing to claim: every move of the opponent's is timely and signed, or claimed"),
            Some(s) => {
                let who = instance::mover_at(s);
                let why = if self.late_slots.contains(&s) { format!("move {s} was sealed only LATE; the flags stand") } else if self.bad_slots.contains_key(&s) { format!("move {s} holds no valid move") } else { format!("{who} did not publish move {s} by t+{}s", self.rel(self.due(s))) };
                match self.claim_wait(s) {
                    Some(wait) => ActionView::no("claim", &format!("{why}: not yet — {wait}")).with_cmd(&format!("claim {s}")),
                    None => ActionView::ok("claim", &why).with_cmd(&format!("claim {s}")),
                }
            }
        });
        // counter / refute: a live claim against me
        let against_me: Vec<(String, u32)> = self.live_claims().into_iter().filter(|(_, dd)| instance::mover_at(*dd) == self.me).collect();
        match against_me.first() {
            Some((base, dd)) => {
                let can_counter = !base.contains("counter") && *dd >= 2;
                v.push(if can_counter { ActionView::ok("counter", &format!("`{base}`: the claim was not due (you say the claimant did not move at {})", dd - 1)) } else { ActionView::no("counter", "no counter on a counter, nor at depth 1") });
                let has_block = self.blocks.get(dd).is_some_and(|b| !b.entry.is_empty());
                v.push(if has_block { ActionView::ok("refute", &format!("`{base}` (depth {dd}): the venue attested your move {dd}; the claimant's timeout opens at height {}", self.window_open(base, delta).unwrap_or(0))) } else { ActionView::no("refute", &format!("`{base}` (depth {dd}): nothing is sealed for move {dd} — nothing to refute with")) });
            }
            None => {
                v.push(ActionView::no("counter", "no live claim against you"));
                v.push(ActionView::no("refute", "no live claim against you"));
            }
        }
        // disprove / timely: a live refutation against me
        let refuted_against_me: Vec<(String, u32)> = self.live_refuted().into_iter().filter(|(_, dd)| instance::mover_at(*dd) != self.me).collect();
        match refuted_against_me.first() {
            Some((base, dd)) => {
                let open = self.window_open(&format!("{base}/refute"), delta).unwrap_or(0);
                let firing = self.firing(*dd);
                let flags = self.flags.get(dd).map(|f| f.iter().filter(|x| x.is_some()).count()).unwrap_or(0);
                if h < open {
                    v.push(ActionView::no("disprove", &format!("`{base}` (depth {dd}): the window opens at height {open} ({} blocks to go); fires: {}", open - h, if firing.is_empty() { "nothing".into() } else { firing.join(", ") })));
                    v.push(ActionView::no("timely", &format!("the window opens at height {open}; {flags} of {K} flags known")));
                } else {
                    v.push(if firing.is_empty() { ActionView::no("disprove", &format!("`{base}` (depth {dd}): the parked move is legal, nothing fires")) } else { ActionView::ok("disprove", &format!("`{base}` (depth {dd}): {}", firing.join(", "))) });
                    v.push(if flags >= self.registry.threshold as usize { ActionView::ok("timely", &format!("{flags} of {K} members flagged move {dd}: no signed seal by its due time")) } else { ActionView::no("timely", &format!("{flags} of {K} flags known for move {dd} (threshold {})", self.registry.threshold)) });
                }
            }
            None => {
                v.push(ActionView::no("disprove", "no live refutation against you"));
                v.push(ActionView::no("timely", "no live refutation against you"));
            }
        }
        // split: mine
        let mut split = ActionView::no("split", "nothing of yours to split");
        if let Some((base, _dd)) = self.live_refuted().into_iter().find(|(_, dd)| instance::mover_at(*dd) == self.me) {
            let open = self.window_open(&format!("{base}/refute"), delta2).unwrap_or(0);
            split = if h >= open { ActionView::ok("split", &format!("your refutation on `{base}` stands: the self-checking split")) } else { ActionView::no("split", &format!("your refutation on `{base}` stands: the split opens at height {open} ({} blocks to go)", open - h)) };
        } else if let Some((base, _dd)) = self.live_claims().into_iter().find(|(_, dd)| instance::mover_at(*dd) != self.me) {
            let open = self.window_open(&base, delta).unwrap_or(0);
            split = if h >= open { ActionView::ok("split", &format!("your claim `{base}` is unanswered: the timeout split")) } else { ActionView::no("split", &format!("your claim `{base}`: the timeout opens at height {open} ({} blocks to go) unless it is refuted or countered", open - h)) };
        }
        v.push(split);
        v
    }

    /// Everything the page shows.
    pub fn snapshot(&mut self) -> Snapshot {
        let h = self.height();
        let d = self.depth;
        let slots: Vec<SlotView> = self
            .blocks
            .iter()
            .map(|(s, b)| {
                let entry = if let Some(why) = self.bad_slots.get(s) {
                    format!("{}: {} — NOT a move ({why})", instance::mover_at(*s), ChessEntry::decode(&b.entry).map(|e| e.state.mv.to_string()).unwrap_or_else(|_| "?".into()))
                } else {
                    format!("{}: {}", instance::mover_at(*s), ChessEntry::decode(&b.entry).map(|e| e.state.mv.to_string()).unwrap_or_else(|_| "?".into()))
                };
                SlotView { slot: *s, due: self.rel(self.due(*s)), proposer: b.proposer, entry, ok: !self.bad_slots.contains_key(s) && !self.late_slots.contains(s), flags: self.flags.get(s).map(|f| f.iter().filter(|x| x.is_some()).count()), late: self.late_slots.contains(s) }
            })
            .collect();
        // the flagged depths with no seal at all (a stall) show as rows too
        let mut slots = slots;
        for (s, f) in &self.flags {
            if !self.blocks.contains_key(s) {
                slots.push(SlotView { slot: *s, due: self.rel(self.due(*s)), proposer: usize::MAX, entry: "nothing sealed".into(), ok: false, flags: Some(f.iter().filter(|x| x.is_some()).count()), late: false });
            }
        }
        slots.sort_by_key(|v| v.slot);
        let live: Vec<LiveView> = self
            .live
            .iter()
            .map(|(label, l)| LiveView { label: label.clone(), height: l.height, spent: self.spent.contains_key(&l.op), value_sat: l.prev.value.to_sat() })
            .collect();
        let disproves: Vec<DisproveView> = self.live_refuted().into_iter().find(|(_, dd)| instance::mover_at(*dd) != self.me).map(|(_, dd)| self.list_disproves(dd).into_iter().map(|(name, fires)| DisproveView { name, fires }).collect()).unwrap_or_default();
        let last_move = (d >= 1).then(|| self.state.mv.to_string());
        let balance_sat = self.rt.balance_of(&self.pubs[self.me.idx()].payout_spk).map(|a| a.to_sat()).unwrap_or(0);
        Snapshot {
            role: self.me.name().into(),
            height: h,
            mtp: self.rel(self.rt.mtp().unwrap_or(0)),
            now: self.rel(unix_now()),
            ell: self.inst.ell,
            backoff: self.vparams.backoff,
            margin: self.inst.margin,
            next_due: self.rel(self.due(d + 1)),
            block_secs: self.vparams.block_secs,
            depth: d,
            fen: self.state.pos.to_fen(),
            to_move: instance::mover_at(d + 1).name().into(),
            terminal: lngap_chess::terminal(&self.state.pos).map(|t| format!("{t:?}")),
            last_move,
            n: self.registry.n(),
            threshold: self.registry.threshold,
            slots,
            live,
            actions: self.actions(),
            disproves,
            mempool: self.mempool_labels(),
            balance_sat,
            log: self.log.iter().rev().take(60).rev().cloned().collect(),
        }
    }

    /// Legal destination squares from `from` in the current position (for
    /// click-to-move).
    pub fn legal_from(&self, from: &str) -> Vec<String> {
        lngap_chess::legal_moves(&self.state.pos).into_iter().map(|m| m.to_string()).filter(|u| u.starts_with(from)).map(|u| u[2..4].to_string()).collect()
    }

    fn firing(&self, d: u32) -> Vec<String> {
        let (Some(new), prior) = (self.blocks.get(&d), if d >= 2 { self.blocks.get(&(d - 1)) } else { None }) else { return vec![] };
        if d >= 2 && prior.is_none() {
            return vec![];
        }
        let l = self.inst.layout(d);
        let prior_head = prior.map(|b| b.header.head()).unwrap_or([0u8; 48]);
        chess::disprove_leaves(&l, &self.inst.depth_keys(d).refute).into_iter().filter(|pl| (pl.fires)(&prior_head, &new.header.head())).map(|pl| pl.name).collect()
    }

    // ============ actions ============

    fn play_move(&mut self, uci: &str) -> Result<()> {
        let d = self.depth + 1;
        ensure!(instance::mover_at(d) == self.me, "it is {}'s move (depth {d})", instance::mover_at(d));
        ensure!(unix_now() <= self.due(d), "your move {d} was due at t+{}s: you are stalled", self.rel(self.due(d)));
        let mv = Move::parse(uci).ok_or_else(|| anyhow!("not a UCI move: {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow!("illegal: {v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: self.me.idx() as u8, state: new.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing (a depth's state key signs once): {e}"))?;
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: self.me.idx() as u8, state: new, sigs: sig.hashes.clone() };
        let to = lngap_pos::rotation(CONTRACT_ID, d, self.registry.n());
        self.send(d, &hex::encode(entry.encode()), to)?;
        self.say(format!("submitted {uci} as move {d} (signed with the depth-{d} state key) to member {to}, the designated sealer; due t+{}s", self.rel(self.due(d))));
        Ok(())
    }

    /// Drop a submission for depth `d` in the venue's inbox, addressed to
    /// member `to`, and remember it for the fallback.
    fn send(&mut self, d: u32, entry: &str, to: usize) -> Result<()> {
        let at = unix_now();
        let name = format!("{}/{}.json", Store::inbox_dir(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
        self.store.write(&name, &InboxEntry { from: self.me.name().into(), depth: d, to, entry: entry.to_string(), at })?;
        self.pending = Some((d, entry.to_string(), to, at));
        Ok(())
    }

    /// Publish `uci` dishonestly, in one of four ways the disprove family
    /// and the authorship gate answer: `illegal` (the mechanical
    /// successor, signed — the `chess_*` kinds), `garbage` (a legal move
    /// with junk preimages — no refutation possible), `malformed` (the
    /// from-square byte 255 — `chess_malformed`), `wrongdepth` (a legal
    /// move signed with the NEXT depth's number — `wrong_slot`).
    fn cheat_move(&mut self, uci: &str, how: &str) -> Result<()> {
        let d = self.depth + 1;
        ensure!(instance::mover_at(d) == self.me, "it is {}'s move (depth {d})", instance::mover_at(d));
        if how == "late" {
            ensure!(unix_now() > self.due(d), "your move {d} is not due until t+{}s: `move` it", self.rel(self.due(d)));
        } else {
            ensure!(unix_now() <= self.due(d), "your move {d} was due at t+{}s", self.rel(self.due(d)));
        }
        let mv = Move::parse(uci).ok_or_else(|| anyhow!("not a UCI move: {uci}"))?;
        let me = self.me.idx() as u8;
        let (entry_bytes, what) = match how {
            "late" => {
                // a legal move for the slot that passed, queued for a
                // colluding member to seal late (the venue's control)
                let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow!("illegal: {v}"))?;
                pos.fullmove = 0;
                let new = ChessState { pos, mv, depth: d as u8 };
                let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: new.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing: {e}"))?;
                (ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: new, sigs: sig.hashes.clone() }.encode(), "LATE: after its due time — honest members will not seal it; a colluding member may (the venue page's `late` control)")
            }
            "illegal" => {
                let mut pos = lngap_chess::certificate::mechanical_successor(&self.state.pos, mv);
                pos.fullmove = 0;
                let new = ChessState { pos, mv, depth: d as u8 };
                let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: new.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing: {e}"))?;
                (ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: new, sigs: sig.hashes.clone() }.encode(), "WITHOUT checking legality (signed)")
            }
            "garbage" => {
                let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow!("a garbage-signed entry still needs a legal move: {v}"))?;
                pos.fullmove = 0;
                let new = ChessState { pos, mv, depth: d as u8 };
                (ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: new, sigs: vec![[0x11; 20]; 87] }.encode(), "with a GARBAGE signature (opens no key): honest members refuse it; a rogue may seal it (the venue page's `rogue` control)")
            }
            "malformed" => {
                let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow!("a malformed entry still starts from a legal move: {v}"))?;
                pos.fullmove = 0;
                let new = ChessState { pos, mv, depth: d as u8 };
                let mut head = chess::head(GAME_ID, d as u8, self.me, &new);
                head[8 + 36] = 255;
                let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &chess::auth_message(&head)).map_err(|e| anyhow!("signing: {e}"))?;
                let mut e = head.to_vec();
                for h in &sig.hashes {
                    e.extend_from_slice(h);
                }
                (e, "MALFORMED (from-square byte 255, signed)")
            }
            "wrongdepth" => {
                let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow!("{v}"))?;
                pos.fullmove = 0;
                let wrong = (d + 2) as u8; // my next depth: the state key of THAT depth signs it
                let new = ChessState { pos, mv, depth: wrong };
                let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, u32::from(wrong)), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: wrong, mover: me, state: new.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing: {e}"))?;
                (ChessEntry { game_id: GAME_ID, depth: wrong, mover: me, state: new, sigs: sig.hashes.clone() }.encode(), "claiming the WRONG depth (signed with that depth's key, which does not open this depth's): honest members refuse it; a rogue may seal it")
            }
            other => bail!("unknown cheat `{other}` (illegal | garbage | malformed | wrongdepth | late)"),
        };
        let to = lngap_pos::rotation(CONTRACT_ID, d, self.registry.n());
        self.send(d, &hex::encode(entry_bytes), to)?;
        if matches!(how, "garbage" | "wrongdepth" | "late") {
            // no honest member will seal it: no fallback resubmissions
            self.pending = None;
        }
        self.say(format!("submitted {uci} as move {d} to member {to} {what}"));
        Ok(())
    }

    /// Sync until `t` seconds after t0.
    fn until(&mut self, t: i64) -> Result<()> {
        while self.rel(unix_now()) < t {
            std::thread::sleep(Duration::from_millis(500));
            self.sync()?;
        }
        Ok(())
    }

    fn broadcast(&mut self, tx: &Transaction, what: &str) -> Result<()> {
        match self.rt.test_accept(tx) {
            Ok(_) => {}
            Err(e) => bail!("{what}: the node rejects it: {e}"),
        }
        let txid = self.rt.send_raw(tx)?;
        self.say(format!("broadcast {what}: {txid} ({} vB); it confirms at the venue's next block", tx.vsize()));
        Ok(())
    }

    /// Both parties' signatures on a skeleton, `[sig_hub, sig_user]`.
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
            bail!("not broadcast: `absent_{d}` is not mineable yet — {wait}; try again then");
        }
        self.say(format!("claiming: no valid move {d} by its due time t+{}s", self.rel(self.due(d))));
        self.broadcast(&tx, &format!("`{label}`"))
    }

    fn counter(&mut self, d: Option<u32>) -> Result<()> {
        let live = self.live_claims();
        let (base, depth) = match d {
            Some(d) => (format!("absent_{d}"), d),
            None => live.iter().find(|(b, dd)| !b.contains("counter") && instance::mover_at(*dd) == self.me).cloned().ok_or_else(|| anyhow!("no live claim against you to counter (an opponent's claim confirms at the venue's next block)"))?,
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
        let (base, d) = live.iter().find(|(_, d)| instance::mover_at(*d) == self.me).cloned().ok_or_else(|| anyhow!("no live claim against you on the chain (an opponent's claim confirms at the venue's next block; `status` after it)"))?;
        let label = format!("{base}/refute");
        let (tx, prev, leaf, control) = {
            let p = self.skel(&label)?;
            (p.tx.clone(), p.prevouts[0].clone(), p.leaf.script.clone(), p.control_block.clone())
        };
        let new = self.blocks.get(&d).ok_or_else(|| anyhow!("nothing is sealed for move {d}: nothing to refute with"))?;
        let new_head = new.header.head();
        let msg = self.parked_message(d)?;
        let pair_sig = self.ks.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).map_err(|e| anyhow!("{e}"))?;
        let auth = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &chess::auth_message(&new_head)).map_err(|e| anyhow!("{e}"))?;
        let sign_at = |b: &SealedBlock| -> Vec<Vec<u8>> {
            (0..HEAD_CHUNKS).map(|j| sig_bytes(&Keypair::from_secret_key(SECP256K1, &b.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect()
        };
        let sigs_new = sign_at(new);
        let mut w = if d >= 2 {
            let prior = self.blocks.get(&(d - 1)).ok_or_else(|| anyhow!("no seal for move {}", d - 1))?;
            let sigs_prev = sign_at(prior);
            refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&auth])
        } else {
            refute::refute_witness(&sigs_new, &pair_sig, &auth)
        };
        // the proposer fragment (D53): the block's proposer scalar signs too
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

    /// Every disprove leaf of the depth-`d` refuted tree, with whether it
    /// fires natively on the parked tuple.
    fn list_disproves(&self, d: u32) -> Vec<(String, bool)> {
        let firing = self.firing(d);
        let l = self.inst.layout(d);
        chess::disprove_leaves(&l, &self.inst.depth_keys(d).refute).into_iter().map(|pl| (pl.name.clone(), firing.contains(&pl.name))).collect()
    }

    fn disprove(&mut self, which: Option<String>) -> Result<()> {
        let live = self.live_refuted();
        let (base, d) = live.iter().find(|(_, d)| instance::mover_at(*d) != self.me).cloned().ok_or_else(|| anyhow!("no live refutation against you on the chain (a refutation confirms at the venue's next block; `status` after it)"))?;
        if matches!(which.as_deref(), Some("?") | Some("list")) {
            println!("  disprove leaves on `{base}` (depth {d}); * = fires on the parked tuple:");
            for (name, fires) in self.list_disproves(d) {
                println!("    {} {}", if fires { "*" } else { " " }, name);
            }
            println!("  `disprove` alone takes the first that fires; `disprove <name>` (with or without the chess_ prefix) a particular one");
            return Ok(());
        }
        let firing = self.firing(d);
        let name = match which {
            Some(w) => {
                let w = if w.starts_with("chess_") || w == "wrong_slot" { w } else { format!("chess_{w}") };
                ensure!(firing.iter().any(|f| *f == w), "`{w}` does not fire natively on the parked tuple (firing: {firing:?})");
                w
            }
            None => firing.first().cloned().ok_or_else(|| anyhow!("no disprove leaf fires on the parked tuple: the move is legal"))?,
        };
        let leaf_name = format!("disprove_{name}");
        self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta)?, &leaf_name)?;
        let (mut tx, prev, leaf, control) = self.payout_tx(&base, d, &leaf_name)?;
        let reveal = self.reveals.get(&base).ok_or_else(|| anyhow!("the mover's reveal is not known yet (the refutation must be confirmed)"))?.clone();
        let mut w: Vec<Vec<u8>> = Vec::new();
        if let Some(kind) = chess::kinds().into_iter().find(|k| chess::leaf_name(*k) == name) {
            let new = ChessState::from_e(self.blocks[&d].header.head()[8..48].try_into().unwrap()).map_err(|e| anyhow!("{e}"))?;
            let prior = if d >= 2 { ChessState::from_e(self.blocks[&(d - 1)].header.head()[8..48].try_into().unwrap()).map_err(|e| anyhow!("{e}"))? } else { ChessState::initial() };
            let exhibit = find_kind(&prior.pos, new.mv, &new.pos, kind).map(exhibit_values).ok_or_else(|| anyhow!("no certificate of kind {kind:?}"))?;
            w.extend(exhibit.iter().map(|&v| scriptnum(v)));
        }
        w.extend(refute::wots_wire(&reveal));
        w.push(sig_bytes(&self.keys.payment, &tx, &prev, &leaf));
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.say(format!("disproving the parked tuple of `{base}` (depth {d}): {name}"));
        self.broadcast(&tx, &leaf_name)
    }

    fn timely(&mut self) -> Result<()> {
        let live = self.live_refuted();
        let (base, d) = live.iter().find(|(_, d)| instance::mover_at(*d) != self.me).cloned().ok_or_else(|| anyhow!("no live refutation against you on the chain (a refutation confirms at the venue's next block; `status` after it)"))?;
        let scalars = self.flags.get(&d).cloned().ok_or_else(|| anyhow!("no flags known for move {d}: the members did not flag it"))?;
        self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta)?, "not_timely")?;
        let (mut tx, prev, leaf, control) = self.payout_tx(&base, d, "not_timely")?;
        let w = not_timely_witness(&tx, 0, std::slice::from_ref(&prev), &leaf, &self.keys.payment, &scalars);
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.say(format!("killing the refutation on `{base}` as NOT TIMELY: {} of {K} members flagged move {d}", scalars.iter().filter(|x| x.is_some()).count()));
        self.broadcast(&tx, "not_timely")
    }

    /// The split that is mine: the timeout split off a claim of mine, or
    /// the self-checking split off a refutation of mine.
    fn split(&mut self) -> Result<()> {
        // a refutation of mine standing
        if let Some((base, d)) = self.live_refuted().into_iter().find(|(_, d)| instance::mover_at(*d) == self.me) {
            let new = ChessState::from_e(self.blocks[&d].header.head()[8..48].try_into().unwrap()).map_err(|e| anyhow!("{e}"))?;
            // R(parked new state): the side to move forfeits
            let code: u8 = if new.pos.side == lngap_chess::Colour::White { 1 } else { 0 };
            let label = format!("{base}/refuted/split_{}", outcome_name(code));
            self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta + self.params.delta_prime)?, &label)?;
            let reveal = self.ks.reveal_uint(&instance::code_label(CONTRACT_ID, 1, d), u32::from(code))?;
            let pair = self.reveals.get(&base).ok_or_else(|| anyhow!("no reveal for {base}"))?.clone();
            let [sh, su] = self.sigs22(&label)?;
            let p = self.skel(&label)?;
            let mut tx = p.tx.clone();
            tx.input[0].witness = tapscript_witness(&checked_split_witness(su, sh, &reveal, &pair), &p.leaf.script, &p.control_block);
            self.say(format!("self-checking split on `{base}`: R(parked state) = {} (the side to move forfeits)", outcome_name(code)));
            return self.broadcast(&tx, &format!("`{label}`"));
        }
        // a claim of mine unanswered
        if let Some((base, d)) = self.live_claims().into_iter().find(|(_, d)| instance::mover_at(*d) != self.me) {
            let code: u8 = if self.me == Role::User { 0 } else { 1 };
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
            self.say(format!("timeout split on `{base}`: {} (the staller forfeits)", outcome_name(code)));
            return self.broadcast(&tx, &format!("`{label}`"));
        }
        bail!("nothing of yours to split")
    }

    fn balance(&self) -> Result<String> {
        let spk = &self.pubs[self.me.idx()].payout_spk;
        Ok(format!("{}'s payout address holds {} sat", self.me, self.rt.balance_of(spk)?.to_sat()))
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
  status | s          the board, the venue, what is due
  move <uci>          play (e.g. `move e2e4`): signed, sent to the designated sealer
  cheat <uci> [how]   publish dishonestly: illegal (default) | garbage | malformed | wrongdepth | late
  claim [d]           absence claim: the opponent did not move at depth d
  counter [d]         counter a claim against you: the claim was not due
  refute              answer the live claim against you with the venue's attestation
  disprove [kind]     disprove the parked tuple: no argument picks the leaf that fires;
                      `disprove ?` lists every leaf and marks those that fire
  timely              kill the refutation against you with the members' flags
  split               the split that is yours (timeout, or self-checking after the window)
  balance             your payout address
  wait <secs>         sleep, then sync
  until <t>           wait until t seconds after t0
  quit";

impl Player {
    /// One command line; the text to show.
    pub fn exec(&mut self, line: &str) -> Result<String> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        let Some(cmd) = parts.first() else { return Ok(String::new()) };
        let arg = parts.get(1).map(|s| s.to_string());
        let arg2 = parts.get(2).map(|s| s.to_string());
        let before = self.log.len();
        let r: Result<String> = match *cmd {
            "help" | "?" => Ok(HELP.to_string()),
            "status" | "s" => self.status(),
            "board" | "b" => Ok(format!("{}", self.state.pos)),
            "move" | "m" => arg.ok_or_else(|| anyhow!("move <uci>")).and_then(|u| self.play_move(&u)).map(|_| String::new()),
            "cheat" => arg.ok_or_else(|| anyhow!("cheat <uci> [illegal|garbage|malformed|wrongdepth]")).and_then(|u| self.cheat_move(&u, arg2.as_deref().unwrap_or("illegal"))).map(|_| String::new()),
            "claim" => self.claim(arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "counter" => self.counter(arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "refute" => self.refute().map(|_| String::new()),
            "disprove" => self.disprove(arg).map(|_| String::new()),
            "timely" => self.timely().map(|_| String::new()),
            "split" => self.split().map(|_| String::new()),
            "balance" => self.balance(),
            "wait" => {
                let secs: u64 = arg.and_then(|a| a.parse().ok()).unwrap_or(1);
                std::thread::sleep(Duration::from_secs(secs));
                Ok(String::new())
            }
            "until" => arg.and_then(|a| a.parse().ok()).ok_or_else(|| anyhow!("until <t>")).and_then(|t| self.until(t)).map(|_| String::new()),
            other => Err(anyhow!("unknown command {other} (try `help`)")),
        };
        // what the command said through `say` is part of its output
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
        print!("{me}> ");
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

// ============ the page's view of the player ============

#[derive(Serialize, Clone, Debug)]
pub struct ActionView {
    pub name: String,
    pub enabled: bool,
    pub hint: String,
    /// The exact command the button sends (the name, unless a depth is
    /// implied).
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
    /// The move's due time, seconds after t0.
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
    /// Seconds after t0: median-time-past, now, the next move's due time.
    pub mtp: i64,
    pub now: i64,
    pub ell: u32,
    pub backoff: u32,
    pub margin: u32,
    pub next_due: i64,
    pub block_secs: u64,
    pub depth: u32,
    pub fen: String,
    pub to_move: String,
    pub terminal: Option<String>,
    pub last_move: Option<String>,
    pub n: usize,
    pub threshold: u32,
    pub slots: Vec<SlotView>,
    pub live: Vec<LiveView>,
    pub actions: Vec<ActionView>,
    pub disproves: Vec<DisproveView>,
    pub mempool: Vec<String>,
    pub balance_sat: u64,
    pub log: Vec<String>,
}
