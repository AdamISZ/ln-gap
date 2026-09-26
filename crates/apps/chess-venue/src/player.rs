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
use lngap_pos::instance::{self, Game, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNKS, HEAD_CHUNK_START};
use lngap_pos::ttt::checked_split_witness;
use lngap_pos::{Registry, SealedBlock};

use crate::store::*;

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
    // ----- the venue as seen -----
    blocks: BTreeMap<u32, SealedBlock>,
    flags: BTreeMap<u32, Vec<Option<SecretKey>>>,
    /// The position after the last sealed LEGAL move, and its depth.
    state: ChessState,
    depth: u32,
    /// Slots that sealed an entry that is not a legal continuation (the
    /// disprove family's business), by slot: what was wrong.
    bad_slots: BTreeMap<u32, String>,
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

    /// The height from which a depth-`d` claim is spendable: its CLTV,
    /// and the broadcaster's `to_self_delay` on the contract output.
    fn mature_at(&self, d: u32) -> u32 {
        self.inst.claim_from(d).max(self.vparams.b0 + u32::from(self.params.to_self_delay))
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

    /// The venue slot the next Bitcoin block will seal.
    fn next_slot(&self) -> u32 {
        self.height() + 1 - self.vparams.b0
    }

    // ============ setup ============

    pub fn open(dir: PathBuf, me: Role, max_depth: u32) -> Result<Player> {
        let store = Store::new(dir);
        println!("{me}: waiting for the venue's node...");
        let node = wait_for(|| store.read::<NodeInfo>(Store::node()))?;
        let rt = Regtest::attach(&PathBuf::from(node.datadir))?;
        println!("{me}: waiting for the venue's registry...");
        let registry: Registry = wait_for(|| store.read(Store::registry()))?;
        println!("{me}: registry has {} members, threshold {}, slots 0..={}", registry.n(), registry.threshold, registry.max_slot());

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
            let deadline = vparams.b0 + 4_000;
            let probe = PosInstance::new(CONTRACT_ID, Amount::from_sat(POT_SAT), deadline, GAME_ID, Game::Chess, vparams.b0, 1, merged.clone(), registry.clone())?;
            let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
            let tree = probe.tree(&ctx)?;
            store.write(Store::contract(), &ContractJson { spk: hex::encode(tree.script_pubkey().as_bytes()), value: POT_SAT, deadline })?;
            println!("{me}: contract proposed ({} sat); waiting for the venue to fund it...", POT_SAT);
            wait_for(|| store.read(Store::funded()))?
        } else {
            println!("{me}: waiting for the user's contract and the venue's funding...");
            wait_for(|| store.read(Store::funded()))?
        };
        let contract: ContractJson = wait_for(|| store.read(Store::contract()))?;
        ensure!(vparams.b0 == funded.height, "the venue's slot clock starts at the funding height");
        let inst = PosInstance::new(CONTRACT_ID, Amount::from_sat(POT_SAT), contract.deadline, GAME_ID, Game::Chess, vparams.b0, 1, merged, registry.clone())?;
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
        println!("{me}: every skeleton is fully signed. The game is on: white ({}) moves first; the venue seals slot 1 at its next tick.", Role::User);
        Ok(Player {
            me,
            store,
            rt,
            keys,
            ks,
            pubs,
            params,
            scanned: vparams.b0,
            vparams,
            registry,
            inst,
            their_state_keys,
            graph,
            blocks: BTreeMap::new(),
            flags: BTreeMap::new(),
            state: ChessState::initial(),
            depth: 0,
            bad_slots: BTreeMap::new(),
            live: BTreeMap::new(),
            spent: HashMap::new(),
            reveals: BTreeMap::new(),
            log: Vec::new(),
        })
    }

    // ============ the venue and the chain, as seen ============

    /// Read new venue blocks and flags, scan new Bitcoin blocks; print
    /// what changed.
    fn sync(&mut self) -> Result<()> {
        // venue blocks
        let mut slot = self.blocks.keys().next_back().map(|s| s + 1).unwrap_or(1);
        while let Some(b) = self.store.read::<BlockJson>(&Store::block(slot))? {
            let block = b.to_block()?;
            self.on_block(slot, &block)?;
            self.blocks.insert(slot, block);
            slot += 1;
        }
        // flags
        for s in 1..slot {
            if self.flags.contains_key(&s) {
                continue;
            }
            if let Some(f) = self.store.read::<FlagsJson>(&Store::flags(s))? {
                let f = flags_from_json(&f)?;
                let n = f.iter().filter(|x| x.is_some()).count();
                self.flags.insert(s, f);
                self.say(format!("venue: slot {s} passed its deadline empty — {n} of {K} members flagged it"));
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

    fn on_block(&mut self, slot: u32, block: &SealedBlock) -> Result<()> {
        if block.entry.is_empty() {
            self.say(format!("venue: slot {slot} sealed EMPTY by member {}", block.proposer));
            return Ok(());
        }
        let mover = instance::mover_at(slot);
        let e = match ChessEntry::decode(&block.entry) {
            Ok(e) => e,
            Err(err) => {
                self.bad_slots.insert(slot, format!("undecodable entry ({err})"));
                self.say(format!("venue: slot {slot} sealed by member {} with an UNDECODABLE entry", block.proposer));
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
            self.say(format!("venue: slot {slot} sealed by member {} with an entry for the WRONG slot or mover (wrong_slot)", block.proposer));
            return Ok(());
        }
        if !signed {
            self.bad_slots.insert(slot, "garbage signature".into());
            self.say(format!("venue: slot {slot} sealed by member {} with {mover}'s move {} — but the signature opens no key (not a move)", block.proposer, e.state.mv));
            return Ok(());
        }
        // a legal continuation of the position?
        if slot != self.depth + 1 {
            self.bad_slots.insert(slot, format!("the game was at depth {}", self.depth));
            self.say(format!("venue: slot {slot} sealed {mover}'s move {} but the game is at depth {} — out of sequence", e.state.mv, self.depth));
            return Ok(());
        }
        match apply(&self.state.pos, e.state.mv) {
            Ok(mut pos) => {
                pos.fullmove = 0;
                if pos != e.state.pos {
                    self.bad_slots.insert(slot, "the claimed position is not the move's result".into());
                    self.say(format!("venue: slot {slot} sealed {mover}'s move {} with a position that is NOT its result — disprovable", e.state.mv));
                    return Ok(());
                }
                self.state = e.state.clone();
                self.depth = slot;
                let term = lngap_chess::terminal(&self.state.pos).map(|t| format!(" — {t:?}")).unwrap_or_default();
                self.say(format!("venue: slot {slot} sealed by member {}: {mover} played {} (signed, legal){term}", block.proposer, e.state.mv));
            }
            Err(v) => {
                self.bad_slots.insert(slot, format!("{v}"));
                self.say(format!("venue: slot {slot} sealed {mover}'s move {} — ILLEGAL ({v}); the absence claim and the disprove family apply", e.state.mv));
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
        let head = |s: u32| -> Result<[u8; 48]> { Ok(self.blocks.get(&s).ok_or_else(|| anyhow!("no venue block at slot {s}"))?.header.head()) };
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

    fn status(&mut self) -> Result<()> {
        let h = self.height();
        let slot = self.next_slot();
        println!("--- {} | height {h} | next venue slot {slot} | game depth {} | side to move: {} ({}) | venue {} members, threshold {}", self.me, self.depth, if self.state.pos.side == lngap_chess::Colour::White { "white" } else { "black" }, instance::mover_at(self.depth + 1), self.registry.n(), self.registry.threshold);
        println!("{}", self.state.pos);
        if let Some(t) = lngap_chess::terminal(&self.state.pos) {
            println!("    terminal: {t:?}");
        }
        // graph transactions waiting in the mempool (confirm at the next tick)
        if let Ok(pool) = self.rt.mempool() {
            for p in &self.graph {
                if pool.contains(&p.txid()) {
                    println!("    in the mempool, confirms at the next block: `{}`", p.label);
                }
            }
        }
        for (s, why) in &self.bad_slots {
            println!("    slot {s}: not a legal move ({why})");
        }
        for (s, f) in &self.flags {
            println!("    slot {s}: flagged empty by {} of {K}", f.iter().filter(|x| x.is_some()).count());
        }
        // what is due
        let mover = instance::mover_at(self.depth + 1);
        let claimed = self.live.contains_key(&format!("absent_{}", self.depth + 1));
        if self.blocks.contains_key(&(self.depth + 1)) && self.depth + 1 < slot && mover != self.me && !claimed {
            let m = self.mature_at(self.depth + 1);
            println!("    {} did not move at slot {}: you may `claim` from height {m}{}", mover, self.depth + 1, if h < m { format!(" ({} blocks to go)", m - h) } else { String::new() });
        }
        let delta = self.params.delta;
        let delta2 = self.params.delta + self.params.delta_prime;
        for (base, d) in self.live_claims() {
            let who = instance::mover_at(d);
            if who == self.me {
                println!("    live claim `{base}` (depth {d}) against you: `refute`{} (the claimant's timeout opens at height {})", if base.starts_with("absent_") && !base.contains("counter") && d >= 2 { " or `counter`" } else { "" }, self.window_open(&base, delta).unwrap_or(0));
            } else {
                println!("    your live claim `{base}` (depth {d}): `split` from height {}, unless it is refuted or countered first", self.window_open(&base, delta).unwrap_or(0));
            }
        }
        for (base, d) in self.live_refuted() {
            let who = instance::mover_at(d);
            let r = format!("{base}/refute");
            if who == self.me {
                println!("    your refutation on `{base}` (depth {d}) stands: `split` from height {} (the disprove window closes at {})", self.window_open(&r, delta2).unwrap_or(0), self.window_open(&r, delta).unwrap_or(0));
            } else {
                let firing = self.firing(d);
                println!("    live refutation on `{base}` (depth {d}): `disprove` ({}) or `timely` ({} flags known), from height {}", if firing.is_empty() { "nothing fires natively".to_string() } else { firing.join(", ") }, self.flags.get(&d).map(|f| f.iter().filter(|x| x.is_some()).count()).unwrap_or(0), self.window_open(&r, delta).unwrap_or(0));
            }
        }
        Ok(())
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
        let slot = self.next_slot();
        ensure!(slot == d, "the next venue slot is {slot} but your move is depth {d}: the slot for your move has passed (you are stalled) or has not come");
        let mv = Move::parse(uci).ok_or_else(|| anyhow!("not a UCI move: {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow!("illegal: {v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: self.me.idx() as u8, state: new.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing (a depth's state key signs once): {e}"))?;
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: self.me.idx() as u8, state: new, sigs: sig.hashes.clone() };
        let name = format!("{}/{}.json", Store::inbox_dir(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
        self.store.write(&name, &InboxEntry { from: self.me.name().into(), entry: hex::encode(entry.encode()) })?;
        self.say(format!("submitted {uci} for slot {d} (signed with the depth-{d} state key); the venue seals it at the next block"));
        Ok(())
    }

    /// Play `uci` WITHOUT checking legality: the mechanical successor,
    /// signed for real — what a cheating mover publishes (the disprove
    /// family's business).
    fn cheat_move(&mut self, uci: &str) -> Result<()> {
        let d = self.depth + 1;
        ensure!(instance::mover_at(d) == self.me, "it is {}'s move (depth {d})", instance::mover_at(d));
        let slot = self.next_slot();
        ensure!(slot == d, "the next venue slot is {slot} but your move is depth {d}");
        let mv = Move::parse(uci).ok_or_else(|| anyhow!("not a UCI move: {uci}"))?;
        let mut pos = lngap_chess::certificate::mechanical_successor(&self.state.pos, mv);
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let sig = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: self.me.idx() as u8, state: new.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing: {e}"))?;
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: self.me.idx() as u8, state: new, sigs: sig.hashes.clone() };
        let name = format!("{}/{}.json", Store::inbox_dir(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos());
        self.store.write(&name, &InboxEntry { from: self.me.name().into(), entry: hex::encode(entry.encode()) })?;
        self.say(format!("submitted {uci} for slot {d} WITHOUT checking legality (signed): the venue seals it regardless"));
        Ok(())
    }

    /// Sync until the next venue slot is at least `slot`.
    fn until_slot(&mut self, slot: u32) -> Result<()> {
        while self.next_slot() < slot {
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
        let m = self.mature_at(d);
        ensure!(self.height() >= m, "not broadcast: `absent_{d}` cannot be mined before height {m} ({} blocks to go) — type `claim {d}` again from then", m - self.height());
        self.say(format!("claiming: no valid move at slot {d}"));
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
        self.say(format!("countering `{base}`: the claim was not due — no move at slot {}", depth - 1));
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
        let new = self.blocks.get(&d).ok_or_else(|| anyhow!("the venue holds no block at slot {d}"))?;
        ensure!(!new.entry.is_empty(), "slot {d} is empty on the venue: nothing to refute with");
        let new_head = new.header.head();
        let msg = self.parked_message(d)?;
        let pair_sig = self.ks.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).map_err(|e| anyhow!("{e}"))?;
        let auth = self.ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &chess::auth_message(&new_head)).map_err(|e| anyhow!("{e}"))?;
        let sign_at = |b: &SealedBlock| -> Vec<Vec<u8>> {
            (0..HEAD_CHUNKS).map(|j| sig_bytes(&Keypair::from_secret_key(SECP256K1, &b.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect()
        };
        let sigs_new = sign_at(new);
        let mut w = if d >= 2 {
            let prior = self.blocks.get(&(d - 1)).ok_or_else(|| anyhow!("no block at slot {}", d - 1))?;
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
        self.say(format!("refuting `{base}`: the venue attested my move at slot {d} (sealed by member {})", new.proposer));
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
        let scalars = self.flags.get(&d).cloned().ok_or_else(|| anyhow!("no flags known for slot {d}: the members did not flag it"))?;
        self.need_height(self.window_open(&format!("{base}/refute"), self.params.delta)?, "not_timely")?;
        let (mut tx, prev, leaf, control) = self.payout_tx(&base, d, "not_timely")?;
        let w = not_timely_witness(&tx, 0, std::slice::from_ref(&prev), &leaf, &self.keys.payment, &scalars);
        tx.input[0].witness = tapscript_witness(&w, &leaf, &control);
        self.say(format!("killing the refutation on `{base}` as NOT TIMELY: {} of {K} members flagged slot {d}", scalars.iter().filter(|x| x.is_some()).count()));
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

    fn balance(&self) -> Result<()> {
        let spk = &self.pubs[self.me.idx()].payout_spk;
        println!("  {}'s payout address holds {} sat", self.me, self.rt.balance_of(spk)?.to_sat());
        Ok(())
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
  move <uci>          play (e.g. `move e2e4`): signed, queued for the next slot
  cheat <uci>         play without checking legality (what a cheater publishes)
  claim [d]           absence claim: the opponent did not move at depth d
  counter [d]         counter a claim against you: the claim was not due
  refute              answer the live claim against you with the venue's attestation
  disprove [kind]     disprove the parked tuple: no argument picks the leaf that fires;
                      `disprove ?` lists every leaf and marks those that fire
  timely              kill the refutation against you with the members' flags
  split               the split that is yours (timeout, or self-checking after the window)
  balance             your payout address
  wait <secs>         sleep, then sync
  until <slot>        wait until the next venue slot is <slot>
  quit";

pub fn run(dir: PathBuf, me: Role, max_depth: u32) -> Result<()> {
    let mut p = Player::open(dir, me, max_depth)?;
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
        let parts: Vec<&str> = line.split_whitespace().collect();
        let Some(cmd) = parts.first() else { continue };
        let arg = parts.get(1).map(|s| s.to_string());
        let r = match *cmd {
            "help" | "?" => {
                println!("{HELP}");
                Ok(())
            }
            "status" | "s" => p.status(),
            "board" | "b" => {
                println!("{}", p.state.pos);
                Ok(())
            }
            "move" | "m" => arg.ok_or_else(|| anyhow!("move <uci>")).and_then(|u| p.play_move(&u)),
            "cheat" => arg.ok_or_else(|| anyhow!("cheat <uci>")).and_then(|u| p.cheat_move(&u)),
            "until" => arg.and_then(|a| a.parse().ok()).ok_or_else(|| anyhow!("until <slot>")).and_then(|s| p.until_slot(s)),
            "claim" => p.claim(arg.and_then(|a| a.parse().ok())),
            "counter" => p.counter(arg.and_then(|a| a.parse().ok())),
            "refute" => p.refute(),
            "disprove" => p.disprove(arg),
            "timely" => p.timely(),
            "split" => p.split(),
            "balance" => p.balance(),
            "wait" => {
                let secs: u64 = arg.and_then(|a| a.parse().ok()).unwrap_or(1);
                std::thread::sleep(Duration::from_secs(secs));
                Ok(())
            }
            "quit" | "exit" => break,
            other => Err(anyhow!("unknown command {other} (try `help`)")),
        };
        if let Err(e) = r {
            println!("  ! {e:#}");
        }
    }
    Ok(())
}
