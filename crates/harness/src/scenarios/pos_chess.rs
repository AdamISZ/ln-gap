//! The PoS absence-claim graph's CHESS scenario suite (POS_FACTCHAIN_PLAN.md
//! step 7's PC1-PC9; D42; PC13 the D50 timeliness flag): the pos_stall suite's chess sibling, on the wired
//! `lngap-pos` graph with `Game::Chess` — the twelve chess kinds over the
//! parked pair, the tied readout, 336-bit per-depth state keys.
//!
//! Like the PS suite these run WITHOUT the channel wrapper: the contract
//! output C is funded directly and the pre-signed graph is played by hand.
//! Two chess-shaped differences from PS, both D42:
//!
//! - there is NO exhibit family: chess terminality is not a state field, so
//!   the terminal game (PC4, fool's mate) resolves through the ABSENCE path
//!   — nothing is sealed for the mated side and its claim is unanswerable; and
//! - the pre-sign fee is 60k sat, not the 1k placeholder: the chess pair
//!   readout is ~44 kvB and the placeholder would sit under the relay floor
//!   (the fee is the scenario's own parameter; the measurements are vB).
//!
//! The reference games: 1. e4 e5 for the early paths, and fool's mate
//! (1. f3 e5 2. g4 Qh4#) for the terminal ones — the hub (black) mates at
//! depth 4, the mated user's move would be depth 5. Since D55 the venue
//! attests entries keyed by (contract, depth), sealed on submission by the
//! designated member; there are no slots and no empty seals; the world
//! keeps a wall clock (a move due every 60 s, claims 60 s after the due
//! time against median-time-past).

use std::collections::HashMap;

use anyhow::{ensure, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, Transaction, TxOut, Txid};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, PresignedTx, Role};
use lngap_chess::certificate::{find_kind, mechanical_successor};
use lngap_chess::leaf::exhibit_values;
use lngap_chess::{apply, Move};
use lngap_chess_fc::{ChessEntry, ChessState};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsParams, WotsPublic, WotsSig};
use lngap_pos::chess;
use lngap_pos::graph::{not_timely_witness, proposer_witness};
use lngap_pos::instance::{self, Game as WhichGame, GameClock, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNK_START, HEAD_CHUNKS};
use lngap_pos::ttt;
use lngap_pos::{Member, PosClient, PosMiner, Registry, SealedBlock};

use super::{Report, Scenario};

/// The roster's base seed: member `i` is seeded `SEED[0] + i`.
const SEED: [u8; 32] = [0x77; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
/// Fool's mate lands at depth 4; the suite's longest line runs to 6.
const MAX_DEPTH: u32 = 8;
/// Seconds per move (D55's `ell`) and the claim margin `m`.
const ELL: u32 = 60;
const MARGIN: u32 = 60;
/// 0.01 BTC — big enough that the 60k-sat pre-sign fee (D42) leaves the
/// winner's share readable.
const POT: u64 = 1_000_000;
/// The pre-sign fee per hop: the chess pair readout is ~44 kvB, so the 1k
/// placeholder would sit under the relay floor (D42).
const FEE: u64 = 60_000;
/// The skeleton count at open: settle + 8x(claim, refute, 3+3 splits) + 8
/// per-depth equiv leaves (D43) + 7x(counter, refute, 3+3 splits) (D44).
const GRAPH_LEN: usize = 129;
/// The chess state key's reveal length (the tied-WOTS authorship: 84
/// message + 3 checksum digits over the 42 signed bytes).
const STATE_DIGITS: usize = 87;
/// The venue's roster (D51, D53, D55): five members sharing ONE content
/// key (seeded `SEED`), each with its member key, its proposer keys and
/// its flag keys; any member may seal any depth (the designated one is the
/// rotation, the mover falling back past silent members); the flag
/// threshold is the
/// majority, 3 of 5 (D50 amended: false emptiness costs 3 flaggers, a
/// standing late attestation 3 abstainers plus the proposer).
const K: usize = 5;
const T: u32 = 3;
/// The hub's member: the colluding proposer in the late fixtures.
const HUB_MEMBER: usize = 1;

fn members() -> Vec<Member> {
    (0..K as u8).map(|i| Member::new([SEED[0] + i; 32])).collect()
}

/// An entry's authorship message (D43): the 40 state bytes, then the
/// move's two bytes (low first) — `chess::auth_message` of the head.
fn entry_msg(e: &ChessEntry) -> Vec<u8> {
    let mv = u32::from(e.state.mv.to_u16());
    let mut m = e.state.to_e().to_vec();
    m.extend_from_slice(&(mv as u16).to_le_bytes());
    m
}


fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

/// The minimal script-number encoding of a small non-negative value (the
/// exhibit elements are squares and ray indices, all under 128).
fn scriptnum(v: i64) -> Vec<u8> {
    assert!((0..128).contains(&v), "exhibit values are small and non-negative");
    if v == 0 { vec![] } else { vec![v as u8] }
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &bitcoin::ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

/// A conflicting signature under the mover's depth-`d` state key,
/// reproduced by hand from the keystore's derivation (the honest keystore
/// refuses to equivocate — asserted at the use site; the 4b wrong-code
/// pattern).
fn adversarial_state_sig(ks_seed_label: &str, d: u32, msg: &[u8]) -> WotsSig {
    let mut ks = KeyStore::new(Seed::from_label(ks_seed_label));
    let label = instance::state_label(CONTRACT_ID, 1, d);
    ks.generate_wots(&label, 42).unwrap();
    ks.sign_wots(&label, msg).unwrap()
}

/// One PoS-venue chess game with its contract funded on a fresh regtest,
/// the venue with the contract registered (D55: attestations keyed by
/// (contract, depth), sealed on submission), the 129-skeleton graph
/// pre-signed. The world keeps a wall clock (`now`, unix seconds).
struct ChessPosGame {
    rt: Regtest,
    params: ChannelParams,
    user: PartyKeys,
    hub: PartyKeys,
    user_ks: KeyStore,
    hub_ks: KeyStore,
    pubs: [PartyPubKeys; 2],
    inst: PosInstance,
    /// The registry the members announced for the contract at open (what
    /// the contract pins and the client verifies seals against).
    registry: Registry,
    miner: PosMiner,
    client: PosClient,
    /// The seal the refutations read, by depth.
    sealed: HashMap<u32, SealedBlock>,
    /// Anyone's native check of a depth-`d` entry's signature: the mover's
    /// state key (in a deployment these ride the draft's public offers).
    venue_commits: HashMap<u32, WotsPublic>,
    /// The validators' published flag scalars, by depth: `flags[d][i]` is
    /// validator `i`'s, present once it saw depth `d`'s due time pass with
    /// no signed entry attested (D50, D55). Published as data; the claimant
    /// collects them.
    flags: HashMap<u32, Vec<Option<SecretKey>>>,
    graph: Vec<PresignedTx>,
    /// The position after the last sealed move.
    state: ChessState,
    /// The deepest sealed move.
    depth: u32,
    /// The world's wall clock (unix seconds).
    now: u32,
    btc_open: u32,
    /// (height, role, txid, broadcaster, vsize) of each broadcast.
    seen: Vec<(u32, String, Txid, Role, usize)>,
    log: Vec<String>,
}

impl ChessPosGame {
    fn open(value: Amount) -> Result<ChessPosGame> {
        let rt = Regtest::start()?;
        let mut miner = PosMiner::new(SEED, members());
        let registry = miner.registry(CONTRACT_ID, MAX_DEPTH)?;
        ensure!(registry.threshold == T && registry.n() == K, "the PoC threshold is the majority of the roster");
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("pc/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("pc/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("pc/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("pc/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Chess)?;
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Chess)?;
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH)?;
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH)?;
        ensure!(keys_u == keys_h, "the merged key sets must agree");
        // the game's clock (D55): move d is due at t0 + d·ELL; its claim is
        // valid from the due time plus MARGIN against median-time-past
        let t0 = rt.mtp()?;
        let clock = GameClock { t0, ell: ELL, margin: MARGIN };
        let deadline = t0 + 100_000;
        let btc_open = rt.height()? + 1;
        let inst = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, WhichGame::Chess, clock, keys_u, registry.clone())?;
        miner.register(CONTRACT_ID, MAX_DEPTH, inst.authorship()).map_err(|e| anyhow::anyhow!(e))?;
        let params = ChannelParams {
            presign_fee: sat(FEE),
            ..ChannelParams::regtest(Amount::from_sat(400_000))
        };
        let pubs = [user.public(), hub.public()];
        let mut venue_commits = HashMap::new();
        for d in 1..=MAX_DEPTH {
            let ks = if instance::mover_at(d) == Role::User { &mut user_ks } else { &mut hub_ks };
            venue_commits.insert(d, ks.wots_public(&instance::state_label(CONTRACT_ID, 1, d))?);
        }
        let mut g = ChessPosGame {
            rt,
            params,
            user,
            hub,
            user_ks,
            hub_ks,
            pubs,
            inst,
            registry,
            miner,
            client: PosClient::new(CONTRACT_ID),
            sealed: HashMap::new(),
            venue_commits,
            flags: HashMap::new(),
            graph: Vec::new(),
            state: ChessState::initial(),
            depth: 0,
            now: t0,
            btc_open,
            seen: Vec::new(),
            log: Vec::new(),
        };
        let ctx = g.ctx();
        let tree = g.inst.tree(&ctx)?;
        let (c_op, c_prev) = g.rt.fund(&tree.script_pubkey(), g.inst.value)?;
        ensure!(g.rt.height()? == btc_open, "the funding mined exactly one block");
        g.graph = g.inst.graph(&ctx, c_op, &c_prev)?;
        ensure!(
            g.graph.len() == GRAPH_LEN,
            "the wired chess graph: settle + {MAX_DEPTH}x(claim, refute, 3+3 splits) + {MAX_DEPTH} per-depth equiv (D43) + {}x(counter, refute, 3+3 splits) (D44); NO exhibit family (D42)",
            MAX_DEPTH - 1
        );
        g.say(format!(
            "game opened: contract {CONTRACT_ID}, pot {} sat; {} pre-signed transactions; a move every {ELL} s, claims {MARGIN} s after a move's due time",
            g.inst.value.to_sat(),
            g.graph.len()
        ));
        Ok(g)
    }

    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] }
    }

    fn ks(&mut self, r: Role) -> &mut KeyStore {
        match r {
            Role::User => &mut self.user_ks,
            Role::Hub => &mut self.hub_ks,
        }
    }

    fn payment(&self, r: Role) -> &Keypair {
        match r {
            Role::User => &self.user.payment,
            Role::Hub => &self.hub.payment,
        }
    }

    fn say(&mut self, s: String) {
        let h = self.rt.height().unwrap();
        let t = self.now - self.inst.t0;
        self.log.push(format!("[pos @ {h} / t+{t}s / depth {}] {s}", self.depth));
    }

    fn head(&self, d: u32) -> [u8; 48] {
        self.sealed[&d].header.head()
    }

    /// Advance the world clock to `t` and publish the flags every member
    /// owes: each depth up to the owed move (none once the game is over)
    /// whose due time has passed with no attested, mover-signed entry is
    /// flagged by every non-silent member, once (D50, D55).
    fn clock_to(&mut self, t: u32) {
        self.now = self.now.max(t);
        let owed = if lngap_chess::terminal(&self.state.pos).is_none() { self.depth + 1 } else { self.depth };
        for d in 1..=owed.min(MAX_DEPTH) {
            if self.flags.contains_key(&d) || self.inst.due(d) > self.now {
                continue;
            }
            let sealed = &self.sealed;
            if self.miner.holds_signed(CONTRACT_ID, d, |h| sealed.values().find(|b| b.head() == *h).map(|b| b.entry.clone())) {
                continue;
            }
            let scalars = self.miner.flag(CONTRACT_ID, d);
            let n = scalars.iter().filter(|f| f.is_some()).count();
            self.flags.insert(d, scalars);
            self.say(format!("move {d} was due at t+{}s and no signed entry was attested: {n} of {K} members flag it", self.inst.due(d) - self.inst.t0));
        }
    }

    /// Submit the entry bytes for the next depth to the designated sealer
    /// (the rotation, falling back past silent members after the backoff),
    /// verify the seal natively; `advance` carries the new position when
    /// the entry is a real signed move.
    fn submit(&mut self, bytes: Vec<u8>, advance: Option<ChessState>, what: String) -> Result<()> {
        let d = self.depth + 1;
        self.clock_to(self.inst.due(d - 1) + 10);
        let designated = lngap_pos::rotation(CONTRACT_ID, d, K);
        let Some(sealer) = self.miner.default_sealer(CONTRACT_ID, d) else {
            self.say(format!("move {d}: every member is SILENT — the mover's entry is NOT sealed"));
            return Ok(());
        };
        if sealer != designated {
            self.say(format!("move {d}: the designated sealer, member {designated}, is silent; after the backoff the mover resubmits to member {sealer}"));
        }
        let block = self.miner.seal_entry(CONTRACT_ID, d, sealer, &bytes).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &self.registry).map_err(|e| anyhow::anyhow!(e))?;
        self.sealed.insert(d, block);
        if let Some(new) = advance {
            self.state = new;
        }
        self.depth = d;
        self.say(format!("move {d} sealed by member {sealer} on submission: {what}"));
        Ok(())
    }

    /// The mover of the next depth plays `uci` (legal), signed for real.
    /// Returns the new state and the state signature (evidence material).
    fn play(&mut self, uci: &str) -> Result<(ChessState, WotsSig)> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: vec![] }))?;
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: sig.hashes.clone() };
        ensure!(refute::check_entry_sig(&self.venue_commits[&d], &entry_msg(&entry), &entry.sigs), "depth {d}: the entry does not open the mover's state key");
        self.submit(entry.encode(), Some(new.clone()), format!("{mover}'s move {mv}; attested, the signature opens the key"))?;
        Ok((new, sig))
    }

    /// The mover of the next depth does not move: nothing is submitted, the
    /// clock passes the due time, and (if the game is not over) the
    /// members flag it.
    fn stall(&mut self) {
        let d = self.depth + 1;
        self.say(format!("{} does not move {d}: nothing is sealed (D55: no empty seals)", instance::mover_at(d)));
        self.clock_to(self.inst.due(d) + 1);
    }

    /// Mine blocks until the Bitcoin height reaches `h` (the dispute
    /// windows are relative, in blocks; the venue is not involved).
    fn wait_to(&mut self, h: u32) -> Result<()> {
        let now = self.rt.height()?;
        if h > now {
            self.rt.mine(u64::from(h - now))?;
        }
        Ok(())
    }

    /// Wait until a depth-`d` claim is valid: the broadcaster's
    /// to_self_delay on the contract output, and median-time-past past the
    /// claim time (the world clock follows; the members flag what is due).
    fn wait_claim(&mut self, d: u32) -> Result<()> {
        self.wait_to(self.btc_open + self.params.to_self_delay as u32)?;
        let t = self.inst.claim_from(d);
        self.rt.make_time_final(t)?;
        self.clock_to(t + 1);
        Ok(())
    }

    /// The mover of the next depth plays `uci` ILLEGALLY: the mechanical
    /// successor, signed over the CLAIMED state (validly signed garbage:
    /// the venue checks authorship, never legality; the disprove family
    /// judges the transition).
    fn play_invalid(&mut self, uci: &str) -> Result<()> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = mechanical_successor(&self.state.pos, mv);
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: vec![] }))?;
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: sig.hashes.clone() };
        self.submit(entry.encode(), Some(new), format!("{mover}'s move {uci} — attested, NOT legal"))
    }

    /// An entry for the next depth claiming `uci` with a GARBAGE sigs region
    /// (D41): honest members refuse it (D55); a ROGUE member (the hub's)
    /// seals it anyway — provable misbehaviour, inert in the contract. The
    /// position does NOT advance, and the members still flag the depth at
    /// its due time.
    fn play_garbage_signed(&mut self, uci: &str) -> Result<()> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new, sigs: vec![[0x11; 20]; STATE_DIGITS] };
        self.clock_to(self.inst.due(d - 1) + 10);
        let honest = self.miner.default_sealer(CONTRACT_ID, d).expect("a live member");
        let refused = self.miner.seal_entry(CONTRACT_ID, d, honest, &entry.encode()).err().unwrap_or_default();
        ensure!(refused.contains("refuses"), "an honest member refuses the unsigned entry: {refused}");
        let block = self.miner.seal_unchecked(CONTRACT_ID, d, HUB_MEMBER, &entry.encode()).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &self.registry).map_err(|e| anyhow::anyhow!(e))?;
        self.say(format!("depth {d}: member {honest} REFUSES {mover}'s claimed move {uci} with a GARBAGE signature; member {HUB_MEMBER} (rogue) seals it anyway — attested (existence, not validity), provably unsigned"));
        self.sealed.insert(d, block);
        self.depth = d;
        self.clock_to(self.inst.due(d) + 1);
        Ok(())
    }

    /// The mover of the next depth submits a SIGNED entry whose state is
    /// the legal successor of `uci` with the from-square byte set to 255 —
    /// an entry the client cannot decode and every kind leaf errors on (the
    /// D45 case). Honest members seal it: they check the signature, never
    /// well-formedness. The position does NOT advance.
    fn play_malformed(&mut self, uci: &str) -> Result<()> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let mut head = chess::head(GAME_ID, d as u8, mover, &new);
        head[8 + 36] = 255;
        ensure!(ChessState::from_e(head[8..48].try_into().unwrap()).is_err(), "the client rejects the entry");
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &chess::auth_message(&head))?;
        let mut entry = head.to_vec();
        for h in &sig.hashes {
            entry.extend_from_slice(h);
        }
        self.submit(entry, None, format!("{mover}'s SIGNED but MALFORMED entry ({uci} with from-square 255) — attested; the client cannot decode it"))
    }

    /// The hub's member seals the mover's `uci` at `d` LATE, after the due
    /// time passed with nothing signed attested and the members flagged it
    /// (D50's late-attestation fixture under D55): the entry is validly
    /// signed and there is no on-time block to contradict — the flags are
    /// what the contract counts. The mover's refutation reads it and names
    /// member 1 in its witness.
    fn play_late(&mut self, d: u32, uci: &str) -> Result<(ChessState, WotsSig)> {
        ensure!(d == self.depth + 1 && self.now > self.inst.due(d) && self.flags.contains_key(&d), "move {d}'s due time has passed and it was flagged");
        let mover = instance::mover_at(d);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: vec![] }))?;
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: sig.hashes.clone() }.encode();
        let late = self.miner.seal_entry(CONTRACT_ID, d, HUB_MEMBER, &entry).map_err(|e| anyhow::anyhow!(e))?;
        ensure!(self.client.observe(&late, &self.registry).map_err(|e| anyhow::anyhow!(e))? == lngap_pos::Observation::New, "the late seal is the only one at depth {d}");
        let t = self.now - self.inst.t0;
        self.say(format!("move {d} sealed LATE (t+{t}s, due t+{}s) by member {HUB_MEMBER} with {mover}'s move {uci} — the hub's member colludes; nothing contradicts it on the venue, the members' flags are the record", self.inst.due(d) - self.inst.t0));
        self.sealed.insert(d, late);
        self.state = new.clone();
        self.depth = d;
        Ok((new, sig))
    }

    /// The state-key signature over a sealed head's signed region (the D41
    /// authorship block), from that depth's mover's keystore — the same
    /// message as the published entry's, so the same signature
    /// (idempotent).
    fn auth_sig(&mut self, d: u32, head: &[u8; 48]) -> WotsSig {
        self.ks(instance::mover_at(d))
            .sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &chess::auth_message(head))
            .unwrap()
    }

    /// The mover at depth `d` plays a SECOND, conflicting move, validly
    /// signed (hand-reproduced: the honest keystore refuses), which the
    /// hub's member seals — an honest seal of a signed entry. The client
    /// sees two different heads at depth `d` (D55's equivocation): both
    /// mover-signed, so the fault is the MOVER's.
    fn double_play(&mut self, d: u32, uci: &str, prior: &ChessState) -> Result<(ChessState, WotsSig)> {
        let mover = instance::mover_at(d);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&prior.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let msg = entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: vec![] });
        ensure!(self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &msg).is_err(), "the honest keystore refuses to equivocate");
        let sig = adversarial_state_sig(&format!("pc/{}-ks", mover.name()), d, &msg);
        let entry = ChessEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, state: new.clone(), sigs: sig.hashes.clone() }.encode();
        let fork = self.miner.seal_entry(CONTRACT_ID, d, HUB_MEMBER, &entry).map_err(|e| anyhow::anyhow!(e))?;
        let member = match self.client.observe(&fork, &self.registry) {
            Ok(lngap_pos::Observation::Equivocation(e)) => e.member,
            other => anyhow::bail!("a second, different head at depth {d} is an equivocation: {other:?}"),
        };
        self.say(format!("depth {d} holds a SECOND head, sealed by member {member}: {mover}'s double-play, both entries signed by {mover} — the mover's equivocation, the members blameless"));
        Ok((new, sig))
    }

    fn skel(&self, label: &str) -> &PresignedTx {
        self.graph.iter().find(|p| p.label == label).unwrap_or_else(|| panic!("no skeleton {label}"))
    }

    /// Broadcast a pre-signed skeleton with `w`; record it; return the
    /// mined height and the new output 0's (outpoint, prevout).
    fn run(&mut self, label: &str, w: Vec<Vec<u8>>, by: Role) -> Result<(u32, OutPoint, TxOut)> {
        let p = self.skel(label);
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        self.rt.mine_with(&[tx.clone()]).map_err(|e| anyhow::anyhow!("{label} must mine: {e}"))?;
        let (h, v) = (self.rt.height()?, tx.vsize());
        self.seen.push((h, label.to_string(), tx.compute_txid(), by, v));
        self.say(format!("{by} broadcasts `{label}` ({v} vB)"));
        Ok((h, OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone()))
    }

    /// Broadcast a runtime (NOT pre-signed) transaction; record it.
    fn run_tx(&mut self, label: &str, tx: Transaction, by: Role) -> Result<u32> {
        self.rt.mine_with(&[tx.clone()]).map_err(|e| anyhow::anyhow!("{label} must mine: {e}"))?;
        let (h, v) = (self.rt.height()?, tx.vsize());
        self.seen.push((h, label.to_string(), tx.compute_txid(), by, v));
        self.say(format!("{by} broadcasts `{label}` ({v} vB)"));
        Ok(h)
    }

    /// The skeleton with the witness attached, NOT broadcast (negatives).
    fn dry(&self, label: &str, w: Vec<Vec<u8>>) -> Transaction {
        let p = self.skel(label);
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        tx
    }

    /// Both parties' signatures on the skeleton's spend (exchanged at
    /// setup), witness order `[sig_hub, sig_user]` (sig_user on top).
    fn sigs22(&self, label: &str) -> [Vec<u8>; 2] {
        let p = self.skel(label);
        let sig_u = sign_tx(&self.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&self.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        [sig_h, sig_u]
    }

    /// The claimant's absence claim at depth `d`.
    fn claim_absent(&mut self, d: u32) -> Result<(u32, OutPoint, TxOut)> {
        let claimant = instance::mover_at(d).other();
        let [sig_h, sig_u] = self.sigs22(&format!("absent_{d}"));
        self.say(format!("{claimant} claims: no valid move {d} on the venue"));
        self.run(&format!("absent_{d}"), vec![sig_h, sig_u], claimant)
    }

    /// The pair-readout witness of a refute at depth `d`, with the pair
    /// reveal (needed again by the disprove/split witnesses). The chess
    /// authorship is the NEW head's block alone (D42). With `junk` set, the
    /// block carries the entry's own garbage preimages (the PC8 negative).
    fn readout_witness(&mut self, label: &str, d: u32, junk: bool) -> Result<(Vec<Vec<u8>>, WotsSig)> {
        let (tx, prev, leaf) = {
            let p = self.skel(label);
            (p.tx.clone(), p.prevouts[0].clone(), p.leaf.script.clone())
        };
        let (prev_head, new_head) = (self.head(d - 1), self.head(d));
        let mut msg = prev_head.to_vec();
        msg.extend_from_slice(&new_head);
        let mover = instance::mover_at(d);
        let pair_sig = self.ks(mover).sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).map_err(|e| anyhow::anyhow!(e))?;
        let new_r = if junk {
            WotsSig::from_hashes(WotsParams::for_bytes(42), &chess::auth_message(&new_head), vec![[0x11; 20]; STATE_DIGITS]).unwrap()
        } else {
            self.auth_sig(d, &new_head)
        };
        let sign_at = |block: &SealedBlock| -> Vec<Vec<u8>> {
            (0..HEAD_CHUNKS).map(|j| sign_tx(&Keypair::from_secret_key(SECP256K1, &block.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect()
        };
        let sigs_new = sign_at(&self.sealed[&d]);
        let sigs_prev = sign_at(&self.sealed[&(d - 1)]);
        let mut w = refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&new_r]);
        // the proposer fragment (D53): the block's proposer scalar signs too, naming the member
        let blk = &self.sealed[&d];
        w.extend(proposer_witness(sign_tx(&Keypair::from_secret_key(SECP256K1, &blk.proposer_secret), &tx, &prev, &leaf), blk.proposer));
        Ok((w, pair_sig))
    }

    /// The depth-`d` refutation carrying the entry's own junk preimages —
    /// the PC8 negative, assembled but never broadcast.
    fn refute_junk(&mut self, d: u32) -> Result<Transaction> {
        let label = format!("absent_{d}/refute");
        let (mut w, _psig) = self.readout_witness(&label, d, true)?;
        let msig = {
            let p = self.skel(&label);
            sign_tx(self.payment(instance::mover_at(d)), &p.tx, &p.prevouts[0], &p.leaf.script)
        };
        w.push(msig);
        Ok(self.dry(&label, w))
    }

    /// The mover's counter off the depth-`d` claim output (D44): the thin
    /// claim "the claimant did not move at `d - 1`", pre-signed 2-of-2. Its
    /// output's tree is the depth-`d - 1` claim tree, so the follow-ons run
    /// at depth `d - 1` under the `absent_{d}/counter` base label.
    fn counter(&mut self, d: u32) -> Result<(u32, OutPoint, TxOut)> {
        let by = instance::mover_at(d);
        let label = format!("absent_{d}/counter");
        let [sig_h, sig_u] = self.sigs22(&label);
        self.say(format!("{by} counters: the claim at {d} was not due — no move {} on the venue", d - 1));
        self.run(&label, vec![sig_h, sig_u], by)
    }

    /// The mover's refutation at depth `d`: the readout parks the attested
    /// pair. Returns the pair reveal and the refuted output.
    fn refute(&mut self, d: u32) -> Result<(WotsSig, u32, OutPoint, TxOut)> {
        self.refute_under(d, &format!("absent_{d}"))
    }

    /// As [`ChessPosGame::refute`] under the claim-shaped output `base`
    /// (`absent_{d}`, or `absent_{d+1}/counter` — D44).
    fn refute_under(&mut self, d: u32, base: &str) -> Result<(WotsSig, u32, OutPoint, TxOut)> {
        let mover = instance::mover_at(d);
        let label = format!("{base}/refute");
        let (mut w, pair_sig) = self.readout_witness(&label, d, false)?;
        let msig = {
            let p = self.skel(&label);
            sign_tx(self.payment(mover), &p.tx, &p.prevouts[0], &p.leaf.script)
        };
        w.push(msig);
        self.say(format!("{mover} refutes: the venue attested moves {} and {d}", d - 1));
        let (h, op, prev) = self.run(&label, w, mover)?;
        Ok((pair_sig, h, op, prev))
    }

    /// Which disprove leaves fire on the attested pair at depth `d` (the
    /// native mirrors, the safety/completeness discipline's native half):
    /// `wrong_slot` on the word0s, then the twelve kinds' certificate
    /// search over the decoded positions.
    fn disproves_firing(&self, d: u32) -> Vec<String> {
        let l = self.inst.layout(d);
        let prior = self.head(d - 1);
        let new = self.head(d);
        chess::disprove_leaves(&l, &self.inst.depth_keys(d).refute)
            .into_iter()
            .filter(|pl| (pl.fires)(&prior, &new))
            .map(|pl| pl.name)
            .collect()
    }

    /// The claimant's disprove off the refuted output (a runtime
    /// transaction): the kind's exhibit (computed from the parked heads) in
    /// the sim-verified order, then the pair reveal copied from the
    /// refutation's published witness.
    fn disprove(&mut self, d: u32, pair_sig: &WotsSig, p_op: OutPoint, p_prev: &TxOut, prefer: &str) -> Result<()> {
        let firing = self.disproves_firing(d);
        ensure!(!firing.is_empty(), "some disprove must fire");
        let name = if firing.iter().any(|n| n == prefer) { prefer.to_string() } else { firing[0].clone() };
        let ctx = self.ctx();
        let p_tree = self.inst.refuted_tree(&ctx, d)?;
        let l = p_tree.leaf(&format!("disprove_{name}"))?;
        let challenger = instance::mover_at(d).other();
        let payout = self.pubs[challenger.idx()].payout_spk.clone();
        let mut tx = lngap_btc::tx::build_spend(p_op, &l.timelock, vec![TxOut { value: p_prev.value - self.params.presign_fee, script_pubkey: payout }]);
        let dsig = sign_tx(self.payment(challenger), &tx, p_prev, &l.script);
        // the exhibit for the firing kind, from the parked tuple
        let kind = chess::kinds().into_iter().find(|k| chess::leaf_name(*k) == name).expect("a kind leaf");
        let prior = ChessState::from_e(self.head(d - 1)[8..48].try_into().unwrap()).unwrap();
        let new = ChessState::from_e(self.head(d)[8..48].try_into().unwrap()).unwrap();
        let exhibit = find_kind(&prior.pos, new.mv, &new.pos, kind).map(|c| exhibit_values(c)).expect("the kind fires");
        let mut w: Vec<Vec<u8>> = exhibit.iter().map(|&v| scriptnum(v)).collect();
        w.extend(refute::wots_wire(pair_sig));
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block(&format!("disprove_{name}"))?);
        self.say(format!("{challenger} disproves the parked tuple: {name} fires"));
        self.run_tx(&format!("disprove_{name}"), tx, challenger)?;
        Ok(())
    }

    /// The claimant's exhibit-less disprove `name` off the refuted output
    /// (`wrong_slot` or `chess_malformed`, D45): the pair reveal alone,
    /// built without decoding the parked heads.
    fn disprove_bare(&mut self, d: u32, pair_sig: &WotsSig, p_op: OutPoint, p_prev: &TxOut, name: &str) -> Result<()> {
        ensure!(self.disproves_firing(d).iter().any(|n| n == name), "{name} must fire natively");
        let ctx = self.ctx();
        let p_tree = self.inst.refuted_tree(&ctx, d)?;
        let leaf = format!("disprove_{name}");
        let l = p_tree.leaf(&leaf)?;
        let challenger = instance::mover_at(d).other();
        let payout = self.pubs[challenger.idx()].payout_spk.clone();
        let mut tx = lngap_btc::tx::build_spend(p_op, &l.timelock, vec![TxOut { value: p_prev.value - self.params.presign_fee, script_pubkey: payout }]);
        let dsig = sign_tx(self.payment(challenger), &tx, p_prev, &l.script);
        let mut w = refute::wots_wire(pair_sig);
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block(&leaf)?);
        self.say(format!("{challenger} disproves the parked tuple: {name} fires"));
        self.run_tx(&leaf, tx, challenger)?;
        Ok(())
    }

    /// The claimant's `not_timely` spend off the refuted output (D50): its
    /// own transaction, signed under every flag point whose scalar the
    /// members published for depth `d` (the first `held` of them, if given);
    /// the leaf counts them against the threshold. With `broadcast` false
    /// the transaction is only assembled (negatives).
    fn not_timely(&mut self, d: u32, p_op: OutPoint, p_prev: &TxOut, held: Option<usize>, broadcast: bool) -> Result<Option<Transaction>> {
        let ctx = self.ctx();
        let p_tree = self.inst.refuted_tree(&ctx, d)?;
        let l = p_tree.leaf("not_timely")?;
        let claimant = instance::mover_at(d).other();
        let payout = self.pubs[claimant.idx()].payout_spk.clone();
        let mut tx = lngap_btc::tx::build_spend(p_op, &l.timelock, vec![TxOut { value: p_prev.value - self.params.presign_fee, script_pubkey: payout }]);
        let mut scalars = self.flags.get(&d).cloned().unwrap_or_else(|| vec![None; K]);
        if let Some(n) = held {
            // the claimant collected only the first `n` published scalars
            let mut seen = 0;
            for f in scalars.iter_mut() {
                if f.is_some() {
                    seen += 1;
                    if seen > n {
                        *f = None;
                    }
                }
            }
        }
        let held = scalars.iter().filter(|s| s.is_some()).count();
        let w = not_timely_witness(&tx, 0, std::slice::from_ref(p_prev), &l.script, self.payment(claimant), &scalars);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block("not_timely")?);
        if !broadcast {
            return Ok(Some(tx));
        }
        self.say(format!("{claimant} disproves the refutation as NOT TIMELY: {held} of {K} members flagged move {d} as not attested by its due time (threshold {T})"));
        self.run_tx("not_timely", tx, claimant)?;
        Ok(None)
    }

    /// A code-gated split spend. `base` is `absent_{d}` (the claimant's
    /// timeout split) or `absent_{d}/refuted` (the mover's self-checking
    /// split).
    fn split(&mut self, d: u32, base: &str, code: u8, pair_sig: Option<&WotsSig>) -> Result<()> {
        let name = match code {
            0 => "UserWins",
            1 => "HubWins",
            _ => "Draw",
        };
        let label = format!("{base}/split_{name}");
        match pair_sig {
            // the mover's self-checking split off the refuted output
            Some(psig) => {
                let mover = instance::mover_at(d);
                let reveal = self.ks(mover).reveal_uint(&instance::code_label(CONTRACT_ID, 1, d), u32::from(code))?;
                let p = self.skel(&label);
                let sig_u = sign_tx(&self.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
                let sig_h = sign_tx(&self.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
                let w = ttt::checked_split_witness(sig_u, sig_h, &reveal, psig);
                self.run(&label, w, mover)?;
            }
            // the claimant's timeout split off the claim output
            None => {
                let claimant = instance::mover_at(d).other();
                let reveal = self.ks(claimant).reveal_uint(&instance::ccode_label(CONTRACT_ID, 1, d), u32::from(code))?;
                let [sig_h, sig_u] = self.sigs22(&label);
                let mut w = reveal.consumption_order();
                w.reverse();
                w.push(sig_h);
                w.push(sig_u);
                self.run(&label, w, claimant)?;
            }
        }
        Ok(())
    }

    /// The equivocation exhibit (D39, D43's per-depth form): both
    /// signatures of the depth-`d` mover's state key, from the two
    /// conflicting entries.
    fn equiv_exhibit(&mut self, d: u32, _state_a: &ChessState, sig_a: &WotsSig, _state_b: &ChessState, sig_b: &WotsSig) -> Result<()> {
        let label = format!("equiv_{d}");
        let [sig_h, sig_u] = self.sigs22(&label);
        let exhibitor = instance::mover_at(d).other();
        self.say(format!("{exhibitor} exhibits the two conflicting state signatures at depth {d}"));
        let mut w = refute::wots_wire(sig_a);
        w.extend(refute::wots_wire(sig_b));
        w.push(sig_h);
        w.push(sig_u);
        self.run(&label, w, exhibitor)?;
        Ok(())
    }

    fn balances(&self) -> [Amount; 2] {
        [self.rt.balance_of(&self.pubs[0].payout_spk).unwrap(), self.rt.balance_of(&self.pubs[1].payout_spk).unwrap()]
    }
}

// ----- the suite ----

fn report(g: &ChessPosGame, sc: &Scenario) -> Report {
    println!(
        "=== {}: {:?} ({} vB in {} txs)",
        sc.id,
        g.seen.iter().map(|s| s.1.clone()).collect::<Vec<_>>(),
        g.seen.iter().map(|s| s.4).sum::<usize>(),
        g.seen.len()
    );
    Report {
        id: sc.id.into(),
        title: sc.title.into(),
        expected: sc.expected.into(),
        txs: g.seen.iter().map(|s| (s.0, s.1.clone(), s.2.to_string(), s.3.name().to_string())).collect(),
        balances: g.balances(),
        narrative: g.log.join("\n"),
    }
}

fn roles(g: &ChessPosGame) -> Vec<String> {
    g.seen.iter().map(|s| s.1.clone()).collect()
}

/// PC2/PC3's shape: the hub stalls at `d`; the user's absence claim and
/// timeout split resolve it.
fn stall(sc: &'static Scenario, d: u32, opening: &[&str]) -> Result<Report> {
    let mut g = ChessPosGame::open(sat(POT))?;
    for uci in opening {
        g.play(uci)?;
    }
    g.stall(); // the hub does not move: nothing is sealed, the members flag it
    g.wait_claim(d)?;
    let (h, _, _) = g.claim_absent(d)?;
    g.wait_to(h + u32::from(g.params.delta) + 1)?;
    g.split(d, &format!("absent_{d}"), 0, None)?;
    ensure!(roles(&g) == vec![format!("absent_{d}"), format!("absent_{d}/split_UserWins")], "{:?}", roles(&g));
    ensure!(g.balances() == [sat(POT - 2 * FEE), sat(0)], "{:?}", g.balances());
    Ok(report(&g, sc))
}

pub const PC1: Scenario = Scenario {
    id: "PC1",
    title: "PoS graph, chess: cooperative game, nothing on Bitcoin",
    expected: "fool's mate on the PoS venue, each entry's signature verified against the mover's per-depth key; no Bitcoin transaction; 129 pre-signed transactions at open (D43's per-depth equiv leaves, D44's counters)",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        for uci in ["f2f3", "e7e5", "g2g4", "d8h4"] {
            g.play(uci)?;
        }
        ensure!(g.depth == 4 && lngap_chess::terminal(&g.state.pos).is_some(), "fool's mate is terminal at depth 4");
        ensure!(g.seen.is_empty(), "nothing on Bitcoin");
        Ok(report(&g, &PC1))
    },
};

pub const PC2: Scenario = Scenario {
    id: "PC2",
    title: "PoS graph, chess: the hub stalls at move 2",
    expected: "the absence claim and the timeout split: two transactions, under 600 vB in all",
    run: || stall(&PC2, 2, &["e2e4"]),
};

pub const PC3: Scenario = Scenario {
    id: "PC3",
    title: "PoS graph, chess: the hub stalls at move 6",
    expected: "the same two transactions through the depth-6 leaves (1. e4 e5 2. Nf3 Nc6 3. Bc4, then nothing)",
    run: || stall(&PC3, 6, &["e2e4", "e7e5", "g1f3", "b8c6", "f1c4"]),
};

pub const PC4: Scenario = Scenario {
    id: "PC4",
    title: "PoS graph, chess: the loser refuses the fold — the mated side's absence resolves (D42)",
    expected: "fool's mate: the hub mates at depth 4; nothing is sealed at depth 5 (the mated user has no legal move); the hub's absence claim is UNANSWERABLE and the timeout split pays HubWins — the terminal path needs no exhibit family: two transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        for uci in ["f2f3", "e7e5", "g2g4", "d8h4"] {
            g.play(uci)?;
        }
        ensure!(lngap_chess::terminal(&g.state.pos).is_some(), "the game is over on the venue");
        g.stall(); // the mated user has no move 5: nothing is sealed
        g.wait_claim(5)?;
        let (h, _, _) = g.claim_absent(5)?; // the hub claims: the user is mated, no move exists
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(5, "absent_5", 1, None)?; // the hub's timeout code: HubWins
        ensure!(roles(&g) == vec!["absent_5".to_string(), "absent_5/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 2 * FEE)], "{:?}", g.balances());
        Ok(report(&g, &PC4))
    },
};

pub const PC5: Scenario = Scenario {
    id: "PC5",
    title: "PoS graph, chess: a spurious absence claim forfeits the claimant",
    expected: "the hub's move 2 (e7e5) is on the venue; the user claims absence anyway; the hub's refutation parks the legal pair, no disprove fires, and the mover's self-checking split pays HubWins (R: the side to move — white — forfeits): three transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        g.play("e7e5")?; // the hub DID publish move 2
        g.wait_claim(2)?;
        g.claim_absent(2)?; // the user's spurious claim
        let (psig, h, _, _) = g.refute(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_2/refuted", 1, Some(&psig))?; // R: white to move forfeits -> HubWins
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/refute".to_string(), "absent_2/refuted/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 3 * FEE)], "{:?}", g.balances());
        Ok(report(&g, &PC5))
    },
};

pub const PC6: Scenario = Scenario {
    id: "PC6",
    title: "PoS graph, chess: an illegal move is disproved off the refutation",
    expected: "the hub plays c8e6 at move 2 — a bishop jumping the d7 pawn (attested, not legal); the user's absence claim is refuted, and the disprove of the parked pair fires chess_ray: three transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        g.play_invalid("c8e6")?; // the hub's bishop jumps its own pawn
        g.wait_claim(2)?;
        g.claim_absent(2)?;
        let (psig, h, p_op, p_prev) = g.refute(2)?;
        let firing = g.disproves_firing(2);
        ensure!(firing.iter().any(|n| n == "chess_ray"), "{firing:?}");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.disprove(2, &psig, p_op, &p_prev, "chess_ray")?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/refute".to_string(), "disprove_chess_ray".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 3 * FEE), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PC6))
    },
};

pub const PC7: Scenario = Scenario {
    id: "PC7",
    title: "PoS graph, chess: a double-played depth (the mover's double-sign) pays the victim",
    expected: "the hub signs two conflicting moves at depth 2 (e7e5 and c7c5) and both are sealed (each validly signed: the members are blameless; the client sees two heads at one depth); the user exhibits both signatures of the hub's depth-2 state key (equiv_2, the per-depth D43 form) and takes the pot: one transaction",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        let prior = g.state.clone();
        let (state_a, sig_a) = g.play("e7e5")?; // honestly signed
        let (state_b, sig_b) = g.double_play(2, "c7c5", &prior)?; // the second signed head
        g.wait_claim(2)?;
        g.equiv_exhibit(2, &state_a, &sig_a, &state_b, &sig_b)?;
        ensure!(roles(&g) == ["equiv_2".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - FEE), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PC7))
    },
};

pub const PC8: Scenario = Scenario {
    id: "PC8",
    title: "PoS graph, chess: a garbage-signed attested entry is not a move (D41)",
    expected: "a legal-looking e7e5 at depth 2 whose preimages open no key is refused by the honest members (D55) and sealed by a rogue member (provable misbehaviour); the hub declines to adopt it (its state key never signed that state); a refutation carrying the entry's own junk preimages fails the authorship fragment; the absence claim and the timeout split pay the user",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?; // really signed
        g.play_garbage_signed("e7e5")?; // depth 2: e7e5 claimed, junk signature, a rogue seal
        g.wait_claim(2)?;
        let (h, _, _) = g.claim_absent(2)?;
        let bad = g.refute_junk(2)?;
        ensure!(g.rt.test_accept(&bad).is_err(), "junk preimages must fail the authorship fragment");
        g.say("the hub's would-be refutation over the garbage-signed entry: rejected by the authorship fragment, never confirmed".to_string());
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(2, "absent_2", 0, None)?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 2 * FEE), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PC8))
    },
};

pub const PC9: Scenario = Scenario {
    id: "PC9",
    title: "PoS graph, chess: the mated side's illegal answer is disproved (the 2-element exhibit)",
    expected: "fool's mate, then the mated user 'answers' g4g5 as move 5 (the king still attacked); the hub's absence claim is refuted over the illegal pair, and the hub's disprove fires chess_kingattacked — a two-element exhibit: three transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        for uci in ["f2f3", "e7e5", "g2g4", "d8h4"] {
            g.play(uci)?;
        }
        ensure!(lngap_chess::terminal(&g.state.pos).is_some(), "terminal at depth 4");
        g.play_invalid("g4g5")?; // the mated user's illegal answer as move 5
        g.wait_claim(5)?;
        g.claim_absent(5)?;
        let (psig, h, p_op, p_prev) = g.refute(5)?;
        let firing = g.disproves_firing(5);
        ensure!(firing.iter().any(|n| n == "chess_kingattacked"), "{firing:?}");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.disprove(5, &psig, p_op, &p_prev, "chess_kingattacked")?;
        ensure!(roles(&g) == vec!["absent_5".to_string(), "absent_5/refute".to_string(), "disprove_chess_kingattacked".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 3 * FEE)], "{:?}", g.balances());
        Ok(report(&g, &PC9))
    },
};

pub const PC10: Scenario = Scenario {
    id: "PC10",
    title: "PoS graph, chess: the staller claims one depth AHEAD — countered (D44)",
    expected: "the hub stalls at move 2, then claims absence at 3 ('the user did not move at 3' — vacuously true, the user's turn never came); the user's counter ('you did not move at 2') has no defence — nothing is attested at depth 2, so no refutation exists — and the user's timeout split off the counter output pays: three transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        g.stall(); // the hub does not move 2: nothing is sealed
        g.wait_claim(3)?;
        g.claim_absent(3)?; // the staller's vacuous claim at 3
        let (h, _, _) = g.counter(3)?;
        g.say("the hub cannot defend the counter: nothing is attested at depth 2 (D55: no empty seals — there is nothing to read out)".to_string());
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(2, "absent_3/counter", 0, None)?;
        ensure!(roles(&g) == vec!["absent_3".to_string(), "absent_3/counter".to_string(), "absent_3/counter/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 3 * FEE), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PC10))
    },
};

pub const PC11: Scenario = Scenario {
    id: "PC11",
    title: "PoS graph, chess: a false counter to a due claim is refuted (D44)",
    expected: "the hub's e7e5 is on the venue at depth 2; the user stalls at 3; the hub's absence claim at 3 is due; the user counters anyway ('you did not move at 2' — false); the hub refutes on the counter output with the (1, 2) pair readout, no disprove fires, and the hub's self-checking split pays R(parked) = HubWins (white to move forfeits): four transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        g.play("e7e5")?; // the hub DID publish move 2
        g.stall(); // the user stalls at 3
        g.wait_claim(3)?;
        g.claim_absent(3)?; // due
        g.counter(3)?; // the user's false counter
        let (psig, h, _, _) = g.refute_under(2, "absent_3/counter")?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_3/counter/refuted", 1, Some(&psig))?; // R: white to move forfeits -> HubWins
        ensure!(roles(&g) == vec!["absent_3".to_string(), "absent_3/counter".to_string(), "absent_3/counter/refute".to_string(), "absent_3/counter/refuted/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 4 * FEE)], "{:?}", g.balances());
        Ok(report(&g, &PC11))
    },
};

pub const PC12: Scenario = Scenario {
    id: "PC12",
    title: "PoS graph, chess: a malformed signed entry is disproved (D45)",
    expected: "the hub submits a SIGNED entry at depth 2 whose state has from-square 255 (sealed: members check the signature, never well-formedness) — undecodable by the client, and every kind leaf's board read errors on it (before D45 no disprove could touch it and the hub's checked split took the pot); the user claims absence, the hub refutes, and the user's chess_malformed disprove takes the pot: three transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        g.play_malformed("e7e5")?; // depth 2: signed, attested, malformed
        g.wait_claim(2)?;
        g.claim_absent(2)?;
        let (psig, h, p_op, p_prev) = g.refute(2)?;
        let firing = g.disproves_firing(2);
        ensure!(firing.iter().any(|n| n == chess::MALFORMED), "{firing:?}");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.disprove_bare(2, &psig, p_op, &p_prev, chess::MALFORMED)?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/refute".to_string(), "disprove_chess_malformed".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 3 * FEE), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PC12))
    },
};

pub const PC13: Scenario = Scenario {
    id: "PC13",
    title: "PoS graph, chess: a LATE attestation is killed by the timeliness flags (D50)",
    expected: "the hub does not move 2 (nothing sealed on time); at the due time the members publish their flag scalars; the hub's member, colluding, then seals the hub's signed e7e5 late (nothing contradicts it on the venue); the user claims absence, the hub refutes with the late block (the readout passes, the move is legal, no tuple disprove fires), and the user's not_timely spend — its own transaction signed under 3 of the 5 members' flag points (the majority) — takes the pot; with 2 flags the leaf rejects it: three transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        g.stall(); // the hub does not move 2: nothing sealed on time, the members flag it
        g.play_late(2, "e7e5")?; // ...the hub's member seals the hub's move late anyway
        g.wait_claim(2)?;
        g.claim_absent(2)?;
        let (_psig, h, p_op, p_prev) = g.refute(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the late move is legal: no tuple disprove fires");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        // two flags do not reach the threshold
        let short = g.not_timely(2, p_op, &p_prev, Some(2), false)?.expect("assembled");
        ensure!(g.rt.test_accept(&short).is_err(), "not_timely must not fire under the threshold");
        g.say("the user's not_timely with 2 of 5 flags: rejected in-leaf (threshold 3), never confirmed".to_string());
        // a third member's flag: the refutation dies
        g.not_timely(2, p_op, &p_prev, Some(3), true)?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/refute".to_string(), "not_timely".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 3 * FEE), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PC13))
    },
};

pub const PC14: Scenario = Scenario {
    id: "PC14",
    title: "PoS graph, chess: a silent designated sealer does not stall the mover — the next member in the rotation seals (D53, D55)",
    expected: "the designated sealer for depth 2 (the rotation) is silent; after the backoff the hub resubmits its e7e5 to the next member in the rotation, which seals it; the user's spurious absence claim is refuted with that seal — the refutation's witness names its member through the proposer fragment — no disprove fires, and the hub's self-checking split pays HubWins: three transactions; the silent member cost nothing",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        let designated = lngap_pos::rotation(CONTRACT_ID, 2, K);
        g.miner.silence(designated); // depth 2's designated sealer goes silent
        g.play("e7e5")?; // resubmitted to, and sealed by, the next member
        ensure!(g.sealed[&2].proposer == (designated + 1) % K, "the mover fell back to the next member in the rotation");
        g.wait_claim(2)?;
        g.claim_absent(2)?; // the user's spurious claim
        let (psig, h, _, _) = g.refute(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_2/refuted", 1, Some(&psig))?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/refute".to_string(), "absent_2/refuted/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 3 * FEE)], "{:?}", g.balances());
        Ok(report(&g, &PC14))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![
        PC1, PC2, PC3, PC4, PC5, PC6, PC7, PC8, PC9, PC10, PC11, PC12, PC13, PC14,
    ]
}
