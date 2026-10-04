//! The PoS absence-claim graph's scenario suite (POS_FACTCHAIN_PLAN.md step
//! 7; D40; PS12 the D50 timeliness flag): PS1-PS8, the PoS analogues of the S1-S9 stall suite
//! (fc_stall.rs), on the wired `lngap-pos` graph with REAL signed venue
//! entries (the per-depth state key signs the state; the D39 equivocation
//! exhibits consume those reveals).
//!
//! Unlike the S-suite these scenarios run WITHOUT the channel wrapper: the
//! contract output C is funded directly and the pre-signed graph is played
//! by hand — the party policies that would file these spends reactively
//! remain deferred (D39's list), and the force-close commitment (~240 vB,
//! unchanged by the venue swap) is excluded from the transaction tables.
//! PS9 of the plan's list (a garbage-signed attested entry) has no
//! resolution path — the PoS sig exhibit is deferred (D39) — so it is
//! documented in D40, not run.
//!
//! The reference game is the S-suite's: user X, hub O, 4, 1, 0, 8, 6, 3, 2
//! — X wins at move 7. Since D55 the venue attests entries keyed by
//! (contract, depth), sealed on submission by the designated member (the
//! rotation); there are no slots and no empty seals. The world keeps a
//! wall clock: move `d` is due at `t0 + d·60 s`, the members flag a due
//! move with no signed entry, and a claim waits for median-time-past to
//! pass the due time plus the 60 s margin.

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
use lngap_contract::Contract;
use lngap_factchain::slot::SlotEntry;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsParams, WotsPublic, WotsSig};
use lngap_pos::graph::{not_timely_witness, proposer_witness};
use lngap_pos::instance::{self, GameClock, PosInstance};
use lngap_pos::rebut::{self, HEAD_CHUNK_START, HEAD_CHUNKS};
use lngap_pos::ttt;
use lngap_pos::{Member, PosClient, PosMiner, Registry, SealedBlock};
use lngap_tictactoe::{Board, TicTacToe, OPEN};

use super::{Report, Scenario};

/// The roster's base seed: member `i` is seeded `SEED[0] + i`.
const SEED: [u8; 32] = [0x77; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
const MAX_DEPTH: u32 = 9;
/// Seconds per move (D55's `ell`) and the claim margin `m`.
const ELL: u32 = 60;
const MARGIN: u32 = 60;
const POT: u64 = 200_000;
/// The skeleton count at open: settle + 9x(claim, rebut, 3+3 splits) +
/// 5x(exhibit, 3 splits) + 9 per-depth equiv leaves (D43) + 8x(counter,
/// rebut, 3+3 splits) (D44).
const GRAPH_LEN: usize = 166;
/// The state key's reveal length (the tied-WOTS authorship: 6 message + 2
/// checksum digits over the 3 state bytes).
const STATE_DIGITS: usize = 8;
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


fn state_bits(b: &Board) -> Vec<bool> {
    TicTacToe.state_bits(b)
}

/// The authorship message of an entry carrying `state` (D43: the 3 state
/// bytes, big-endian).
fn entry_msg(state: u32) -> Vec<u8> {
    state.to_be_bytes()[1..].to_vec()
}

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
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
    ks.generate_wots(&label, 3).unwrap();
    ks.sign_wots(&label, msg).unwrap()
}

/// One PoS-venue game with its contract funded on a fresh regtest: the
/// draft (both keystores' offers), the venue with the contract registered
/// (D55: attestations keyed by (contract, depth)), C funded, the
/// 166-skeleton graph pre-signed. The world keeps a wall clock (`now`,
/// unix seconds) from which the moves' due times, the members' flags and
/// the claims' median-time-past locks are read.
struct PosGame {
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
    /// The seal the rebuttals read, by depth.
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
    board: Board,
    depth: u32,
    /// The world's wall clock (unix seconds).
    now: u32,
    btc_open: u32,
    /// (height, role, txid, broadcaster, vsize) of each broadcast.
    seen: Vec<(u32, String, Txid, Role, usize)>,
    log: Vec<String>,
}

impl PosGame {
    fn open(value: Amount) -> Result<PosGame> {
        PosGame::open_with_deposit(value, Amount::ZERO)
    }

    /// A game whose contract value is `stakes` plus a dispute deposit `d`
    /// from each side (D56).
    fn open_with_deposit(stakes: Amount, d: Amount) -> Result<PosGame> {
        let value = stakes + d * 2;
        let rt = Regtest::start()?;
        let mut miner = PosMiner::new(SEED, members());
        let registry = miner.registry(CONTRACT_ID, MAX_DEPTH)?;
        ensure!(registry.threshold == T && registry.n() == K, "the PoC threshold is the majority of the roster");
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("ps/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("ps/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("ps/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("ps/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH, instance::Game::Ttt)?;
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH, instance::Game::Ttt)?;
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH)?;
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH)?;
        ensure!(keys_u == keys_h, "the merged key sets must agree");
        // the game's clock (D55): move d is due at t0 + d·ELL; its claim is
        // valid from the due time plus MARGIN against median-time-past
        let t0 = rt.mtp()?;
        let clock = GameClock { t0, ell: ELL, margin: MARGIN };
        let deadline = t0 + 100_000;
        let btc_open = rt.height()? + 1;
        let inst = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, instance::Game::Ttt, clock, keys_u, registry.clone())?.with_deposit(d)?;
        miner.register(CONTRACT_ID, MAX_DEPTH, inst.authorship()).map_err(|e| anyhow::anyhow!(e))?;
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
        let pubs = [user.public(), hub.public()];
        let mut venue_commits = HashMap::new();
        for d in 1..=MAX_DEPTH {
            let ks = if instance::mover_at(d) == Role::User { &mut user_ks } else { &mut hub_ks };
            venue_commits.insert(d, ks.wots_public(&instance::state_label(CONTRACT_ID, 1, d))?);
        }
        let mut g = PosGame {
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
            board: Board::empty(),
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
        ensure!(g.graph.len() == GRAPH_LEN, "the wired graph: settle + 9x(claim, rebut, 3+3 splits) + 5x(exhibit, 3 splits) + 9 per-depth equiv (D43) + 8x(counter, rebut, 3+3 splits) (D44)");
        if g.inst.deposit > Amount::ZERO {
            g.say(format!("each side's dispute deposit: {} sat inside the contract (D56): returned by cooperative settlement, paid to the winner of an on-chain dispute", g.inst.deposit.to_sat()));
        }
        g.say(format!("game opened: contract {CONTRACT_ID}, pot {} sat; {GRAPH_LEN} pre-signed transactions; a move every {ELL} s, claims {MARGIN} s after a move's due time", g.inst.value.to_sat()));
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
    /// owes: each depth up to the owed move whose due time has passed with
    /// no attested, mover-signed entry is flagged by every non-silent
    /// member, once (D50, D55).
    fn clock_to(&mut self, t: u32) {
        self.now = self.now.max(t);
        let owed = if self.board.status == OPEN { self.depth + 1 } else { self.depth };
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

    /// The mover submits its signed entry for the next depth to the
    /// designated sealer (the rotation, skipping silent members — the
    /// mover's fallback after the backoff); the seal is verified natively
    /// as anyone would, and the entry's signature checked against the
    /// mover's pinned key. `valid` says whether the board advances.
    fn submit(&mut self, entry: SlotEntry, new: Board, valid: bool) -> Result<()> {
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
        let block = self.miner.seal_entry(CONTRACT_ID, d, sealer, &entry.encode()).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &self.registry).map_err(|e| anyhow::anyhow!(e))?;
        ensure!(rebut::check_entry_sig(&self.venue_commits[&d], &entry_msg(entry.state), &entry.sigs), "depth {d}: the entry does not open the mover's state key");
        self.sealed.insert(d, block);
        if valid {
            self.board = new;
        }
        self.depth = d;
        let b = self.board.render();
        self.say(format!("move {d} sealed by member {sealer} on submission ({}'s move, {b}); attested, the signature opens the key", instance::mover_at(d)));
        Ok(())
    }

    /// The mover of the next depth plays `mv` (legal), signed for real.
    /// Returns the new board and the state signature (evidence material).
    fn play(&mut self, mv: u8) -> Result<(Board, WotsSig)> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let new = TicTacToe.transition(&self.board, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(lngap_lamport::bits_to_uint(&state_bits(&new))))?;
        let entry = SlotEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: sig.hashes.clone() };
        self.submit(entry, new.clone(), true)?;
        Ok((new, sig))
    }

    /// The mover of the next depth stalls: nothing is submitted, the clock
    /// passes the move's due time, and the members flag it.
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

    /// Wait until a depth-`d` claim/exhibit is valid: the broadcaster's
    /// to_self_delay on the contract output, and median-time-past past the
    /// claim time (the world clock follows; the members flag what is due).
    fn wait_claim(&mut self, d: u32) -> Result<()> {
        self.wait_to(self.btc_open + self.params.to_self_delay as u32)?;
        let t = self.inst.claim_from(d);
        self.rt.make_time_final(t)?;
        self.clock_to(t + 1);
        Ok(())
    }

    /// The mover of the next depth plays `mv` onto an OCCUPIED cell, the
    /// naive overwrite, signed over the CLAIMED state (validly signed
    /// garbage: the venue checks authorship, never legality; the disprove
    /// family judges the transition).
    fn play_invalid(&mut self, mv: u8) -> Result<()> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let mut new = self.board.clone();
        new.cells[mv as usize] = if mover == Role::User { 1 } else { 2 };
        new.turn = mover.other();
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(lngap_lamport::bits_to_uint(&state_bits(&new))))?;
        let entry = SlotEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: sig.hashes.clone() };
        self.submit(entry, new, true)?;
        self.say(format!("depth {d} holds {mover}'s move {mv} onto an occupied cell — attested, NOT legal"));
        Ok(())
    }

    /// The mover plays `mv` legally but claims a TERMINAL status the board
    /// does not have (validly signed; `status_mismatch`'s case).
    fn play_fabricated_terminal(&mut self, mv: u8, false_status: u8) -> Result<()> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let mut new = TicTacToe.transition(&self.board, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        new.status = false_status;
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(lngap_lamport::bits_to_uint(&state_bits(&new))))?;
        let entry = SlotEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: sig.hashes.clone() };
        self.submit(entry, new, true)?;
        self.say(format!("depth {d} holds {mover}'s move {mv} claiming a fabricated terminal status — attested, NOT honest"));
        Ok(())
    }

    /// An entry for the next depth claiming `mv` with a GARBAGE sigs region
    /// (D41's PS9): honest members refuse it (D55: members seal only
    /// mover-signed entries); a ROGUE member (the hub's) seals it anyway —
    /// provable misbehaviour, and inert in the contract (the authorship
    /// fragment). The board does NOT advance, and the members still flag
    /// the depth at its due time (junk is not a signed entry).
    fn play_garbage_signed(&mut self, mv: u8) -> Result<()> {
        let d = self.depth + 1;
        let mover = instance::mover_at(d);
        let new = TicTacToe.transition(&self.board, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        let entry = SlotEntry {
            game_id: GAME_ID,
            depth: d as u8,
            mover: mover.idx() as u8,
            mv,
            state: lngap_lamport::bits_to_uint(&state_bits(&new)),
            sigs: vec![[0x11; 20]; STATE_DIGITS],
        };
        self.clock_to(self.inst.due(d - 1) + 10);
        let honest = self.miner.default_sealer(CONTRACT_ID, d).expect("a live member");
        let refused = self.miner.seal_entry(CONTRACT_ID, d, honest, &entry.encode()).err().unwrap_or_default();
        ensure!(refused.contains("refuses"), "an honest member refuses the unsigned entry: {refused}");
        let block = self.miner.seal_unchecked(CONTRACT_ID, d, HUB_MEMBER, &entry.encode()).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &self.registry).map_err(|e| anyhow::anyhow!(e))?;
        self.say(format!("depth {d}: member {honest} REFUSES {mover}'s claimed move {mv} with a GARBAGE signature; member {HUB_MEMBER} (rogue) seals it anyway — attested (existence, not validity), provably unsigned, and anyone sees it opens no key"));
        self.sealed.insert(d, block);
        self.depth = d;
        self.clock_to(self.inst.due(d) + 1);
        Ok(())
    }

    /// The hub's member seals the mover's `mv` at `d` LATE, after the due
    /// time passed with nothing signed attested and the members flagged it
    /// (D50's late-attestation fixture under D55): the entry is validly
    /// signed, so the seal itself is unremarkable — there is no on-time
    /// block to contradict — and the flags are what the contract counts.
    /// The mover's rebuttal reads it and names member 1 in its witness.
    fn play_late(&mut self, d: u32, mv: u8) -> Result<(Board, WotsSig)> {
        ensure!(d == self.depth + 1 && self.now > self.inst.due(d) && self.flags.contains_key(&d), "move {d}'s due time has passed and it was flagged");
        let mover = instance::mover_at(d);
        let new = TicTacToe.transition(&self.board, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        let sig = self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &entry_msg(lngap_lamport::bits_to_uint(&state_bits(&new))))?;
        let entry = SlotEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: sig.hashes.clone() }.encode();
        let late = self.miner.seal_entry(CONTRACT_ID, d, HUB_MEMBER, &entry).map_err(|e| anyhow::anyhow!(e))?;
        ensure!(self.client.observe(&late, &self.registry).map_err(|e| anyhow::anyhow!(e))? == lngap_pos::Observation::New, "the late seal is the only one at depth {d}");
        let b = new.render();
        let t = self.now - self.inst.t0;
        self.say(format!("move {d} sealed LATE (t+{t}s, due t+{}s) by member {HUB_MEMBER} with {mover}'s move {mv} ({b}) — the hub's member colludes; nothing contradicts it on the venue, the members' flags are the record", self.inst.due(d) - self.inst.t0));
        self.sealed.insert(d, late);
        self.board = new.clone();
        self.depth = d;
        Ok((new, sig))
    }

    /// The state-key signature over a sealed head's signed region (the D41
    /// authorship block), from that depth's mover's keystore — the same
    /// message as the published entry's, so the same signature
    /// (idempotent).
    fn auth_sig(&mut self, d: u32, head: &[u8; 48]) -> WotsSig {
        self.ks(instance::mover_at(d))
            .sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &ttt::auth_message(head))
            .unwrap()
    }

    /// The mover at depth `d` plays a SECOND, conflicting move, validly
    /// signed (hand-reproduced: the honest keystore refuses), submitted to
    /// the hub's member, which seals it — an honest seal of a signed entry.
    /// The client sees two different heads at depth `d` (D55's
    /// equivocation): both mover-signed, so the fault is the MOVER's.
    fn double_play(&mut self, d: u32, mv: u8, prior: &Board) -> Result<(Board, WotsSig)> {
        let mover = instance::mover_at(d);
        let new = TicTacToe.transition(prior, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        let msg = entry_msg(lngap_lamport::bits_to_uint(&state_bits(&new)));
        ensure!(self.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &msg).is_err(), "the honest keystore refuses to equivocate");
        let sig = adversarial_state_sig(&format!("ps/{}-ks", mover.name().to_lowercase()), d, &msg);
        let entry = SlotEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: sig.hashes.clone() }.encode();
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

    /// The pair-readout witness of a rebut/exhibit at depth `d`, with the
    /// pair reveal (needed again by the disprove/split witnesses). With
    /// `junk` set, the authorship blocks carry the entry's own garbage
    /// preimages instead of the movers' reveals (the PS9 negative).
    fn readout_witness(&mut self, label: &str, d: u32, junk: bool) -> Result<(Vec<Vec<u8>>, WotsSig)> {
        let (tx, prev, leaf) = {
            let p = self.skel(label);
            (p.tx.clone(), p.prevouts[0].clone(), p.leaf.script.clone())
        };
        let (prev_head, new_head) = (self.head(d - 1), self.head(d));
        let mut msg = prev_head.to_vec();
        msg.extend_from_slice(&new_head);
        let mover = instance::mover_at(d);
        let pair_sig = self.ks(mover).sign_wots(&instance::rebut_label(CONTRACT_ID, 1, d), &msg).map_err(|e| anyhow::anyhow!("{e}"))?;
        let mk_junk = |head: &[u8; 48]| WotsSig::from_hashes(WotsParams::for_bytes(3), &ttt::auth_message(head), vec![[0x11; 20]; STATE_DIGITS]).unwrap();
        let (prev_r, new_r) = if junk { (mk_junk(&prev_head), mk_junk(&new_head)) } else { (self.auth_sig(d - 1, &prev_head), self.auth_sig(d, &new_head)) };
        let sign_at = |block: &SealedBlock| -> Vec<Vec<u8>> {
            (0..HEAD_CHUNKS).map(|j| sign_tx(&Keypair::from_secret_key(SECP256K1, &block.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect()
        };
        let sigs_new = sign_at(&self.sealed[&d]);
        // the exhibit still reads both heads out; a rebuttal reads the new
        // head alone, the prior bound by the claimant's signature
        let mut w = if label.starts_with("exhibit") {
            let sigs_prev = sign_at(&self.sealed[&(d - 1)]);
            rebut::rebut_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&new_r, &prev_r])
        } else {
            rebut::rebut_witness_pair_signed(&sigs_new, &pair_sig, [&new_r, &prev_r])
        };
        // the proposer fragment (D53): the block's proposer scalar signs too, naming the member
        let blk = &self.sealed[&d];
        w.extend(proposer_witness(sign_tx(&Keypair::from_secret_key(SECP256K1, &blk.proposer_secret), &tx, &prev, &leaf), blk.proposer));
        Ok((w, pair_sig))
    }

    /// The depth-`d` rebuttal carrying the entry's own junk preimages —
    /// the PS9 negative, assembled but never broadcast.
    fn rebut_junk(&mut self, d: u32) -> Result<Transaction> {
        let label = format!("absent_{d}/rebut");
        let (mut w, _psig) = self.readout_witness(&label, d, true)?;
        // the rebuttal is 2-of-2: the pre-signed skeleton, both signatures
        let [sig_h, sig_u] = self.sigs22(&label);
        w.push(sig_h);
        w.push(sig_u);
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

    /// The mover's rebuttal at depth `d`: the readout parks the attested
    /// pair. Returns the pair reveal and the rebuttal output.
    fn rebut(&mut self, d: u32) -> Result<(WotsSig, u32, OutPoint, TxOut)> {
        self.rebut_under(d, &format!("absent_{d}"))
    }

    /// As [`PosGame::rebut`] under the claim-shaped output `base`
    /// (`absent_{d}`, or `absent_{d+1}/counter` — D44).
    fn rebut_under(&mut self, d: u32, base: &str) -> Result<(WotsSig, u32, OutPoint, TxOut)> {
        let mover = instance::mover_at(d);
        let label = format!("{base}/rebut");
        let (mut w, pair_sig) = self.readout_witness(&label, d, false)?;
        // the rebuttal is 2-of-2: the pre-signed skeleton, both signatures
        let [sig_h, sig_u] = self.sigs22(&label);
        w.push(sig_h);
        w.push(sig_u);
        self.say(format!("{mover} rebuts: the venue attested moves {} and {d}", d - 1));
        let (h, op, prev) = self.run(&label, w, mover)?;
        Ok((pair_sig, h, op, prev))
    }

    /// The mover's terminal exhibit at depth `d` (D37). Returns the pair
    /// reveal and the exhibit output.
    fn exhibit(&mut self, d: u32) -> Result<(WotsSig, u32, OutPoint, TxOut)> {
        let mover = instance::mover_at(d);
        let label = format!("exhibit_{d}");
        let (mut w, pair_sig) = self.readout_witness(&label, d, false)?;
        let [sig_h, sig_u] = self.sigs22(&label);
        w.push(sig_h);
        w.push(sig_u);
        self.say(format!("{mover} exhibits the attested terminal pair at depth {d}"));
        let (h, op, prev) = self.run(&label, w, mover)?;
        Ok((pair_sig, h, op, prev))
    }

    /// Which disprove leaves fire on the attested pair at depth `d` (the
    /// native mirrors, the safety/completeness discipline's native half).
    fn disproves_firing(&self, d: u32) -> Vec<String> {
        let l = self.inst.layout(d);
        let prior = self.head(d - 1);
        let new = self.head(d);
        ttt::disprove_leaves(&l, &self.inst.depth_keys(d).rebut)
            .into_iter()
            .filter(|pl| (pl.fires)(&prior, &new))
            .map(|pl| pl.name)
            .collect()
    }

    /// The claimant's disprove off the rebuttal/exhibit output (a runtime
    /// transaction: the witness copies the pair reveal from the rebuttal's
    /// published witness).
    fn disprove(&mut self, d: u32, pair_sig: &WotsSig, p_op: OutPoint, p_prev: &TxOut, prefer: &str) -> Result<()> {
        let firing = self.disproves_firing(d);
        ensure!(!firing.is_empty(), "some disprove must fire");
        let name = if firing.iter().any(|n| n == prefer) { prefer.to_string() } else { firing[0].clone() };
        let ctx = self.ctx();
        let p_tree = self.inst.rebuttal_tree(&ctx, d)?;
        let l = p_tree.leaf(&format!("disprove_{name}"))?;
        let challenger = instance::mover_at(d).other();
        let payout = self.pubs[challenger.idx()].payout_spk.clone();
        let mut tx = lngap_btc::tx::build_spend(p_op, &l.timelock, vec![TxOut { value: p_prev.value - self.params.presign_fee, script_pubkey: payout }]);
        let dsig = sign_tx(self.payment(challenger), &tx, p_prev, &l.script);
        let mut w = rebut::wots_wire(pair_sig);
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block(&format!("disprove_{name}"))?);
        self.say(format!("{challenger} disproves the parked tuple: {name} fires"));
        self.run_tx(&format!("disprove_{name}"), tx, challenger)?;
        Ok(())
    }

    /// The claimant's `not_timely` spend off the rebuttal output (D50): its
    /// own transaction, signed under every flag point whose scalar the
    /// members published for depth `d` (the first `held` of them, if given);
    /// the leaf counts them against the threshold. With `broadcast` false
    /// the transaction is only assembled (negatives).
    fn not_timely(&mut self, d: u32, p_op: OutPoint, p_prev: &TxOut, held: Option<usize>, broadcast: bool) -> Result<Option<Transaction>> {
        let ctx = self.ctx();
        let p_tree = self.inst.rebuttal_tree(&ctx, d)?;
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
        self.say(format!("{claimant} disproves the rebuttal as NOT TIMELY: {held} of {K} members flagged move {d} as not attested by its due time (threshold {T})"));
        self.run_tx("not_timely", tx, claimant)?;
        Ok(None)
    }

    /// A code-gated split spend. `base` is `absent_{d}` (the claimant's
    /// timeout split) or `absent_{d}/rebuttal` / `exhibit_{d}` (the mover's
    /// self-checking split).
    fn split(&mut self, d: u32, base: &str, code: u8, pair_sig: Option<&WotsSig>) -> Result<()> {
        let name = match code {
            0 => "UserWins",
            1 => "HubWins",
            _ => "Draw",
        };
        let label = format!("{base}/split_{name}");
        match pair_sig {
            // the mover's self-checking split off the rebuttal/exhibit output
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
    fn equiv_exhibit(&mut self, d: u32, _board_a: &Board, sig_a: &WotsSig, _board_b: &Board, sig_b: &WotsSig) -> Result<()> {
        let label = format!("equiv_{d}");
        let [sig_h, sig_u] = self.sigs22(&label);
        let exhibitor = instance::mover_at(d).other();
        self.say(format!("{exhibitor} exhibits the two conflicting state signatures at depth {d}"));
        let mut w = rebut::wots_wire(sig_a);
        w.extend(rebut::wots_wire(sig_b));
        w.push(sig_h);
        w.push(sig_u);
        self.run(&label, w, exhibitor)?;
        Ok(())
    }

    fn balances(&self) -> [Amount; 2] {
        [self.rt.balance_of(&self.pubs[0].payout_spk).unwrap(), self.rt.balance_of(&self.pubs[1].payout_spk).unwrap()]
    }
}

fn report(g: &PosGame, sc: &Scenario) -> Report {
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

fn roles(g: &PosGame) -> Vec<String> {
    g.seen.iter().map(|s| s.1.clone()).collect()
}

/// PS2/PS3's shape: the hub stalls at `d`; the user's absence claim and
/// timeout split resolve it.
fn stall(sc: &'static Scenario, d: u32, opening: &[u8]) -> Result<Report> {
    let mut g = PosGame::open(sat(POT))?;
    for mv in opening {
        g.play(*mv)?;
    }
    g.stall(); // the hub does not move: nothing is sealed, the members flag it
    g.wait_claim(d)?;
    let (h, _, _) = g.claim_absent(d)?;
    g.wait_to(h + u32::from(g.params.delta) + 1)?;
    g.split(d, &format!("absent_{d}"), 0, None)?;
    ensure!(roles(&g) == vec![format!("absent_{d}"), format!("absent_{d}/split_UserWins")], "{:?}", roles(&g));
    ensure!(g.balances() == [sat(POT - 2_000), sat(0)], "{:?}", g.balances());
    Ok(report(&g, sc))
}

pub const PS1: Scenario = Scenario {
    id: "PS1",
    title: "PoS graph: cooperative game, nothing on Bitcoin",
    expected: "seven moves on the PoS venue, each entry's signature verified against the mover's per-depth key; no Bitcoin transaction; 166 pre-signed transactions at open (D44's counters included)",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        for mv in [4u8, 1, 0, 8, 6, 3, 2] {
            g.play(mv)?;
        }
        ensure!(g.depth == 7 && g.board.render() == "XOX/OX./X.O" && g.board.status != OPEN);
        ensure!(g.seen.is_empty(), "nothing on Bitcoin");
        Ok(report(&g, &PS1))
    },
};

pub const PS2: Scenario = Scenario {
    id: "PS2",
    title: "PoS graph: the hub stalls at move 2",
    expected: "the absence claim and the timeout split: two transactions, under 600 vB in all",
    run: || stall(&PS2, 2, &[4]),
};

pub const PS3: Scenario = Scenario {
    id: "PS3",
    title: "PoS graph: the hub stalls at move 6",
    expected: "the same two transactions through the depth-6 leaves",
    run: || stall(&PS3, 6, &[4, 1, 0, 8, 6]),
};

pub const PS4: Scenario = Scenario {
    id: "PS4",
    title: "PoS graph: the loser refuses the fold (the terminal exhibit)",
    expected: "the winner's terminal exhibit parks the attested pair under the status gate; no disprove fires; the self-checking split pays UserWins: two transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        for mv in [4u8, 1, 0, 8, 6, 3, 2] {
            g.play(mv)?;
        }
        ensure!(g.board.status != OPEN, "the game is over on the venue");
        g.wait_claim(7)?;
        let (psig, h, _e_op, _e_prev) = g.exhibit(7)?;
        ensure!(g.disproves_firing(7).is_empty(), "the exhibited terminal move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(7, "exhibit_7", 0, Some(&psig))?;
        ensure!(roles(&g) == vec!["exhibit_7".to_string(), "exhibit_7/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 2_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS4))
    },
};

pub const PS5: Scenario = Scenario {
    id: "PS5",
    title: "PoS graph: a spurious absence claim forfeits the claimant",
    expected: "the hub's move 2 is on the venue; the user claims absence anyway; the hub's rebuttal parks the legal pair, no disprove fires, and the mover's self-checking split pays HubWins (R of an open state forfeits the claimant): three transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        g.play(1)?; // O@1 — the hub DID publish move 2
        g.wait_claim(2)?;
        g.claim_absent(2)?; // the user's spurious claim
        let (psig, h, _, _) = g.rebut(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_2/rebuttal", 1, Some(&psig))?; // R(open) = the claimant forfeits
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/rebut".to_string(), "absent_2/rebuttal/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 3_000)], "{:?}", g.balances());
        Ok(report(&g, &PS5))
    },
};

pub const PS6A: Scenario = Scenario {
    id: "PS6A",
    title: "PoS graph: an illegal move is disproved off the rebuttal",
    expected: "the hub plays an occupied cell at move 2 (attested, not legal); the user's absence claim is rebutted, and the disprove of the parked pair fires cell_occupied_4: three transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        g.play_invalid(4)?; // the hub claims O onto X's cell
        g.wait_claim(2)?;
        g.claim_absent(2)?;
        let (psig, h, p_op, p_prev) = g.rebut(2)?;
        let firing = g.disproves_firing(2);
        ensure!(firing.iter().any(|n| n == "cell_occupied_4"), "{firing:?}");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.disprove(2, &psig, p_op, &p_prev, "cell_occupied_4")?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/rebut".to_string(), "disprove_cell_occupied_4".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 3_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS6A))
    },
};

pub const PS6B: Scenario = Scenario {
    id: "PS6B",
    title: "PoS graph: a fabricated terminal state is disproved off the exhibit",
    expected: "the hub's move 6 claims a terminal status the board does not have; the hub's exhibit passes the status gate (the attested head SAYS terminal), and the user's disprove fires status_mismatch alone: two transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        for mv in [4u8, 1, 0, 8, 6] {
            g.play(mv)?;
        }
        g.play_fabricated_terminal(3, 2)?; // O@3, claiming O_WON on an open board
        g.wait_claim(6)?;
        let (psig, h, e_op, e_prev) = g.exhibit(6)?;
        let firing = g.disproves_firing(6);
        ensure!(firing == vec!["status_mismatch".to_string()], "exactly the fabricated status fires: {firing:?}");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.disprove(6, &psig, e_op, &e_prev, "status_mismatch")?;
        ensure!(roles(&g) == vec!["exhibit_6".to_string(), "disprove_status_mismatch".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 2_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS6B))
    },
};

pub const PS7: Scenario = Scenario {
    id: "PS7",
    title: "PoS graph: a double-played depth (the mover's double-sign) pays the victim",
    expected: "the hub signs two conflicting moves at depth 2 and both are sealed (each validly signed: the members are blameless; the client sees two heads at one depth and names the second seal's member); the user exhibits both signatures of the hub's depth-2 state key (equiv_2, the per-depth D43 form) and takes the pot: one transaction",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        let prior = g.board.clone();
        let (board_a, reveal_a) = g.play(1)?; // O@1, honestly signed
        let (board_b, reveal_b) = g.double_play(2, 8, &prior)?; // O@8 in a fork block
        g.wait_claim(2)?;
        g.equiv_exhibit(2, &board_a, &reveal_a, &board_b, &reveal_b)?;
        ensure!(roles(&g) == ["equiv_2".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 1_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS7))
    },
};

pub const PS8: Scenario = Scenario {
    id: "PS8",
    title: "PoS graph: a baseless terminal exhibit is rejected by the gate",
    expected: "the user exhibits the honest OPEN pair at depth 5 as terminal; the status gate rejects the spend (it never confirms — unlike S7 there is no claim to punish, the exhibit proves or aborts); the hub then does not move 6 and the absence claim resolves",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        for mv in [4u8, 1, 0, 8, 6] {
            g.play(mv)?;
        }
        ensure!(g.board.status == OPEN);
        g.wait_claim(5)?;
        // the baseless exhibit, assembled honestly otherwise: sigs, readout,
        // pair reveal all valid — the open state is what fails
        let (w, _psig) = g.readout_witness("exhibit_5", 5, false)?;
        let [sig_h, sig_u] = g.sigs22("exhibit_5");
        let mut w = w;
        w.push(sig_h);
        w.push(sig_u);
        let bad = g.dry("exhibit_5", w);
        ensure!(g.rt.test_accept(&bad).is_err(), "the status gate must reject an open-state exhibit");
        g.say("the user's baseless terminal exhibit at depth 5: rejected by the status gate, never confirmed".to_string());
        // the game continues; the hub does not move 6 and loses by absence
        g.wait_claim(6)?;
        let (h, _, _) = g.claim_absent(6)?;
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(6, "absent_6", 0, None)?;
        ensure!(roles(&g) == vec!["absent_6".to_string(), "absent_6/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 2_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS8))
    },
};

pub const PS9: Scenario = Scenario {
    id: "PS9",
    title: "PoS graph: a garbage-signed attested entry is not a move (D41)",
    expected: "a legal-looking depth-2 entry whose preimages open no key is refused by the honest members (D55) and sealed by a rogue member (provable misbehaviour); the hub declines to adopt it (its state key never signed that state); a rebuttal carrying the entry's own junk preimages fails the authorship fragment; the absence claim and the timeout split pay the user",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4, really signed
        g.play_garbage_signed(0)?; // depth 2: O@0 claimed, junk signature, a rogue seal
        g.wait_claim(2)?;
        let (h, _, _) = g.claim_absent(2)?;
        let bad = g.rebut_junk(2)?;
        ensure!(g.rt.test_accept(&bad).is_err(), "junk preimages must fail the authorship fragment");
        g.say("the hub declines to adopt the junk entry (adopting would be its move); no rebuttal exists — the absence claim resolves".to_string());
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(2, "absent_2", 0, None)?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 2_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS9))
    },
};

pub const PS10: Scenario = Scenario {
    id: "PS10",
    title: "PoS graph: the staller claims one depth AHEAD — countered (D44)",
    expected: "the hub stalls at move 2, then claims absence at 3 ('the user did not move at 3' — vacuously true, the user's turn never came); the user's counter ('you did not move at 2') has no defence — nothing is attested at depth 2, so no rebuttal exists — and the user's timeout split off the counter output pays: three transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?;
        g.stall(); // the hub does not move 2: nothing is sealed
        g.wait_claim(3)?;
        let (_, _, _) = g.claim_absent(3)?; // the staller's vacuous claim at 3
        let (h, _, _) = g.counter(3)?;
        g.say("the hub cannot defend the counter: nothing is attested at depth 2 (D55: no empty seals — there is nothing to read out)".to_string());
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(2, "absent_3/counter", 0, None)?;
        ensure!(roles(&g) == vec!["absent_3".to_string(), "absent_3/counter".to_string(), "absent_3/counter/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 3_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS10))
    },
};

pub const PS11: Scenario = Scenario {
    id: "PS11",
    title: "PoS graph: a false counter to a due claim is rebutted (D44)",
    expected: "the hub's move 2 is on the venue; the user stalls at 3; the hub's absence claim at 3 is due; the user counters anyway ('you did not move at 2' — false); the hub rebuts on the counter output with the (1, 2) pair readout, no disprove fires, and the hub's self-checking split pays R(parked) = HubWins: four transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?;
        g.play(1)?; // the hub DID publish move 2
        g.stall(); // the user stalls at 3
        g.wait_claim(3)?;
        g.claim_absent(3)?; // due
        g.counter(3)?; // the user's false counter
        let (psig, h, _, _) = g.rebut_under(2, "absent_3/counter")?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_3/counter/rebuttal", 1, Some(&psig))?; // R: the user on turn forfeits -> HubWins
        ensure!(roles(&g) == vec!["absent_3".to_string(), "absent_3/counter".to_string(), "absent_3/counter/rebut".to_string(), "absent_3/counter/rebuttal/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 4_000)], "{:?}", g.balances());
        Ok(report(&g, &PS11))
    },
};

pub const PS12: Scenario = Scenario {
    id: "PS12",
    title: "PoS graph: a LATE attestation is killed by the timeliness flags (D50)",
    expected: "the hub does not move 2 (nothing sealed on time); at the due time the members publish their flag scalars; the hub's member, colluding, then seals the hub's signed O@1 late (nothing contradicts it on the venue); the user claims absence, the hub rebuts with the late block (the readout passes, the move is legal, no tuple disprove fires), and the user's not_timely spend — its own transaction signed under 3 of the 5 members' flag points (the majority) — takes the pot; with 2 flags the leaf rejects it: three transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        g.stall(); // the hub does not move 2: nothing sealed on time, the members flag it
        g.play_late(2, 1)?; // ...the proposer seals the hub's O@1 late anyway
        g.wait_claim(2)?;
        g.claim_absent(2)?;
        let (_psig, h, p_op, p_prev) = g.rebut(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the late move is legal: no tuple disprove fires");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        // two flags do not reach the threshold
        let short = g.not_timely(2, p_op, &p_prev, Some(2), false)?.expect("assembled");
        ensure!(g.rt.test_accept(&short).is_err(), "not_timely must not fire under the threshold");
        g.say("the user's not_timely with 2 of 5 flags: rejected in-leaf (threshold 3), never confirmed".to_string());
        // a third member's flag: the rebuttal dies
        g.not_timely(2, p_op, &p_prev, Some(3), true)?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/rebut".to_string(), "not_timely".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 3_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS12))
    },
};

pub const PS13: Scenario = Scenario {
    id: "PS13",
    title: "PoS graph: a silent designated sealer does not stall the mover — the next member in the rotation seals (D53, D55)",
    expected: "the designated sealer for depth 2 (the rotation) is silent; after the backoff the hub resubmits its O@1 to the next member in the rotation, which seals it; the user's spurious absence claim is rebutted with that seal — the rebuttal's witness names its member through the proposer fragment — no disprove fires, and the hub's self-checking split pays HubWins: three transactions; the silent member cost nothing",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        let designated = lngap_pos::rotation(CONTRACT_ID, 2, K);
        g.miner.silence(designated); // depth 2's designated sealer goes silent
        g.play(1)?; // O@1: resubmitted to, and sealed by, the next member
        ensure!(g.sealed[&2].proposer == (designated + 1) % K, "the mover fell back to the next member in the rotation");
        g.wait_claim(2)?;
        g.claim_absent(2)?; // the user's spurious claim
        let (psig, h, _, _) = g.rebut(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_2/rebuttal", 1, Some(&psig))?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/rebut".to_string(), "absent_2/rebuttal/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 3_000)], "{:?}", g.balances());
        Ok(report(&g, &PS13))
    },
};

/// Each side's dispute deposit in PS14/PS15: it covers the most expensive
/// path an honest party can be forced into at the scenarios' fixed fee
/// (claim or counter, rebuttal, split: 3,000 sat), with room to spare.
const DEPOSIT: u64 = 10_000;

pub const PS14: Scenario = Scenario {
    id: "PS14",
    title: "PoS graph: a spurious claim with dispute deposits — the loser pays (D56)",
    expected: "each side has a 10,000 sat dispute deposit inside the contract; the hub's move 2 is on the venue; the user claims absence anyway; the hub rebuts and its self-checking split pays it the whole output: both stakes, both deposits, less the three hops' fees — the user's deposit covers the fees, so the honest mover nets its stake, the user's stake and its own deposit back with 7,000 sat to spare; settle, the no-dispute fallback, would have returned each deposit: three transactions",
    run: || {
        let mut g = PosGame::open_with_deposit(sat(POT), sat(DEPOSIT))?;
        // settle returns each deposit to its owner (nobody disputed)
        let settle = g.skel("settle").tx.clone();
        ensure!(settle.output.iter().all(|o| o.value >= sat(DEPOSIT)), "settle returns each deposit: {:?}", settle.output.iter().map(|o| o.value).collect::<Vec<_>>());
        g.play(4)?; // X@4
        g.play(1)?; // O@1 — the hub DID publish move 2
        g.wait_claim(2)?;
        g.claim_absent(2)?; // the user's spurious claim
        let (psig, h, _, _) = g.rebut(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_2/rebuttal", 1, Some(&psig))?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/rebut".to_string(), "absent_2/rebuttal/split_HubWins".to_string()], "{:?}", roles(&g));
        let fees = 3_000;
        ensure!(g.balances() == [sat(0), sat(POT + 2 * DEPOSIT - fees)], "{:?}", g.balances());
        ensure!(POT + 2 * DEPOSIT - fees >= POT + DEPOSIT, "the honest mover is made whole: stakes and its own deposit, the fees paid from the user's");
        g.say(format!("the hub receives {} sat: both stakes ({POT}) and its own deposit back ({DEPOSIT}), the dispute's {fees} sat of fees paid from the user's deposit, {} sat of it left over", POT + 2 * DEPOSIT - fees, DEPOSIT - fees));
        Ok(report(&g, &PS14))
    },
};

pub const PS15: Scenario = Scenario {
    id: "PS15",
    title: "PoS graph: an honest stall claim with dispute deposits is not penalised (D56)",
    expected: "each side has a 10,000 sat dispute deposit; the hub stalls at move 2; the user's absence claim and timeout split pay the user the whole output — both stakes and both deposits less two fees: the honest claimant is reimbursed from the staller's deposit: two transactions",
    run: || {
        let mut g = PosGame::open_with_deposit(sat(POT), sat(DEPOSIT))?;
        g.play(4)?;
        g.stall(); // the hub does not move 2
        g.wait_claim(2)?;
        let (h, _, _) = g.claim_absent(2)?;
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(2, "absent_2", 0, None)?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT + 2 * DEPOSIT - 2_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS15))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![PS1, PS2, PS3, PS4, PS5, PS6A, PS6B, PS7, PS8, PS9, PS10, PS11, PS12, PS13, PS14, PS15]
}
