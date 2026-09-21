//! The PoS absence-claim graph's CHESS scenario suite (POS_FACTCHAIN_PLAN.md
//! step 7's PC1-PC9; D42): the pos_stall suite's chess sibling, on the wired
//! `lngap-pos` graph with `Game::Chess` — the twelve chess kinds over the
//! parked pair, the tied readout, 336-bit per-depth state keys.
//!
//! Like the PS suite these run WITHOUT the channel wrapper: the contract
//! output C is funded directly and the pre-signed graph is played by hand.
//! Two chess-shaped differences from PS, both D42:
//!
//! - there is NO exhibit family: chess terminality is not a state field, so
//!   the terminal game (PC4, fool's mate) resolves through the ABSENCE path
//!   — the mated side's slot seals empty and its claim is unanswerable; and
//! - the pre-sign fee is 60k sat, not the 1k placeholder: the chess pair
//!   readout is ~44 kvB and the placeholder would sit under the relay floor
//!   (the fee is the scenario's own parameter; the measurements are vB).
//!
//! The reference games: 1. e4 e5 for the early paths, and fool's mate
//! (1. f3 e5 2. g4 Qh4#) for the terminal ones — the hub (black) mates at
//! depth 4, the mated user's slot is depth 5. One venue block seals per
//! Bitcoin block, empty when no move is pending (the cadence default).

use std::collections::HashMap;

use anyhow::{ensure, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::SECP256K1;
use bitcoin::{Amount, OutPoint, Transaction, TxOut, Txid};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, PresignedTx, Role};
use lngap_chess::certificate::{find_kind, mechanical_successor};
use lngap_chess::leaf::exhibit_values;
use lngap_chess::{apply, Move};
use lngap_chess_fc::{ChessEntry, ChessState, SIGNED_BITS};
use lngap_ec_wots::{Attester, EpochTable};
use lngap_factchain::{entry_head, entry_root, Header};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSig;
use lngap_lamport::Reveal;
use lngap_n4bit::{hash_claim, Digest};
use lngap_pos::chess;
use lngap_pos::instance::{self, Game as WhichGame, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNK_START, HEAD_CHUNKS};
use lngap_pos::ttt;
use lngap_pos::{PosClient, PosMiner, SealedBlock, HEADER_CHUNKS};

use super::{Report, Scenario};

/// The venue's attester seed (the single key standing in for the FROST
/// group key, per the ec-wots design).
const SEED: [u8; 32] = [0x77; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
/// Fool's mate lands at depth 4; the suite's longest line runs to 6.
const MAX_DEPTH: u32 = 8;
const GRACE: u32 = 1;
/// 0.01 BTC — big enough that the 60k-sat pre-sign fee (D42) leaves the
/// winner's share readable.
const POT: u64 = 1_000_000;
/// The pre-sign fee per hop: the chess pair readout is ~44 kvB, so the 1k
/// placeholder would sit under the relay floor (D42).
const FEE: u64 = 60_000;

fn epoch_tables() -> Vec<EpochTable> {
    let attester = Attester::new(SEED);
    (0..=MAX_DEPTH as u64).map(|s| attester.epoch_table(s, HEADER_CHUNKS)).collect()
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

/// A conflicting reveal of the mover's depth-`d` state key, reproduced by
/// hand from the keystore's derivation (the honest keystore refuses to
/// equivocate — asserted at the use site; the 4b wrong-code pattern).
fn adversarial_state_reveal(ks_seed_label: &str, d: u32, bits: &[bool]) -> Reveal {
    let seed = Seed::from_label(ks_seed_label);
    let sk = lngap_lamport::SecretKey::from_entropy(SIGNED_BITS, seed.derive_bytes(&format!("lamport/{}", instance::state_label(CONTRACT_ID, 1, d))));
    sk.reveal_bits(bits).unwrap()
}

/// One PoS-venue chess game with its contract funded on a fresh regtest:
/// the draft (both keystores' offers), the venue at genesis, C funded, the
/// 2,753-skeleton graph pre-signed.
struct ChessPosGame {
    rt: Regtest,
    params: ChannelParams,
    user: PartyKeys,
    hub: PartyKeys,
    user_ks: KeyStore,
    hub_ks: KeyStore,
    pubs: [PartyPubKeys; 2],
    inst: PosInstance,
    tables: Vec<EpochTable>,
    miner: PosMiner,
    client: PosClient,
    sealed: HashMap<u32, SealedBlock>,
    /// Anyone's native check of a slot-`d` entry's signature: the mover's
    /// state key's claim-native mirror commitments (in a deployment these
    /// ride the draft's public offers; the contract leaf uses the hash160
    /// form of the same key).
    venue_commits: HashMap<u32, Vec<[Digest; 2]>>,
    graph: Vec<PresignedTx>,
    /// The position after the last sealed move.
    state: ChessState,
    /// The deepest sealed move.
    depth: u32,
    /// The next venue slot to seal (1-based): move `depth + 1` sits in it.
    /// Dispute-time waits mine WITHOUT sealing — the venue runs sparse then
    /// (legal; the cadence default is a venue property, not a validity rule).
    next_slot: u32,
    btc_open: u32,
    /// (height, role, txid, broadcaster, vsize) of each broadcast.
    seen: Vec<(u32, String, Txid, Role, usize)>,
    log: Vec<String>,
}

impl ChessPosGame {
    fn open(value: Amount) -> Result<ChessPosGame> {
        let rt = Regtest::start()?;
        let tables = epoch_tables();
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("pc/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("pc/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("pc/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("pc/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Chess)?;
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Chess)?;
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH)?;
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH)?;
        ensure!(keys_u == keys_h, "the merged key sets must agree");
        // the contract's slot clock: slot 1 seals at `btc_open`, one venue
        // block per Bitcoin block while the game is being played
        let btc_open = rt.height()? + 1;
        let deadline = btc_open + 400;
        let inst = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, WhichGame::Chess, btc_open, GRACE, keys_u)?;
        let params = ChannelParams {
            presign_fee: sat(FEE),
            ..ChannelParams::regtest(Amount::from_sat(400_000))
        };
        let pubs = [user.public(), hub.public()];
        let mut venue_commits = HashMap::new();
        for d in 1..=MAX_DEPTH {
            let ks = if instance::mover_at(d) == Role::User { &mut user_ks } else { &mut hub_ks };
            venue_commits.insert(d, ks.commit_with(&instance::state_label(CONTRACT_ID, 1, d), |p| hash_claim(p))?);
        }
        let attester = Attester::new(SEED);
        let (gen, _t0) = lngap_pos::genesis(&attester);
        let gen_digest = gen.header.digest();
        let miner = PosMiner::new(SEED, gen_digest, 0);
        let client = PosClient::from_checkpoint(0, gen_digest);
        let mut g = ChessPosGame {
            rt,
            params,
            user,
            hub,
            user_ks,
            hub_ks,
            pubs,
            inst,
            tables,
            miner,
            client,
            sealed: HashMap::from([(0u32, gen)]),
            venue_commits,
            graph: Vec::new(),
            state: ChessState::initial(),
            depth: 0,
            next_slot: 1,
            btc_open,
            seen: Vec::new(),
            log: Vec::new(),
        };
        let ctx = g.ctx();
        let tree = g.inst.tree(&ctx, &g.tables)?;
        let (c_op, c_prev) = g.rt.fund(&tree.script_pubkey(), g.inst.value)?;
        ensure!(g.rt.height()? == btc_open, "the funding mined exactly one block");
        g.graph = g.inst.graph(&ctx, c_op, &c_prev, &g.tables)?;
        ensure!(
            g.graph.len() == (1 + MAX_DEPTH as usize * 8 + MAX_DEPTH as usize * SIGNED_BITS) as usize,
            "the wired chess graph: settle + {MAX_DEPTH}x(claim, refute, 3+3 splits) + {MAX_DEPTH}x{SIGNED_BITS} equiv; NO exhibit family (D42)"
        );
        g.say(format!(
            "game opened: contract {CONTRACT_ID}, pot {} sat; {} pre-signed transactions",
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
        self.log.push(format!("[pos @ {h} / depth {}] {s}", self.depth));
    }

    fn head(&self, slot: u32) -> [u8; 48] {
        self.sealed[&slot].header.head()
    }

    /// Seal the current slot's block (with `entry`, or empty), verify it
    /// natively as anyone would, and check a move entry's signature against
    /// the mover's pinned key.
    fn seal(&mut self, entry: Option<(ChessEntry, ChessState)>) -> Result<()> {
        let slot = self.next_slot;
        if let Some((e, _)) = &entry {
            self.miner.submit(e.encode());
        }
        let (block, table) = self.miner.seal_next(slot).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &table).map_err(|e| anyhow::anyhow!(e))?;
        self.next_slot += 1;
        if let Some((e, new)) = entry {
            ensure!(e.check_sigs(&self.venue_commits[&slot]), "slot {slot}: the entry does not open the mover's state key");
            let mv = new.mv;
            self.state = new;
            self.depth = slot;
            self.say(format!(
                "slot {slot} sealed with {}'s move {}; attested, the signature opens the key",
                instance::mover_at(slot),
                mv
            ));
        } else {
            self.say(format!("slot {slot} sealed EMPTY (cadence)"));
        }
        self.sealed.insert(slot, block);
        Ok(())
    }

    /// One Bitcoin block, one venue slot: play `uci` (legal), signed for
    /// real. Returns the new state and the state reveal (evidence material).
    fn play(&mut self, uci: &str) -> Result<(ChessState, Reveal)> {
        self.rt.mine(1)?;
        let slot = self.next_slot;
        let mover = instance::mover_at(slot);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: slot as u8 };
        let reveal = self.ks(mover).reveal_bits(&instance::state_label(CONTRACT_ID, 1, slot), &ChessEntry::signed_bits(&new))?;
        let entry = ChessEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            state: new.clone(),
            sigs: reveal.preimages.clone(),
        };
        self.seal(Some((entry, new.clone())))?;
        Ok((new, reveal))
    }

    /// One empty venue slot (the mover stalls, or the game is over).
    fn idle_slot(&mut self) -> Result<()> {
        self.rt.mine(1)?;
        self.seal(None)
    }

    /// Mine and seal empty slots until the Bitcoin height reaches `h`.
    fn wait_to(&mut self, h: u32) -> Result<()> {
        while self.rt.height()? < h {
            self.idle_slot()?;
        }
        Ok(())
    }

    /// The height from which a depth-`d` claim matures, also covering the
    /// broadcaster's to_self_delay on the contract output.
    fn mature_at(&self, d: u32) -> u32 {
        self.inst.claim_from(d).max(self.btc_open + self.params.to_self_delay as u32)
    }

    /// The mover at the coming slot plays `uci` ILLEGALLY and the venue
    /// seals the mechanical successor, signed over the CLAIMED state
    /// (validly signed garbage: the disprove family judges the transition).
    fn play_invalid(&mut self, uci: &str) -> Result<()> {
        self.rt.mine(1)?;
        let slot = self.next_slot;
        let mover = instance::mover_at(slot);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = mechanical_successor(&self.state.pos, mv);
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: slot as u8 };
        let reveal = self.ks(mover).reveal_bits(&instance::state_label(CONTRACT_ID, 1, slot), &ChessEntry::signed_bits(&new))?;
        let entry = ChessEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            state: new.clone(),
            sigs: reveal.preimages.clone(),
        };
        self.seal(Some((entry, new)))?;
        self.say(format!("slot {slot} holds {mover}'s move {uci} — attested, NOT legal"));
        Ok(())
    }

    /// The mover at the coming slot claims `uci` with a GARBAGE sigs region
    /// (D41): the venue attests existence, never validity — the chain
    /// accepts the block (the attestation is honest) while the entry opens
    /// no key. The position does NOT advance (no signed move exists).
    fn play_garbage_signed(&mut self, uci: &str) -> Result<()> {
        self.rt.mine(1)?;
        let slot = self.next_slot;
        let mover = instance::mover_at(slot);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&self.state.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: slot as u8 };
        let entry = ChessEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            state: new,
            sigs: vec![[0x11; 20]; SIGNED_BITS],
        };
        self.miner.submit(entry.encode());
        let (block, table) = self.miner.seal_next(slot).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &table).map_err(|e| anyhow::anyhow!(e))?;
        self.next_slot += 1;
        self.say(format!("slot {slot} holds {mover}'s claimed move {uci} with a GARBAGE signature — attested (existence, not validity); anyone sees it opens no key"));
        self.sealed.insert(slot, block);
        Ok(())
    }

    /// The state-key reveal over a sealed head's CLAIMED state||move (the
    /// D41 authorship block), from that depth's mover's keystore — the same
    /// bits as the published entry's, so the same preimages (idempotent).
    fn auth_reveal(&mut self, d: u32, head: &[u8; 48]) -> Reveal {
        let state = ChessState::from_e(head[8..48].try_into().unwrap()).unwrap();
        self.ks(instance::mover_at(d))
            .reveal_bits(&instance::state_label(CONTRACT_ID, 1, d), &ChessEntry::signed_bits(&state))
            .unwrap()
    }

    /// The mover at depth `d` plays a SECOND, conflicting move in a fork
    /// block at the same slot (the venue equivocates). The client names the
    /// event; the conflicting state reveal is hand-reproduced.
    fn double_play(&mut self, d: u32, uci: &str, prior: &ChessState) -> Result<(ChessState, Reveal)> {
        let mover = instance::mover_at(d);
        let mv = Move::parse(uci).ok_or_else(|| anyhow::anyhow!("bad uci {uci}"))?;
        let mut pos = apply(&prior.pos, mv).map_err(|v| anyhow::anyhow!("{v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let bits = ChessEntry::signed_bits(&new);
        ensure!(self.ks(mover).reveal_bits(&instance::state_label(CONTRACT_ID, 1, d), &bits).is_err(), "the honest keystore refuses to equivocate");
        let reveal = adversarial_state_reveal(&format!("pc/{}-ks", mover.name()), d, &bits);
        let entry = ChessEntry {
            game_id: GAME_ID,
            depth: d as u8,
            mover: mover.idx() as u8,
            state: new.clone(),
            sigs: reveal.preimages.clone(),
        }
        .encode();
        let parent = self.sealed[&(d - 1)].header.digest();
        let header = Header::new(&parent, &entry_root(&entry), &entry_head(&entry), d);
        let attestation = self.miner.attester().attest(&self.tables[d as usize], header.as_bytes());
        let fork = SealedBlock { header, entry, attestation };
        ensure!(
            matches!(self.client.observe(&fork, &self.tables[d as usize]), Ok(lngap_pos::Observation::Equivocation(_))),
            "the second sealed block at slot {d} is the equivocation"
        );
        self.say(format!("slot {d} sealed TWICE ({mover}'s double-play): the client names the equivocation"));
        Ok((new, reveal))
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
        self.say(format!("{claimant} claims: no valid move at slot {d}"));
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
            Reveal { preimages: vec![[0x11; 20]; SIGNED_BITS] }
        } else {
            self.auth_reveal(d, &new_head)
        };
        let sign_at = |block: &SealedBlock| -> Vec<Vec<u8>> {
            (0..HEAD_CHUNKS).map(|j| sign_tx(&Keypair::from_secret_key(SECP256K1, &block.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect()
        };
        let sigs_new = sign_at(&self.sealed[&d]);
        let sigs_prev = sign_at(&self.sealed[&(d - 1)]);
        let w = refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&new_r]);
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

    /// The mover's refutation at depth `d`: the readout parks the attested
    /// pair. Returns the pair reveal and the refuted output.
    fn refute(&mut self, d: u32) -> Result<(WotsSig, u32, OutPoint, TxOut)> {
        let mover = instance::mover_at(d);
        let label = format!("absent_{d}/refute");
        let (mut w, pair_sig) = self.readout_witness(&label, d, false)?;
        let msig = {
            let p = self.skel(&label);
            sign_tx(self.payment(mover), &p.tx, &p.prevouts[0], &p.leaf.script)
        };
        w.push(msig);
        self.say(format!("{mover} refutes: the venue attested the moves at slots {} and {d}", d - 1));
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

    /// The equivocation exhibit (D39): both preimages of a differing signed
    /// bit of the depth-`d` mover's key, from the two conflicting entries.
    fn equiv_exhibit(&mut self, d: u32, state_a: &ChessState, reveal_a: &Reveal, state_b: &ChessState, reveal_b: &Reveal) -> Result<()> {
        let bits_a = ChessEntry::signed_bits(state_a);
        let bits_b = ChessEntry::signed_bits(state_b);
        let i = (0..SIGNED_BITS).find(|&i| bits_a[i] != bits_b[i]).expect("conflicting states differ at some bit");
        let (pa, pb) = (reveal_a.preimages[i], reveal_b.preimages[i]);
        let (p0, p1) = if bits_a[i] { (pb, pa) } else { (pa, pb) };
        let c = &self.inst.depth_keys(d).state.bits[i];
        assert_eq!(lngap_btc::hash160(&p0), c.h0, "p0 must open the bit's h0");
        assert_eq!(lngap_btc::hash160(&p1), c.h1, "p1 must open the bit's h1");
        let label = format!("equiv_{d}_{i}");
        let [sig_h, sig_u] = self.sigs22(&label);
        let exhibitor = instance::mover_at(d).other();
        self.say(format!("{exhibitor} exhibits the double-signed state bit {i} at depth {d}"));
        self.run(&label, vec![p0.to_vec(), p1.to_vec(), sig_h, sig_u], exhibitor)?;
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
    g.idle_slot()?; // the hub's slot seals empty
    g.wait_to(g.mature_at(d))?;
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
    expected: "fool's mate on the PoS venue, each entry's signature verified against the mover's per-depth key; no Bitcoin transaction; 2,753 pre-signed transactions at open",
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
    expected: "fool's mate: the hub mates at depth 4; the mated user's slot 5 seals empty (no legal move exists); the hub's absence claim is UNANSWERABLE and the timeout split pays HubWins — the terminal path needs no exhibit family: two transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        for uci in ["f2f3", "e7e5", "g2g4", "d8h4"] {
            g.play(uci)?;
        }
        ensure!(lngap_chess::terminal(&g.state.pos).is_some(), "the game is over on the venue");
        g.idle_slot()?; // the mated user's slot seals empty
        g.wait_to(g.mature_at(5))?;
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
        g.play("e7e5")?; // the hub DID publish at slot 2
        g.wait_to(g.mature_at(2))?;
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
        g.wait_to(g.mature_at(2))?;
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
    title: "PoS graph, chess: a double-played slot (venue equivocation + the mover's double-sign) pays the victim",
    expected: "the venue seals slot 2 twice with conflicting hub entries (e7e5 and c7c5; the client names the equivocation); the user exhibits both preimages of a differing signed bit of the hub's depth-2 key (equiv_2_{i}, a 336-bit family) and takes the pot: one transaction",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?;
        let prior = g.state.clone();
        let (state_a, reveal_a) = g.play("e7e5")?; // honestly signed
        let (state_b, reveal_b) = g.double_play(2, "c7c5", &prior)?; // the fork block
        g.wait_to(g.mature_at(2))?;
        g.equiv_exhibit(2, &state_a, &reveal_a, &state_b, &reveal_b)?;
        ensure!(roles(&g).len() == 1 && roles(&g)[0].starts_with("equiv_2_"), "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - FEE), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PC7))
    },
};

pub const PC8: Scenario = Scenario {
    id: "PC8",
    title: "PoS graph, chess: a garbage-signed attested entry is not a move (D41)",
    expected: "the venue seals slot 2 with a legal-looking e7e5 whose preimages open no key; the hub declines to adopt it (its state key never signed that state); a refutation carrying the entry's own junk preimages fails the authorship fragment; the absence claim and the timeout split pay the user",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        g.play("e2e4")?; // really signed
        g.play_garbage_signed("e7e5")?; // slot 2: e7e5 claimed, junk signature
        g.wait_to(g.mature_at(2))?;
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
    expected: "fool's mate, then the mated user 'answers' g4g5 at slot 5 (the king still attacked); the hub's absence claim is refuted over the illegal pair, and the hub's disprove fires chess_kingattacked — a two-element exhibit: three transactions",
    run: || {
        let mut g = ChessPosGame::open(sat(POT))?;
        for uci in ["f2f3", "e7e5", "g2g4", "d8h4"] {
            g.play(uci)?;
        }
        ensure!(lngap_chess::terminal(&g.state.pos).is_some(), "terminal at depth 4");
        g.play_invalid("g4g5")?; // the mated user's illegal answer at slot 5
        g.wait_to(g.mature_at(5))?;
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

pub fn scenarios() -> Vec<Scenario> {
    vec![
        PC1, PC2, PC3, PC4, PC5, PC6, PC7, PC8, PC9,
    ]
}
