//! The PoS absence-claim graph's scenario suite (POS_FACTCHAIN_PLAN.md step
//! 7; D40): PS1-PS8, the PoS analogues of the S1-S9 stall suite
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
//! — X wins at move 7. One venue block seals per Bitcoin block, empty when
//! no move is pending (the cadence default).

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
use lngap_contract::Contract;
use lngap_ec_wots::{Attester, EpochTable};
use lngap_factchain::slot::{SlotEntry, STATE_BITS};
use lngap_factchain::{entry_head, entry_root, Header};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSig;
use lngap_lamport::Reveal;
use lngap_n4bit::{hash_claim, Digest};
use lngap_pos::instance::{self, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNK_START, HEAD_CHUNKS};
use lngap_pos::ttt;
use lngap_pos::{PosClient, PosMiner, SealedBlock, HEADER_CHUNKS};
use lngap_tictactoe::{Board, TicTacToe, OPEN};

use super::{Report, Scenario};

/// The venue's attester seed (the single key standing in for the FROST
/// group key, per the ec-wots design).
const SEED: [u8; 32] = [0x77; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
const MAX_DEPTH: u32 = 9;
const GRACE: u32 = 1;
const POT: u64 = 200_000;

fn epoch_tables() -> Vec<EpochTable> {
    let attester = Attester::new(SEED);
    (0..=MAX_DEPTH as u64).map(|s| attester.epoch_table(s, HEADER_CHUNKS)).collect()
}

fn state_bits(b: &Board) -> Vec<bool> {
    TicTacToe.state_bits(b)
}

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &bitcoin::ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

/// A conflicting reveal of the mover's depth-`d` state key, reproduced by
/// hand from the keystore's derivation (the honest keystore refuses to
/// equivocate — asserted at the use site; the 4b wrong-code pattern).
fn adversarial_state_reveal(ks_seed_label: &str, d: u32, bits: &[bool]) -> Reveal {
    let seed = Seed::from_label(ks_seed_label);
    let sk = lngap_lamport::SecretKey::from_entropy(STATE_BITS, seed.derive_bytes(&format!("lamport/{}", instance::state_label(CONTRACT_ID, 1, d))));
    sk.reveal_bits(bits).unwrap()
}

/// One PoS-venue game with its contract funded on a fresh regtest: the
/// draft (both keystores' offers), the venue at genesis, C funded, the
/// 282-skeleton graph pre-signed.
struct PosGame {
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
    board: Board,
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

impl PosGame {
    fn open(value: Amount) -> Result<PosGame> {
        let rt = Regtest::start()?;
        let tables = epoch_tables();
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("ps/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("ps/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("ps/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("ps/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH)?;
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH)?;
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH)?;
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH)?;
        ensure!(keys_u == keys_h, "the merged key sets must agree");
        // the contract's slot clock: slot 1 seals at `btc_open`, one venue
        // block per Bitcoin block while the game is being played
        let btc_open = rt.height()? + 1;
        let deadline = btc_open + 400;
        let inst = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, btc_open, GRACE, keys_u)?;
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
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
        let mut g = PosGame {
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
            board: Board::empty(),
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
        ensure!(g.graph.len() == 282, "the wired graph: settle + 9x(claim, refute, 3+3 splits) + 5x(exhibit, 3 splits) + 9x21 equiv");
        g.say(format!("game opened: contract {CONTRACT_ID}, pot {} sat; 282 pre-signed transactions", g.inst.value.to_sat()));
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
    fn seal(&mut self, entry: Option<(SlotEntry, Board)>) -> Result<()> {
        let slot = self.next_slot;
        if let Some((e, _)) = &entry {
            self.miner.submit(e.encode());
        }
        let (block, table) = self.miner.seal_next(slot).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &table).map_err(|e| anyhow::anyhow!(e))?;
        self.next_slot += 1;
        if let Some((e, new)) = entry {
            ensure!(e.check_sigs(&self.venue_commits[&slot]), "slot {slot}: the entry does not open the mover's state key");
            self.board = new;
            self.depth = slot;
            let b = self.board.render();
            self.say(format!("slot {slot} sealed with {}'s move ({b}); attested, the signature opens the key", instance::mover_at(slot)));
        } else {
            self.say(format!("slot {slot} sealed EMPTY (cadence)"));
        }
        self.sealed.insert(slot, block);
        Ok(())
    }

    /// One Bitcoin block, one venue slot: play `mv` (legal), signed for
    /// real. Returns the new board and the state reveal (evidence material).
    fn play(&mut self, mv: u8) -> Result<(Board, Reveal)> {
        self.rt.mine(1)?;
        let slot = self.next_slot;
        let mover = instance::mover_at(slot);
        let new = TicTacToe.transition(&self.board, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        let reveal = self.ks(mover).reveal_bits(&instance::state_label(CONTRACT_ID, 1, slot), &state_bits(&new))?;
        let entry = SlotEntry { game_id: GAME_ID, depth: slot as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: reveal.preimages.clone() };
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

    /// The height from which a depth-`d` claim/exhibit matures, also
    /// covering the broadcaster's to_self_delay on the contract output.
    fn mature_at(&self, d: u32) -> u32 {
        self.inst.claim_from(d).max(self.btc_open + self.params.to_self_delay as u32)
    }

    /// The mover at the coming slot plays `mv` onto an OCCUPIED cell and
    /// the venue seals the naive overwrite, signed over the CLAIMED state
    /// (validly signed garbage: the disprove family judges the transition).
    fn play_invalid(&mut self, mv: u8) -> Result<()> {
        self.rt.mine(1)?;
        let slot = self.next_slot;
        let mover = instance::mover_at(slot);
        let mut new = self.board.clone();
        new.cells[mv as usize] = if mover == Role::User { 1 } else { 2 };
        new.turn = mover.other();
        let reveal = self.ks(mover).reveal_bits(&instance::state_label(CONTRACT_ID, 1, slot), &state_bits(&new))?;
        let entry = SlotEntry { game_id: GAME_ID, depth: slot as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: reveal.preimages.clone() };
        self.seal(Some((entry, new)))?;
        self.say(format!("slot {slot} holds {mover}'s move {mv} onto an occupied cell — attested, NOT legal"));
        Ok(())
    }

    /// The mover plays `mv` legally but claims a TERMINAL status the board
    /// does not have (validly signed; `status_mismatch`'s case). The venue
    /// seals the fabricated head.
    fn play_fabricated_terminal(&mut self, mv: u8, false_status: u8) -> Result<()> {
        self.rt.mine(1)?;
        let slot = self.next_slot;
        let mover = instance::mover_at(slot);
        let mut new = TicTacToe.transition(&self.board, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        new.status = false_status;
        let reveal = self.ks(mover).reveal_bits(&instance::state_label(CONTRACT_ID, 1, slot), &state_bits(&new))?;
        let entry = SlotEntry { game_id: GAME_ID, depth: slot as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&state_bits(&new)), sigs: reveal.preimages.clone() };
        self.seal(Some((entry, new)))?;
        self.say(format!("slot {slot} holds {mover}'s move {mv} claiming a fabricated terminal status — attested, NOT honest"));
        Ok(())
    }

    /// The mover at the coming slot claims `mv` with a GARBAGE sigs region
    /// (D41's PS9): the venue attests existence, never validity — the chain
    /// accepts the block (the attestation is honest) while the entry opens
    /// no key. The board does NOT advance (no signed move exists).
    fn play_garbage_signed(&mut self, mv: u8) -> Result<()> {
        self.rt.mine(1)?;
        let slot = self.next_slot;
        let mover = instance::mover_at(slot);
        let new = TicTacToe.transition(&self.board, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        let entry = SlotEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            mv,
            state: lngap_lamport::bits_to_uint(&state_bits(&new)),
            sigs: vec![[0x11; 20]; STATE_BITS],
        };
        self.miner.submit(entry.encode());
        let (block, table) = self.miner.seal_next(slot).map_err(|e| anyhow::anyhow!(e))?;
        self.client.verify_and_append(&block, &table).map_err(|e| anyhow::anyhow!(e))?;
        self.next_slot += 1;
        self.say(format!("slot {slot} holds {mover}'s claimed move {mv} with a GARBAGE signature — attested (existence, not validity); anyone sees it opens no key"));
        self.sealed.insert(slot, block);
        Ok(())
    }

    /// The state-key reveal over a sealed head's CLAIMED state (the D41
    /// authorship block), from that depth's mover's keystore — the same
    /// bits as the published entry's, so the same preimages (idempotent).
    fn auth_reveal(&mut self, d: u32, head: &[u8; 48]) -> Reveal {
        let state = u32::from_be_bytes(head[4..8].try_into().unwrap()) & 0x00ff_ffff;
        self.ks(instance::mover_at(d))
            .reveal_bits(&instance::state_label(CONTRACT_ID, 1, d), &lngap_lamport::uint_to_bits(state, STATE_BITS))
            .unwrap()
    }

    /// The mover at depth `d` plays a SECOND, conflicting move in a fork
    /// block at the same slot (the venue equivocates). The client names the
    /// event; the conflicting state reveal is hand-reproduced.
    fn double_play(&mut self, d: u32, mv: u8, prior: &Board) -> Result<(Board, Reveal)> {
        let mover = instance::mover_at(d);
        let new = TicTacToe.transition(prior, &mv, mover).map_err(|e| anyhow::anyhow!("{e}"))?;
        let bits = state_bits(&new);
        ensure!(self.ks(mover).reveal_bits(&instance::state_label(CONTRACT_ID, 1, d), &bits).is_err(), "the honest keystore refuses to equivocate");
        let reveal = adversarial_state_reveal(&format!("ps/{}-ks", mover.name().to_lowercase()), d, &bits);
        let entry = SlotEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, mv, state: lngap_lamport::bits_to_uint(&bits), sigs: reveal.preimages.clone() }.encode();
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

    /// The pair-readout witness of a refute/exhibit at depth `d`, with the
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
        let pair_sig = self.ks(mover).sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).map_err(|e| anyhow::anyhow!("{e}"))?;
        let junk_r = Reveal { preimages: vec![[0x11; 20]; STATE_BITS] };
        let (prev_r, new_r) = if junk { (junk_r.clone(), junk_r) } else { (self.auth_reveal(d - 1, &prev_head), self.auth_reveal(d, &new_head)) };
        let sign_at = |block: &SealedBlock| -> Vec<Vec<u8>> {
            (0..HEAD_CHUNKS).map(|j| sign_tx(&Keypair::from_secret_key(SECP256K1, &block.attestation.secrets[HEAD_CHUNK_START + j]), &tx, &prev, &leaf)).collect()
        };
        let sigs_new = sign_at(&self.sealed[&d]);
        let sigs_prev = sign_at(&self.sealed[&(d - 1)]);
        let w = refute::refute_witness_pair(&prev_head, &sigs_prev, &new_head, &sigs_new, &pair_sig, &prev_r, &new_r);
        Ok((w, pair_sig))
    }

    /// The depth-`d` refutation carrying the entry's own junk preimages —
    /// the PS9 negative, assembled but never broadcast.
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
        ttt::disprove_leaves(&l, &self.inst.depth_keys(d).refute)
            .into_iter()
            .filter(|pl| (pl.fires)(&prior, &new))
            .map(|pl| pl.name)
            .collect()
    }

    /// The claimant's disprove off the refuted/exhibit output (a runtime
    /// transaction: the witness copies the pair reveal from the refutation's
    /// published witness).
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
        let mut w = refute::wots_wire(pair_sig);
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block(&format!("disprove_{name}"))?);
        self.say(format!("{challenger} disproves the parked tuple: {name} fires"));
        self.run_tx(&format!("disprove_{name}"), tx, challenger)?;
        Ok(())
    }

    /// A code-gated split spend. `base` is `absent_{d}` (the claimant's
    /// timeout split) or `absent_{d}/refuted` / `exhibit_{d}` (the mover's
    /// self-checking split).
    fn split(&mut self, d: u32, base: &str, code: u8, pair_sig: Option<&WotsSig>) -> Result<()> {
        let name = match code {
            0 => "UserWins",
            1 => "HubWins",
            _ => "Draw",
        };
        let label = format!("{base}/split_{name}");
        match pair_sig {
            // the mover's self-checking split off the refuted/exhibit output
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

    /// The equivocation exhibit (D39): both preimages of a differing state
    /// bit of the depth-`d` mover's key, from the two conflicting entries.
    fn equiv_exhibit(&mut self, d: u32, board_a: &Board, reveal_a: &Reveal, board_b: &Board, reveal_b: &Reveal) -> Result<()> {
        let bits_a = state_bits(board_a);
        let bits_b = state_bits(board_b);
        let i = (0..STATE_BITS).find(|&i| bits_a[i] != bits_b[i]).expect("conflicting states differ at some bit");
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
    g.idle_slot()?; // the hub's slot seals empty
    g.wait_to(g.mature_at(d))?;
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
    expected: "seven moves on the PoS venue, each entry's signature verified against the mover's per-depth key; no Bitcoin transaction; 282 pre-signed transactions at open",
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
        g.wait_to(g.mature_at(7))?;
        let (psig, h, e_op, e_prev) = g.exhibit(7)?;
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
    expected: "the hub's move 2 is on the venue; the user claims absence anyway; the hub's refutation parks the legal pair, no disprove fires, and the mover's self-checking split pays HubWins (R of an open state forfeits the claimant): three transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        g.play(1)?; // O@1 — the hub DID publish at slot 2
        g.wait_to(g.mature_at(2))?;
        g.claim_absent(2)?; // the user's spurious claim
        let (psig, h, _, _) = g.refute(2)?;
        ensure!(g.disproves_firing(2).is_empty(), "the parked move is legal");
        g.wait_to(h + u32::from(g.params.delta) + u32::from(g.params.delta_prime) + 1)?;
        g.split(2, "absent_2/refuted", 1, Some(&psig))?; // R(open) = the claimant forfeits
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/refute".to_string(), "absent_2/refuted/split_HubWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(0), sat(POT - 3_000)], "{:?}", g.balances());
        Ok(report(&g, &PS5))
    },
};

pub const PS6A: Scenario = Scenario {
    id: "PS6A",
    title: "PoS graph: an illegal move is disproved off the refutation",
    expected: "the hub plays an occupied cell at move 2 (attested, not legal); the user's absence claim is refuted, and the disprove of the parked pair fires cell_occupied_4: three transactions",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        g.play_invalid(4)?; // the hub claims O onto X's cell
        g.wait_to(g.mature_at(2))?;
        g.claim_absent(2)?;
        let (psig, h, p_op, p_prev) = g.refute(2)?;
        let firing = g.disproves_firing(2);
        ensure!(firing.iter().any(|n| n == "cell_occupied_4"), "{firing:?}");
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.disprove(2, &psig, p_op, &p_prev, "cell_occupied_4")?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/refute".to_string(), "disprove_cell_occupied_4".to_string()], "{:?}", roles(&g));
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
        g.wait_to(g.mature_at(6))?;
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
    title: "PoS graph: a double-played slot (venue equivocation + the mover's double-sign) pays the victim",
    expected: "the venue seals slot 2 twice with conflicting hub entries (the client names the equivocation); the user exhibits both preimages of a differing state bit of the hub's depth-2 key (equiv_2_{i}) and takes the pot: one transaction",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4
        let prior = g.board.clone();
        let (board_a, reveal_a) = g.play(1)?; // O@1, honestly signed
        let (board_b, reveal_b) = g.double_play(2, 8, &prior)?; // O@8 in a fork block
        g.wait_to(g.mature_at(2))?;
        g.equiv_exhibit(2, &board_a, &reveal_a, &board_b, &reveal_b)?;
        ensure!(roles(&g).len() == 1 && roles(&g)[0].starts_with("equiv_2_"), "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 1_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS7))
    },
};

pub const PS8: Scenario = Scenario {
    id: "PS8",
    title: "PoS graph: a baseless terminal exhibit is rejected by the gate",
    expected: "the user exhibits the honest OPEN pair at depth 5 as terminal; the status gate rejects the spend (it never confirms — unlike S7 there is no claim to punish, the exhibit proves or aborts); the hub then stalls slot 6 and the absence claim resolves",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        for mv in [4u8, 1, 0, 8, 6] {
            g.play(mv)?;
        }
        ensure!(g.board.status == OPEN);
        g.wait_to(g.mature_at(5))?;
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
        // the game continues; the hub stalls slot 6 and loses by absence
        g.wait_to(g.mature_at(6))?;
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
    expected: "the venue seals slot 2 with a legal-looking entry whose preimages open no key; the hub declines to adopt it (its state key never signed that state); a refutation carrying the entry's own junk preimages fails the authorship fragment; the absence claim and the timeout split pay the user",
    run: || {
        let mut g = PosGame::open(sat(POT))?;
        g.play(4)?; // X@4, really signed
        g.play_garbage_signed(0)?; // slot 2: O@0 claimed, junk signature
        g.wait_to(g.mature_at(2))?;
        let (h, _, _) = g.claim_absent(2)?;
        let bad = g.refute_junk(2)?;
        ensure!(g.rt.test_accept(&bad).is_err(), "junk preimages must fail the authorship fragment");
        g.say("the hub declines to adopt the junk entry (adopting would be its move); no refutation exists — the absence claim resolves".to_string());
        g.wait_to(h + u32::from(g.params.delta) + 1)?;
        g.split(2, "absent_2", 0, None)?;
        ensure!(roles(&g) == vec!["absent_2".to_string(), "absent_2/split_UserWins".to_string()], "{:?}", roles(&g));
        ensure!(g.balances() == [sat(POT - 2_000), sat(0)], "{:?}", g.balances());
        Ok(report(&g, &PS9))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![PS1, PS2, PS3, PS4, PS5, PS6A, PS6B, PS7, PS8, PS9]
}
