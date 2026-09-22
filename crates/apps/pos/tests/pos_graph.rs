//! The wired PoS absence-claim graph on regtest (POS_FACTCHAIN_PLAN.md step
//! 4b): the full absence → refute → disprove/split dance with per-depth key
//! sets generated in the two parties' keystores under the draft's label
//! discipline and exchanged as public offers, and the venue's epoch tables
//! published at setup.
//!
//! Paths mined (the node enforcing real timelocks):
//!
//! - A: hub's slot-2 move is ILLEGAL (an occupied cell): the user claims
//!   absence, hub's two-head refutation parks the attested pair, and the
//!   user's `cell_occupied_4` disprove takes the pot after `delta`;
//! - B: hub's slot-2 move is legal: no disprove fires, and the mover's
//!   SELF-CHECKING split pays R(parked state) after `delta + delta'` — the
//!   wrong code is rejected in-leaf;
//! - C: hub never published at slot 2: no refutation exists and the user's
//!   timeout split pays after `delta`;
//! - D: the depth-1 single-head form (user's legal opening stands, hub's
//!   disprove fails, the user's checked split pays UserWins);
//! - E: the game is OVER (the user's win at depth 5): the winner's
//!   terminal exhibit (D37) parks the attested pair under the
//!   `status != OPEN` gate and the self-checking split pays
//!   R(parked terminal) = UserWins — the 4b graph's terminal-claim hole
//!   closed;
//! - F: the gate rejects an OPEN state (no mid-game self-claim), and a
//!   drawn game at depth 9 — unresolvable in 4b's graph — pays Draw.
//!
//! Venue entries are signed for real (the mover's per-depth state key): the
//! D41 authorship fragment on every refute/exhibit leaf checks the
//! presented preimages against the parked head's claimed state, so the
//! witness carries them — and path G shows a garbage-signed attested entry
//! admits no refutation (the D40/PS9 hole, closed).

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PresignedTx, Role};
use lngap_contract::Contract;
use lngap_ec_wots::{Attester, EpochTable};
use lngap_factchain::slot::SlotEntry;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsParams, WotsSig};
use lngap_pos::instance::{self, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNK_START, HEAD_CHUNKS};
use lngap_pos::ttt;
use lngap_pos::{PosMiner, SealedBlock, HEADER_CHUNKS};
use lngap_tictactoe::{Board, TicTacToe};

const SEED: [u8; 32] = [7u8; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
const MAX_DEPTH: u32 = 9;
/// The slot the absence claim is played at in paths A-C.
const D: u32 = 2;
/// The ttt state key's WOTS length in digits (6 message + 2 checksum over
/// the 3 signed state bytes, D43).
const STATE_DIGITS: usize = 8;

fn state_u32(b: &Board) -> u32 {
    lngap_lamport::bits_to_uint(&TicTacToe.state_bits(b))
}

/// The venue's epoch tables, published at contract open (the attester's
/// deterministic per-slot registry).
fn epoch_tables() -> Vec<EpochTable> {
    let attester = Attester::new(SEED);
    (0..=MAX_DEPTH as u64).map(|s| attester.epoch_table(s, HEADER_CHUNKS)).collect()
}

/// The venue: the blocks sealed so far, by slot.
struct Venue {
    miner: PosMiner,
    sealed: std::collections::HashMap<u32, SealedBlock>,
}

impl Venue {
    fn new() -> Venue {
        let attester = Attester::new(SEED);
        let (gen, _table0) = lngap_pos::genesis(&attester);
        Venue {
            miner: PosMiner::new(SEED, gen.header.digest(), 0),
            sealed: std::collections::HashMap::new(),
        }
    }
    /// Seal `slot` carrying `mv` played from `board` by its mover (the
    /// venue is a dumb sequencer: an illegal move seals just the same; the
    /// entry claims the naive overwrite), SIGNED with the mover's state key
    /// over the claimed state (D41: the refute/exhibit leaves check it).
    /// Returns the claimed new board.
    fn seal_move(&mut self, slot: u32, board: &Board, mv: u8, ks: &mut KeyStore) -> Board {
        let mover = instance::mover_at(slot);
        let new = TicTacToe.transition(board, &mv, mover).unwrap_or_else(|_| {
            let mut n = board.clone();
            n.cells[mv as usize] = if mover == Role::User { 1 } else { 2 };
            n.turn = mover.other();
            n
        });
        let sig = ks.sign_wots(&instance::state_label(CONTRACT_ID, 1, slot), &state_u32(&new).to_be_bytes()[1..]).unwrap();
        let entry = SlotEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            mv,
            state: state_u32(&new),
            sigs: sig.hashes.clone(),
        };
        self.miner.submit(entry.encode());
        let (block, table) = self.miner.seal_next(slot).unwrap();
        assert!(block.verify_seal(&table).is_ok());
        self.sealed.insert(slot, block);
        new
    }
    /// Seal `slot` with a legal-looking but GARBAGE-SIGNED entry (the
    /// D41/PS9 case): the sigs region is junk. The venue attests existence,
    /// never validity — it seals anyway.
    fn seal_move_junk(&mut self, slot: u32, board: &Board, mv: u8) {
        let mover = instance::mover_at(slot);
        let new = TicTacToe.transition(board, &mv, mover).unwrap();
        let entry = SlotEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            mv,
            state: state_u32(&new),
            sigs: vec![[0x11; 20]; STATE_DIGITS],
        };
        self.miner.submit(entry.encode());
        let (block, table) = self.miner.seal_next(slot).unwrap();
        assert!(block.verify_seal(&table).is_ok());
        self.sealed.insert(slot, block);
    }
    /// Seal `slot` empty (the mover stalls).
    fn seal_empty(&mut self, slot: u32) {
        let (block, table) = self.miner.seal_next(slot).unwrap();
        assert!(block.verify_seal(&table).is_ok());
        self.sealed.insert(slot, block);
    }
    fn head(&self, slot: u32) -> [u8; 48] {
        self.sealed[&slot].header.head()
    }
}

/// The two parties, their keystores, and the agreed instance.
struct Game {
    user: PartyKeys,
    hub: PartyKeys,
    user_ks: KeyStore,
    hub_ks: KeyStore,
    params: ChannelParams,
    pubs: [lngap_channel::PartyPubKeys; 2],
    inst: PosInstance,
}

impl Game {
    /// The draft: both sides generate their per-depth keys under the
    /// standard labels, exchange the public offers, and build the SAME
    /// instance (checked: both trees agree, exhibits included).
    fn open(btc_open: u32, deadline: u32, value: Amount, tables: &[EpochTable]) -> Game {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("pos4b/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("pos4b/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("pos4b/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("pos4b/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH, instance::Game::Ttt).unwrap();
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH, instance::Game::Ttt).unwrap();
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH).unwrap();
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH).unwrap();
        assert_eq!(keys_u, keys_h, "the merged key sets must agree");
        let inst_u = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, instance::Game::Ttt, btc_open, 1, keys_u).unwrap();
        let inst_h = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, instance::Game::Ttt, btc_open, 1, keys_h).unwrap();
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
        let pubs = [user.public(), hub.public()];
        let g = Game {
            user,
            hub,
            user_ks,
            hub_ks,
            params,
            pubs,
            inst: inst_u,
        };
        // the draft's agreement property: both sides build the same output
        let ctx = g.ctx();
        assert_eq!(
            g.inst.tree(&ctx, tables).unwrap().script_pubkey(),
            inst_h.tree(&ctx, tables).unwrap().script_pubkey(),
            "both parties must build the same contract output"
        );
        g
    }
    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx {
            params: &self.params,
            keys: &self.pubs,
            broadcaster: Role::User,
            seq: 1,
            rev_hash: [0u8; 20],
        }
    }
    fn keys_of(&mut self, r: Role) -> (&mut KeyStore, &Keypair) {
        match r {
            Role::User => (&mut self.user_ks, &self.user.payment),
            Role::Hub => (&mut self.hub_ks, &self.hub.payment),
        }
    }
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &bitcoin::ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf)
        .unwrap()
        .as_ref()
        .to_vec()
}

fn sign_with(secret: &SecretKey, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tx(&Keypair::from_secret_key(SECP256K1, secret), tx, prev, leaf)
}

fn skel<'a>(graph: &'a [PresignedTx], label: &str) -> &'a PresignedTx {
    graph.iter().find(|p| p.label == label).unwrap_or_else(|| panic!("no skeleton {label}"))
}

/// Seal `slot` with `mv` played by its mover, signed with the mover's
/// state key from that side's keystore (D41: the venue entries are really
/// signed).
fn seal_move(path: &mut Path, g: &mut Game, slot: u32, mv: u8) {
    let mover = instance::mover_at(slot);
    path.board = path.venue.seal_move(slot, &path.board, mv, g.keys_of(mover).0);
}

/// The state-key signature over a sealed head's CLAIMED state (the D41
/// authorship block), from that depth's mover's keystore — the same
/// message as the published entry's, so the same signature (idempotent).
fn auth_sig(g: &mut Game, d: u32, head: &[u8; 48]) -> WotsSig {
    g.keys_of(instance::mover_at(d))
        .0
        .sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &ttt::auth_message(head))
        .unwrap()
}

/// One playing of the dance from a funded contract output.
struct Path {
    venue: Venue,
    graph: Vec<PresignedTx>,
    board: Board,
    /// The pair reveal, public once the refutation is mined (the disprove
    /// and checked-split spends copy it).
    pair_sig: Option<WotsSig>,
}

impl Path {
    fn open(rt: &Regtest, g: &Game, tables: &[EpochTable]) -> Path {
        let ctx = g.ctx();
        let tree = g.inst.tree(&ctx, tables).unwrap();
        let (c_op, c_prev) = rt.fund(&tree.script_pubkey(), g.inst.value).unwrap();
        let graph = g.inst.graph(&ctx, c_op, &c_prev, tables).unwrap();
        Path { venue: Venue::new(), graph, board: Board::empty(), pair_sig: None }
    }

    /// Broadcast the pre-signed absence claim at depth `d`; return A's
    /// (outpoint, prevout).
    fn claim(&self, rt: &Regtest, g: &Game, d: u32) -> (OutPoint, TxOut) {
        let p = skel(&self.graph, &format!("absent_{d}"));
        let mut tx = p.tx.clone();
        let sig_u = sign_tx(&g.user.payment, &tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &tx, &p.prevouts[0], &p.leaf.script);
        tx.input[0].witness = tapscript_witness(&[sig_h, sig_u], &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the absence claim must mine: {e}"));
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone())
    }

    /// The mover's refutation: the readout of slots `d-1` and `d` (slot `d`
    /// alone at depth 1) tied to the pair reveal, plus the mover's
    /// signature on the pre-signed skeleton. Returns P's (outpoint, prevout).
    fn refute(&mut self, rt: &Regtest, g: &mut Game, d: u32) -> (OutPoint, TxOut) {
        let p = skel(&self.graph, &format!("absent_{d}/refute"));
        let mut tx = p.tx.clone();
        let a_prev = p.prevouts[0].clone();
        let new_head = self.venue.head(d);
        let w = if d >= 2 {
            let prev_head = self.venue.head(d - 1);
            let mut msg = prev_head.to_vec();
            msg.extend_from_slice(&new_head);
            let pair_sig = g.keys_of(instance::mover_at(d)).0.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).unwrap();
            self.pair_sig = Some(pair_sig.clone());
            let prev_sig = auth_sig(g, d - 1, &prev_head);
            let new_sig = auth_sig(g, d, &new_head);
            let new_block = &self.venue.sealed[&d];
            let prev_block = &self.venue.sealed[&(d - 1)];
            let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            let sigs_prev: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&prev_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&new_sig, &prev_sig])
        } else {
            let sig = g.keys_of(instance::mover_at(d)).0.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &new_head).unwrap();
            self.pair_sig = Some(sig.clone());
            let new_sig = auth_sig(g, d, &new_head);
            let new_block = &self.venue.sealed[&d];
            let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            refute::refute_witness(&sigs, &sig, &new_sig)
        };
        let mover_sig = sign_tx(g.payment_of(instance::mover_at(d)), &tx, &a_prev, &p.leaf.script);
        let mut w = w;
        w.push(mover_sig);
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the refutation at depth {d} must mine: {e}"));
        println!("REGTEST 4b: refutation at depth {d}: {} vB", tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone())
    }

    /// The depth-`d` refutation carrying the entry's OWN junk preimages
    /// instead of the mover's reveal over the claimed state — the D41
    /// negative, assembled but NOT broadcast (the caller test_accepts the
    /// rejection).
    fn refute_with_preimages(&mut self, rt: &Regtest, g: &mut Game, d: u32, junk: bool) -> Transaction {
        assert!(junk, "the honest refutation is refute()");
        let _ = rt;
        let p = skel(&self.graph, &format!("absent_{d}/refute"));
        let tx = &p.tx;
        let a_prev = &p.prevouts[0];
        let (prev_head, new_head) = (self.venue.head(d - 1), self.venue.head(d));
        let mk_junk = |head: &[u8; 48]| WotsSig::from_hashes(WotsParams::for_bytes(3), &ttt::auth_message(head), vec![[0x11; 20]; STATE_DIGITS]).unwrap();
        let mut msg = prev_head.to_vec();
        msg.extend_from_slice(&new_head);
        let pair_sig = g
            .keys_of(instance::mover_at(d))
            .0
            .sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg)
            .unwrap();
        let new_block = &self.venue.sealed[&d];
        let prev_block = &self.venue.sealed[&(d - 1)];
        let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], tx, a_prev, &p.leaf.script))
            .collect();
        let sigs_prev: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&prev_block.attestation.secrets[HEAD_CHUNK_START + j], tx, a_prev, &p.leaf.script))
            .collect();
        let mut w = refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&mk_junk(&new_head), &mk_junk(&prev_head)]);
        let mover_sig = sign_tx(g.payment_of(instance::mover_at(d)), tx, a_prev, &p.leaf.script);
        w.push(mover_sig);
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        tx
    }

    /// The exhibit witness at depth `d` (the gated pair readout plus both
    /// parties' signatures), WITHOUT broadcasting — the open-state gate
    /// negative needs it dry.
    fn exhibit_witness(&mut self, g: &mut Game, d: u32) -> Vec<Vec<u8>> {
        let p = skel(&self.graph, &format!("exhibit_{d}"));
        let tx = &p.tx;
        let c_prev = &p.prevouts[0];
        let new_head = self.venue.head(d);
        let prev_head = self.venue.head(d - 1);
        let mut msg = prev_head.to_vec();
        msg.extend_from_slice(&new_head);
        let pair_sig = {
            let (mover_ks, _) = g.keys_of(instance::mover_at(d));
            mover_ks.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).unwrap()
        };
        self.pair_sig = Some(pair_sig.clone());
        let prev_sig = auth_sig(g, d - 1, &prev_head);
        let new_sig = auth_sig(g, d, &new_head);
        let new_block = &self.venue.sealed[&d];
        let prev_block = &self.venue.sealed[&(d - 1)];
        let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], tx, c_prev, &p.leaf.script))
            .collect();
        let sigs_prev: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&prev_block.attestation.secrets[HEAD_CHUNK_START + j], tx, c_prev, &p.leaf.script))
            .collect();
        let mut w = refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&new_sig, &prev_sig]);
        let sig_u = sign_tx(&g.user.payment, tx, c_prev, &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, tx, c_prev, &p.leaf.script);
        w.push(sig_h);
        w.push(sig_u);
        w
    }

    /// The winner's terminal exhibit at depth `d` (D37): the gated two-head
    /// readout of slots `d-1` and `d` under the depth-`d` refute key, on
    /// the pre-signed 2-of-2 skeleton spending the CONTRACT output (its
    /// output is pinned to the refuted tree of depth `d`). Returns E's
    /// (outpoint, prevout).
    fn exhibit(&mut self, rt: &Regtest, g: &mut Game, d: u32) -> (OutPoint, TxOut) {
        let w = self.exhibit_witness(g, d);
        let p = skel(&self.graph, &format!("exhibit_{d}"));
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the exhibit at depth {d} must mine: {e}"));
        println!("REGTEST 4c: terminal exhibit at depth {d}: {} vB", tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone())
    }

    /// The claimant's disprove spend over the parked tuple (built at
    /// runtime — the claimant's own money claim; the pair reveal is copied
    /// from the refutation's published witness). Caller mines or rejects.
    fn disprove(&self, rt: &Regtest, g: &Game, d: u32, p_op: OutPoint, p_prev: &TxOut, leaf: &str) -> Transaction {
        let _ = rt;
        let ctx = g.ctx();
        let p_tree = g.inst.refuted_tree(&ctx, d).unwrap();
        let l = p_tree.leaf(leaf).unwrap();
        let claimant = instance::mover_at(d).other();
        let payout = g.keys_of_pub(claimant).payout_spk.clone();
        let mut tx = lngap_btc::tx::build_spend(
            p_op,
            &l.timelock,
            vec![TxOut { value: p_prev.value - g.params.presign_fee, script_pubkey: payout }],
        );
        let dsig = sign_tx(g.payment_of(claimant), &tx, p_prev, &l.script);
        let mut w = refute::wots_wire(self.pair_sig.as_ref().expect("the refutation went first"));
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block(leaf).unwrap());
        tx
    }

    /// A timeout-split witness off the claim output (the claimant's code).
    fn timeout_witness(&self, g: &mut Game, d: u32, code: u8) -> Vec<Vec<u8>> {
        let p = skel(&self.graph, &format!("absent_{d}/split_{}", self.outcome_name(code)));
        let reveal = g.keys_of(instance::mover_at(d).other()).0.reveal_uint(&instance::ccode_label(CONTRACT_ID, 1, d), u32::from(code)).unwrap();
        let sig_u = sign_tx(&g.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let mut w = reveal.consumption_order();
        w.reverse();
        w.push(sig_h);
        w.push(sig_u);
        w
    }

    /// A self-checking split witness off the refuted output (the mover's
    /// code reveal over the pair reveal).
    fn checked_witness(&self, g: &mut Game, d: u32, code: u8) -> Vec<Vec<u8>> {
        let reveal = g
            .keys_of(instance::mover_at(d))
            .0
            .reveal_uint(&instance::code_label(CONTRACT_ID, 1, d), u32::from(code))
            .unwrap();
        self.checked_witness_with(g, d, code, &reveal)
    }

    /// A self-checking split witness off an EXHIBIT output (the exhibit
    /// output's tree IS the refuted tree of depth `d`; the skeletons are
    /// labelled `exhibit_d/…`).
    fn exhibit_checked_witness(&self, g: &mut Game, d: u32, code: u8) -> Vec<Vec<u8>> {
        let reveal = g
            .keys_of(instance::mover_at(d))
            .0
            .reveal_uint(&instance::code_label(CONTRACT_ID, 1, d), u32::from(code))
            .unwrap();
        self.checked_witness_at(g, &format!("exhibit_{d}"), code, &reveal)
    }

    /// As [`Path::checked_witness`], with an explicitly supplied code
    /// reveal (for the adversarial wrong-code negative: the honest
    /// keystore's one-time reveal discipline refuses to equivocate).
    fn checked_witness_with(&self, g: &Game, d: u32, code: u8, reveal: &lngap_lamport::Reveal) -> Vec<Vec<u8>> {
        self.checked_witness_at(g, &format!("absent_{d}/refuted"), code, reveal)
    }

    fn checked_witness_at(&self, g: &Game, base: &str, code: u8, reveal: &lngap_lamport::Reveal) -> Vec<Vec<u8>> {
        let p = skel(&self.graph, &format!("{base}/split_{}", self.outcome_name(code)));
        let sig_u = sign_tx(&g.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        ttt::checked_split_witness(sig_u, sig_h, reveal, self.pair_sig.as_ref().expect("the refutation/exhibit went first"))
    }

    fn outcome_name(&self, code: u8) -> &'static str {
        match code {
            0 => "UserWins",
            1 => "HubWins",
            _ => "Draw",
        }
    }
}

/// A reveal of the mover's code key to a FALSE value — the adversary's
/// move, reproduced by hand because the honest keystore refuses to
/// equivocate (the in-leaf `code == R(parked)` check is what actually
/// defends the split).
fn adversarial_code_reveal(d: u32, code: u8) -> lngap_lamport::Reveal {
    let seed = match instance::mover_at(d) {
        Role::User => Seed::from_label("pos4b/user-ks"),
        Role::Hub => Seed::from_label("pos4b/hub-ks"),
    };
    let sk = lngap_lamport::SecretKey::from_entropy(
        lngap_contract::CODE_BITS,
        seed.derive_bytes(&format!("lamport/{}", instance::code_label(CONTRACT_ID, 1, d))),
    );
    sk.reveal_bits(&lngap_lamport::uint_to_bits(u32::from(code), lngap_contract::CODE_BITS))
        .unwrap()
}

impl Game {
    fn keys_of_pub(&self, r: Role) -> lngap_channel::PartyPubKeys {
        match r {
            Role::User => self.user.public(),
            Role::Hub => self.hub.public(),
        }
    }
    fn payment_of(&self, r: Role) -> &Keypair {
        match r {
            Role::User => &self.user.payment,
            Role::Hub => &self.hub.payment,
        }
    }
}

/// Broadcast a pre-signed skeleton with the given witness.
fn run(rt: &Regtest, p: &PresignedTx, w: Vec<Vec<u8>>) -> Transaction {
    let mut tx = p.tx.clone();
    tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
    rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("{} must mine: {e}", p.label));
    tx
}

/// The skeleton with the witness attached but NOT broadcast (for negatives).
fn dry(p: &PresignedTx, w: Vec<Vec<u8>>) -> Transaction {
    let mut tx = p.tx.clone();
    tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
    tx
}

#[test]
fn wired_pos_graph() {
    let rt = Regtest::start().unwrap();
    let tables = epoch_tables();
    let value = Amount::from_sat(200_000);

    // ================= path A: an illegal (occupied-cell) move is killed ==
    {
        let g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut g = g;
        let mut path = Path::open(&rt, &g, &tables);
        assert_eq!(path.graph.len(), 166, "the wired graph: settle + 9 x (claim, refute, 3 + 3 splits) + 5 x (exhibit, 3 splits) + 9 per-depth equivocation exhibits (D39, D43) + 8 x (counter, refute, 3 + 3 splits) (D44)");
        // slot 1: user's legal X@4; slot 2: hub plays the OCCUPIED cell 4
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 1, 4);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 2, 4);
        // past the claim window and the broadcaster's to_self_delay
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        let (_a_op, _a_prev) = path.claim(&rt, &g, D);
        let (p_op, p_prev) = path.refute(&rt, &mut g, D);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        // the wrong disprove leaf cannot fire
        let bad = path.disprove(&rt, &g, D, p_op, &p_prev, "disprove_cell_occupied_5");
        assert!(rt.test_accept(&bad).is_err(), "cell_occupied_5 must not fire on mv = 4");
        // the mover's split cannot beat the disprove window... (it also
        // reads a state it cannot honestly cash: R of an illegal tuple)
        let w = path.checked_witness(&mut g, D, 1);
        let early = dry(skel(&path.graph, "absent_2/refuted/split_HubWins"), w);
        assert!(rt.test_accept(&early).is_err(), "the mover's split must wait out the disprove window");
        // the occupied cell is disproved: the user takes the pot
        let dtx = path.disprove(&rt, &g, D, p_op, &p_prev, "disprove_cell_occupied_4");
        rt.mine_with(&[dtx.clone()]).unwrap_or_else(|e| panic!("the occupied-cell disprove must mine: {e}"));
        println!("REGTEST 4b: disprove cell_occupied_4: {} vB", dtx.vsize());
    }

    // ================= path B: a legal refutation stands =================
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 1, 4);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 2, 0); // legal: O@0
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        let (_a_op, _a_prev) = path.claim(&rt, &g, D);
        let (p_op, p_prev) = path.refute(&rt, &mut g, D);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        for leaf in ["disprove_cell_occupied_0", "disprove_status_mismatch", "disprove_board_mismatch_0"] {
            let bad = path.disprove(&rt, &g, D, p_op, &p_prev, leaf);
            assert!(rt.test_accept(&bad).is_err(), "{leaf} must not fire on a legal move");
        }
        // the mover's split with a FALSE code is rejected in-leaf
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        let w = path.checked_witness_with(&g, D, 0, &adversarial_code_reveal(D, 0)); // claims UserWins
        let bad = dry(skel(&path.graph, "absent_2/refuted/split_UserWins"), w);
        assert!(rt.test_accept(&bad).is_err(), "R(parked state) = HubWins; the UserWins code must fail");
        // the true code pays the mover (an open state forfeits the claimant)
        let w = path.checked_witness(&mut g, D, 1);
        let tx = run(&rt, skel(&path.graph, "absent_2/refuted/split_HubWins"), w);
        println!("REGTEST 4b: checked split (refuted, legal): {} vB", tx.vsize());
    }

    // ================= path C: a real stall pays the claimant ============
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 1, 4);
        rt.mine(1).unwrap();
        path.venue.seal_empty(2); // hub stalls
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        let (_a_op, _a_prev) = path.claim(&rt, &g, D);
        // no refutation exists for an empty slot; the timeout split pays
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let w = path.timeout_witness(&mut g, D, 0);
        let tx = run(&rt, skel(&path.graph, "absent_2/split_UserWins"), w);
        println!("REGTEST 4b: timeout split: {} vB", tx.vsize());
    }

    // ================= path D: the depth-1 single-head form ==============
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 1, 4); // legal opening
        rt.mine(2).unwrap(); // past claim_from(1)
        let (_a_op, _a_prev) = path.claim(&rt, &g, 1); // hub claims absence
        let (p_op, p_prev) = path.refute(&rt, &mut g, 1);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let bad = path.disprove(&rt, &g, 1, p_op, &p_prev, "disprove_board_mismatch_4");
        assert!(rt.test_accept(&bad).is_err(), "a legal opening must not be disprovable");
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        // the wrong code fails; R(s_1) = open, hub on turn -> UserWins
        let w = path.checked_witness_with(&g, 1, 1, &adversarial_code_reveal(1, 1));
        let bad = dry(skel(&path.graph, "absent_1/refuted/split_HubWins"), w);
        assert!(rt.test_accept(&bad).is_err(), "the mover's false code must fail");
        let w = path.checked_witness(&mut g, 1, 0);
        let tx = run(&rt, skel(&path.graph, "absent_1/refuted/split_UserWins"), w);
        println!("REGTEST 4b: checked split (depth 1): {} vB", tx.vsize());
    }

    // ============ path E: the terminal exhibit pays the winner (D37) ====
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        // the winning line: X@0, O@3, X@1, O@4, X@2 — the top row,
        // terminal at depth 5 with the user the last mover
        for (i, mv) in [0u8, 3, 1, 4, 2].into_iter().enumerate() {
            rt.mine(1).unwrap();
            seal_move(&mut path, &mut g, i as u32 + 1, mv);
        }
        assert!(TicTacToe.turn(&path.board).is_none(), "the line must be terminal at depth 5");
        // the loser cannot exhibit: the depth-5 refute key is the user's,
        // never generated in the hub's keystore
        assert!(
            g.hub_ks.sign_wots(&instance::refute_label(CONTRACT_ID, 1, 5), &[0u8; 96]).is_err(),
            "the hub holds no depth-5 refute key"
        );
        // past the window, the winner exhibits: the parked pair is the
        // attested terminal tuple
        let need = g.inst.claim_from(5).saturating_sub(rt.height().unwrap()) + 1;
        rt.mine(u64::from(need)).unwrap();
        let (e_op, e_prev) = path.exhibit(&rt, &mut g, 5);
        // no disprove fires on the legal terminal move
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        for leaf in ["disprove_wrong_slot", "disprove_status_mismatch", "disprove_board_mismatch_2"] {
            let bad = path.disprove(&rt, &g, 5, e_op, &e_prev, leaf);
            assert!(rt.test_accept(&bad).is_err(), "{leaf} must not fire on the exhibited terminal move");
        }
        // the split pays R(parked terminal) = UserWins — a false code fails
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        let w = path.checked_witness_at(&g, "exhibit_5", 1, &adversarial_code_reveal(5, 1)); // claims HubWins
        let bad = dry(skel(&path.graph, "exhibit_5/split_HubWins"), w);
        assert!(rt.test_accept(&bad).is_err(), "R(parked terminal) = UserWins; the HubWins code must fail");
        let w = path.exhibit_checked_witness(&mut g, 5, 0);
        let tx = run(&rt, skel(&path.graph, "exhibit_5/split_UserWins"), w);
        println!("REGTEST 4c: exhibit split (win at 5): {} vB", tx.vsize());
    }

    // ============ path F: the gate rejects open states; a draw pays =====
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        // the drawn line XOX/XOO/OXX: 0,1,3,4,2 then 5,7,6,8
        for (i, mv) in [0u8, 1, 3, 4, 2].into_iter().enumerate() {
            rt.mine(1).unwrap();
            seal_move(&mut path, &mut g, i as u32 + 1, mv);
        }
        assert!(TicTacToe.turn(&path.board).is_some(), "the board must still be OPEN at depth 5");
        // the gate: the exhibit leaf rejects an OPEN parked state even
        // though the readout and both signatures are honest — no mid-game
        // self-claim
        let need = g.inst.claim_from(5).saturating_sub(rt.height().unwrap()) + 1;
        rt.mine(u64::from(need)).unwrap();
        let w = path.exhibit_witness(&mut g, 5);
        let bad = dry(skel(&path.graph, "exhibit_5"), w);
        assert!(rt.test_accept(&bad).is_err(), "the status gate must reject an open state");
        // play on to the draw at depth 9 — the case 4b's graph could not
        // resolve at all
        for (i, mv) in [5u8, 7, 6, 8].into_iter().enumerate() {
            rt.mine(1).unwrap();
            seal_move(&mut path, &mut g, 6 + i as u32, mv);
        }
        assert!(TicTacToe.turn(&path.board).is_none(), "the line must be a draw at depth 9");
        let need = g.inst.claim_from(9).saturating_sub(rt.height().unwrap()) + 1;
        rt.mine(u64::from(need)).unwrap();
        let (e_op, e_prev) = path.exhibit(&rt, &mut g, 9);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        for leaf in ["disprove_wrong_slot", "disprove_status_mismatch", "disprove_board_mismatch_8"] {
            let bad = path.disprove(&rt, &g, 9, e_op, &e_prev, leaf);
            assert!(rt.test_accept(&bad).is_err(), "{leaf} must not fire on the drawn terminal move");
        }
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        let w = path.exhibit_checked_witness(&mut g, 9, 2);
        let tx = run(&rt, skel(&path.graph, "exhibit_9/split_Draw"), w);
        println!("REGTEST 4c: exhibit split (draw at 9): {} vB", tx.vsize());
    }

    // ============ path G: a garbage-signed attested entry is not a move ==
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 1, 4); // X@4, really signed
        rt.mine(1).unwrap();
        // the hub's slot-2 entry claims a legal move (O@0) but its sigs
        // region is junk (the PS9 hole, D40 — closed by D41)
        path.venue.seal_move_junk(2, &path.board, 0);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        let (_a_op, _a_prev) = path.claim(&rt, &g, 2);
        // the hub declines to adopt the junk (its key never signed that
        // state): a refutation carrying the entry's own junk preimages
        // fails the authorship fragment on-chain
        let bad = path.refute_with_preimages(&rt, &mut g, 2, true);
        assert!(rt.test_accept(&bad).is_err(), "junk preimages must fail the authorship fragment");
        // (the hub COULD adopt the entry by signing its claimed state —
        // that would be its move; it declines, so the absence resolves)
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let w = path.timeout_witness(&mut g, 2, 0);
        let tx = run(&rt, skel(&path.graph, "absent_2/split_UserWins"), w);
        println!("REGTEST 6/PS9: garbage-signed entry held no refutation; timeout split: {} vB", tx.vsize());
    }

    // ============ path H: a mismatched re-commitment fails the tied readout
    {
        // the pair reveal signs a TAMPERED new head (one padding nibble
        // off, so the CLAIMED state is unchanged and the D41 authorship
        // passes): the readout's possession sigs cover the REAL attested
        // heads, so the tampered digit selects an anticipation point whose
        // secret nobody holds — with the D42 tied readout the tie IS the
        // point selection. (This is the sim_refute mismatched-recommitment
        // negative, testable only with real sigs — the sim stubs CHECKSIG.)
        let mut g = Game::open(
            rt.height().unwrap() + 1,
            rt.height().unwrap() + 400,
            value,
            &tables,
        );
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 1, 4);
        rt.mine(1).unwrap();
        seal_move(&mut path, &mut g, 2, 0);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, D);
        let p = skel(&path.graph, "absent_2/refute");
        let a_prev = p.prevouts[0].clone();
        let new_head = path.venue.head(D);
        let prev_head = path.venue.head(D - 1);
        let mut tampered = new_head;
        tampered[30] ^= 1; // ttt's padding region: the claimed state is unchanged
        let mut msg = prev_head.to_vec();
        msg.extend_from_slice(&tampered);
        let pair_sig = g
            .keys_of(instance::mover_at(D))
            .0
            .sign_wots(&instance::refute_label(CONTRACT_ID, 1, D), &msg)
            .unwrap();
        let prev_sig = auth_sig(&mut g, D - 1, &prev_head);
        let new_sig = auth_sig(&mut g, D, &new_head);
        let mut tx = p.tx.clone();
        let new_block = &path.venue.sealed[&D];
        let prev_block = &path.venue.sealed[&(D - 1)];
        let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
            .collect();
        let sigs_prev: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&prev_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
            .collect();
        let mut w = refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&new_sig, &prev_sig]);
        w.push(sign_tx(g.payment_of(instance::mover_at(D)), &tx, &a_prev, &p.leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        // mine_with (generateblock), not test_accept: the fee placeholder is
        // below the relay floor for a ~30 kvB tx and must not mask the
        // script-level rejection
        assert!(
            rt.mine_with_check(&tx).is_err(),
            "the tampered re-commitment must fail the tied readout"
        );
        println!("REGTEST 4b: mismatched re-commitment rejected by the tied readout");
    }
}
