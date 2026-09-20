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
//!   disprove fails, the user's checked split pays UserWins).
//!
//! The venue entries' state signatures are dummies here — a garbage-signed
//! attested entry is the PoS sig exhibit's case (deferred, D36); the leaves
//! under test judge the head's content fields.

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
use lngap_lamport::winternitz::WotsSig;
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
    /// entry claims the naive overwrite). Returns the claimed new board.
    fn seal_move(&mut self, slot: u32, board: &Board, mv: u8) -> Board {
        let mover = instance::mover_at(slot);
        let new = TicTacToe.transition(board, &mv, mover).unwrap_or_else(|_| {
            let mut n = board.clone();
            n.cells[mv as usize] = if mover == Role::User { 1 } else { 2 };
            n.turn = mover.other();
            n
        });
        let entry = SlotEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            mv,
            state: state_u32(&new),
            sigs: vec![[0x11; 20]; 21],
        };
        self.miner.submit(entry.encode());
        let (block, table) = self.miner.seal_next(slot).unwrap();
        assert!(block.verify_seal(&table).is_ok());
        self.sealed.insert(slot, block);
        new
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
    /// instance (checked: both trees agree).
    fn open(btc_open: u32, deadline: u32, value: Amount) -> Game {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("pos4b/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("pos4b/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("pos4b/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("pos4b/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH).unwrap();
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH).unwrap();
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH).unwrap();
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH).unwrap();
        assert_eq!(keys_u, keys_h, "the merged key sets must agree");
        let inst_u = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, btc_open, 1, keys_u).unwrap();
        let inst_h = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, btc_open, 1, keys_h).unwrap();
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
            g.inst.tree(&ctx).unwrap().script_pubkey(),
            inst_h.tree(&ctx).unwrap().script_pubkey(),
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
        let tree = g.inst.tree(&ctx).unwrap();
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
        let (mover_ks, mover_payment) = g.keys_of(instance::mover_at(d));
        let new_head = self.venue.head(d);
        let w = if d >= 2 {
            let prev_head = self.venue.head(d - 1);
            let mut msg = prev_head.to_vec();
            msg.extend_from_slice(&new_head);
            let pair_sig = mover_ks.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).unwrap();
            self.pair_sig = Some(pair_sig.clone());
            let new_block = &self.venue.sealed[&d];
            let prev_block = &self.venue.sealed[&(d - 1)];
            let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            let sigs_prev: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&prev_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            refute::refute_witness_pair(&prev_head, &sigs_prev, &new_head, &sigs_new, &pair_sig)
        } else {
            let sig = mover_ks.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &new_head).unwrap();
            self.pair_sig = Some(sig.clone());
            let new_block = &self.venue.sealed[&d];
            let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            refute::refute_witness(&new_head, &sigs, &sig)
        };
        let mover_sig = sign_tx(mover_payment, &tx, &a_prev, &p.leaf.script);
        let mut w = w;
        w.push(mover_sig);
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the refutation at depth {d} must mine: {e}"));
        println!("REGTEST 4b: refutation at depth {d}: {} vB", tx.vsize());
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

    /// As [`Path::checked_witness`], with an explicitly supplied code
    /// reveal (for the adversarial wrong-code negative: the honest
    /// keystore's one-time reveal discipline refuses to equivocate).
    fn checked_witness_with(&self, g: &Game, d: u32, code: u8, reveal: &lngap_lamport::Reveal) -> Vec<Vec<u8>> {
        let p = skel(&self.graph, &format!("absent_{d}/refuted/split_{}", self.outcome_name(code)));
        let sig_u = sign_tx(&g.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        ttt::checked_split_witness(sig_u, sig_h, &reveal, self.pair_sig.as_ref().expect("the refutation went first"))
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
        let g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value);
        let mut g = g;
        let mut path = Path::open(&rt, &g, &tables);
        assert_eq!(path.graph.len(), 73, "the wired graph: settle + 9 x (claim, refute, 3 + 3 splits)");
        // slot 1: user's legal X@4; slot 2: hub plays the OCCUPIED cell 4
        rt.mine(1).unwrap();
        path.board = path.venue.seal_move(1, &path.board, 4);
        rt.mine(1).unwrap();
        path.venue.seal_move(2, &path.board, 4);
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
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.board = path.venue.seal_move(1, &path.board, 4);
        rt.mine(1).unwrap();
        path.board = path.venue.seal_move(2, &path.board, 0); // legal: O@0
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
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.board = path.venue.seal_move(1, &path.board, 4);
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
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.board = path.venue.seal_move(1, &path.board, 4); // legal opening
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
}
