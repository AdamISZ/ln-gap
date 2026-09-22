//! The wired PoS absence-claim graph for CHESS on regtest
//! (POS_FACTCHAIN_PLAN.md step 7's PC gap; D42): the chess disprove family
//! over the parked pair, played end-to-end with per-depth key sets
//! generated in the two parties' keystores under the draft's label
//! discipline, real signed venue entries (336-bit state keys), and the
//! venue's epoch tables published at setup.
//!
//! Paths mined (the node enforcing real timelocks):
//!
//! - A: hub's slot-2 move is ILLEGAL (a bishop jumps a pawn): the user
//!   claims absence, hub's two-head refutation parks the attested pair,
//!   and the user's `chess_ray` disprove takes the pot after `delta`;
//! - B: hub's slot-2 move is legal: no disprove fires, and the mover's
//!   SELF-CHECKING split pays R(parked state) = HubWins (the side to
//!   move — white — forfeits) after `delta + delta'`; the wrong code is
//!   rejected in-leaf;
//! - C: hub never published at slot 2: no refutation exists and the
//!   user's timeout split pays after `delta`;
//! - D: the depth-1 single-head form (the constant-prior pad): the
//!   user's legal opening stands, hub's disprove fails, the user's
//!   checked split pays UserWins;
//! - E: the GAME IS OVER — fool's mate (1. f3 e5 2. g4 Qh4#): the mated
//!   user has no legal move at depth 5, so hub's absence claim there is
//!   unanswerable and pays by timeout (THE chess terminal path — chess
//!   has no exhibit family, D42); and when the user nonetheless answers
//!   with an illegal g4g5 (the king still attacked), the
//!   `chess_kingattacked` disprove — a TWO-ELEMENT exhibit — takes the
//!   pot;
//! - F1: the staller claims one depth AHEAD (D44): the hub stalls at 2 and
//!   claims `absent_3`; the user's counter ("you did not move at 2") is
//!   answered by the hub's zero-head refutation, which `wrong_slot` kills;
//!   and, the hub declining, by the user's timeout split off the counter;
//! - F2: a FALSE counter to a due claim: the hub's e7e5 is on the venue,
//!   the user stalls at 3 and counters the hub's due `absent_3` anyway;
//!   the hub refutes on the counter output and its checked split pays;
//! - G: a garbage-signed attested entry admits no refutation (the D41
//!   authorship fragment rejects the junk signature).

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PresignedTx, Role};
use lngap_chess::certificate::find_kind;
use lngap_chess::leaf::{exhibit_values, Kind};
use lngap_chess::{apply, Move};
use lngap_chess_fc::{ChessEntry, ChessState};
use lngap_ec_wots::{Attester, EpochTable};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsParams, WotsSig};
use lngap_pos::chess;
use lngap_pos::instance::{self, Game as WhichGame, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNK_START, HEAD_CHUNKS};
use lngap_pos::ttt;
use lngap_pos::{PosMiner, SealedBlock, HEADER_CHUNKS};

const SEED: [u8; 32] = [7u8; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
/// Fool's mate lands at depth 4; the mated user's slot is depth 5.
const MAX_DEPTH: u32 = 5;
/// The slot the absence claim is played at in paths A-C.
const D: u32 = 2;
/// The chess state key's WOTS length in digits (84 message + 3 checksum
/// over the 42 signed bytes — the 40 state bytes then the move, D43).
const STATE_DIGITS: usize = 87;

/// An entry's authorship message (D43): the 40 state bytes, then the
/// move's two bytes (low first) — `chess::auth_message` of the head.
fn entry_msg(e: &ChessEntry) -> Vec<u8> {
    let mv = u32::from(e.state.mv.to_u16());
    let mut m = e.state.to_e().to_vec();
    m.extend_from_slice(&(mv as u16).to_le_bytes());
    m
}

/// The venue's epoch tables, published at contract open (the attester's
/// deterministic per-slot registry).
fn epoch_tables() -> Vec<EpochTable> {
    let attester = Attester::new(SEED);
    (0..=MAX_DEPTH as u64).map(|s| attester.epoch_table(s, HEADER_CHUNKS)).collect()
}

/// Play `uci` from `s` (natively), if legal.
fn play(s: &ChessState, uci: &str) -> Option<ChessState> {
    let mv = Move::parse(uci)?;
    let mut pos = apply(&s.pos, mv).ok()?;
    pos.fullmove = 0;
    Some(ChessState { pos, mv, depth: s.depth + 1 })
}

/// The move played ignoring legality (an illegal-but-well-formed claimed
/// successor — what a cheating venue entry asserts).
fn pretend(s: &ChessState, uci: &str) -> ChessState {
    let mv = Move::parse(uci).unwrap();
    let mut pos = lngap_chess::certificate::mechanical_successor(&s.pos, mv);
    pos.fullmove = 0;
    ChessState { pos, mv, depth: s.depth + 1 }
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
    /// Seal `slot` with the entry for `state` (after move `state.depth`)
    /// SIGNED with the mover's state key over the signed region (D41: the
    /// refute leaves check it). The venue is a dumb sequencer: an illegal
    /// move seals just the same.
    fn seal_move(&mut self, slot: u32, state: &ChessState, ks: &mut KeyStore) {
        assert_eq!(u32::from(state.depth), slot);
        let mover = instance::mover_at(slot);
        let sig = ks
            .sign_wots(
                &instance::state_label(CONTRACT_ID, 1, slot),
                &entry_msg(&ChessEntry { game_id: GAME_ID, depth: slot as u8, mover: mover.idx() as u8, state: state.clone(), sigs: vec![] }),
            )
            .unwrap();
        let entry = ChessEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            state: state.clone(),
            sigs: sig.hashes.clone(),
        };
        self.miner.submit(entry.encode());
        let (block, table) = self.miner.seal_next(slot).unwrap();
        assert!(block.verify_seal(&table).is_ok());
        self.sealed.insert(slot, block);
    }
    /// Seal `slot` with a legal-looking but GARBAGE-SIGNED entry (the
    /// D41/PS9 case): the sigs region is junk. The venue attests
    /// existence, never validity — it seals anyway.
    fn seal_move_junk(&mut self, slot: u32, state: &ChessState) {
        let mover = instance::mover_at(slot);
        let entry = ChessEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            state: state.clone(),
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
    /// standard labels (the chess game selects the 336-bit state keys),
    /// exchange the public offers, and build the SAME instance.
    fn open(btc_open: u32, deadline: u32, value: Amount, tables: &[EpochTable]) -> Game {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("posc/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("posc/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("posc/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("posc/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Chess).unwrap();
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Chess).unwrap();
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH).unwrap();
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH).unwrap();
        assert_eq!(keys_u, keys_h, "the merged key sets must agree");
        let inst_u = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, WhichGame::Chess, btc_open, 1, keys_u).unwrap();
        let inst_h = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, WhichGame::Chess, btc_open, 1, keys_h).unwrap();
        let params = ChannelParams {
            presign_fee: Amount::from_sat(60_000), // the venue readout must be fee-covered: the chess pair refute is ~53 kvB; the 1k-sat regtest placeholder is below the relay floor for it (D42)
            ..ChannelParams::regtest(Amount::from_sat(400_000))
        };
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

/// The state-key signature over a sealed head's signed region (the D41
/// authorship block), from that depth's mover's keystore — the same
/// message as the published entry's, so the same signature (idempotent).
fn auth_sig(g: &mut Game, d: u32, head: &[u8; 48]) -> WotsSig {
    g.keys_of(instance::mover_at(d))
        .0
        .sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &chess::auth_message(head))
        .unwrap()
}

/// One playing of the dance from a funded contract output.
struct Path {
    venue: Venue,
    graph: Vec<PresignedTx>,
    /// The position after the last sealed move.
    state: ChessState,
    /// The pair reveal, public once a refutation is mined (the disprove
    /// and checked-split spends copy it).
    pair_sig: Option<WotsSig>,
}

impl Path {
    fn open(rt: &Regtest, g: &Game, tables: &[EpochTable]) -> Path {
        let ctx = g.ctx();
        let tree = g.inst.tree(&ctx, tables).unwrap();
        let (c_op, c_prev) = rt.fund(&tree.script_pubkey(), g.inst.value).unwrap();
        let graph = g.inst.graph(&ctx, c_op, &c_prev, tables).unwrap();
        Path {
            venue: Venue::new(),
            graph,
            state: ChessState::initial(),
            pair_sig: None,
        }
    }

    /// Play `uci` (legally or not) into slot `slot`.
    fn seal(&mut self, g: &mut Game, slot: u32, uci: &str, legal: bool) {
        let next = if legal { play(&self.state, uci).expect("a legal scripted line") } else { pretend(&self.state, uci) };
        let mover = instance::mover_at(slot);
        self.venue.seal_move(slot, &next, g.keys_of(mover).0);
        self.state = next;
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

    /// The mover's counter off the depth-`d` claim output (D44): the thin
    /// claim "the claimant did not move at `d - 1`". 2-of-2 pre-signed,
    /// no timelock. Returns the counter output's (outpoint, prevout); its
    /// tree is the depth-`d - 1` claim tree, so the follow-ons use the
    /// `absent_{d}/counter` base label at depth `d - 1`.
    fn counter(&self, rt: &Regtest, g: &Game, d: u32) -> (OutPoint, TxOut) {
        let p = skel(&self.graph, &format!("absent_{d}/counter"));
        let mut tx = p.tx.clone();
        let sig_u = sign_tx(&g.user.payment, &tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &tx, &p.prevouts[0], &p.leaf.script);
        tx.input[0].witness = tapscript_witness(&[sig_h, sig_u], &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the counter must mine: {e}"));
        println!("REGTEST PC: counter off the depth-{d} claim: {} vB", tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone())
    }

    /// The mover's refutation: the readout of slots `d-1` and `d` (slot `d`
    /// alone at depth 1) tied to the pair reveal, the D41 authorship
    /// blocks, plus the mover's signature on the pre-signed skeleton.
    /// Returns P's (outpoint, prevout).
    fn refute(&mut self, rt: &Regtest, g: &mut Game, d: u32) -> (OutPoint, TxOut) {
        self.refute_under(rt, g, d, &format!("absent_{d}"))
    }

    /// As [`Path::refute`] under a claim-shaped output labelled `base`
    /// (`absent_{d}`, or `absent_{d+1}/counter` — the counter output's tree
    /// is the depth-`d` claim tree, D44).
    fn refute_under(&mut self, rt: &Regtest, g: &mut Game, d: u32, base: &str) -> (OutPoint, TxOut) {
        let p = skel(&self.graph, &format!("{base}/refute"));
        let mut tx = p.tx.clone();
        let a_prev = p.prevouts[0].clone();
        let new_head = self.venue.head(d);
        let w = if d >= 2 {
            let prev_head = self.venue.head(d - 1);
            let mut msg = prev_head.to_vec();
            msg.extend_from_slice(&new_head);
            let pair_sig = g.keys_of(instance::mover_at(d)).0.sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).unwrap();
            self.pair_sig = Some(pair_sig.clone());
            let _prev_sig = auth_sig(g, d - 1, &prev_head); // chess authorship is new-head-only (D42); the call keeps the keystore's one-time discipline
            let new_sig = auth_sig(g, d, &new_head);
            let new_block = &self.venue.sealed[&d];
            let prev_block = &self.venue.sealed[&(d - 1)];
            let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            let sigs_prev: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
                .map(|j| sign_with(&prev_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script))
                .collect();
            refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&new_sig])
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
        // with the fee now adequate, test_accept failure would be a real
        // script problem — surface it, but the mine is the assertion
        if let Err(e) = rt.test_accept(&tx) {
            println!("note: the refutation at depth {d} ({} vB, script {} B): {e}", tx.vsize(), p.leaf.script.len());
        }
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the refutation at depth {d} must mine: {e}"));
        println!("REGTEST PC: refutation at depth {d}: {} vB", tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone())
    }

    /// The depth-`d` refutation carrying the entry's OWN junk signature
    /// instead of the mover's signature over the claimed state — the D41
    /// negative, assembled but NOT broadcast (the caller test_accepts the
    /// rejection).
    fn refute_with_junk(&mut self, g: &mut Game, d: u32) -> Transaction {
        let p = skel(&self.graph, &format!("absent_{d}/refute"));
        let tx = &p.tx;
        let a_prev = &p.prevouts[0];
        let (prev_head, new_head) = (self.venue.head(d - 1), self.venue.head(d));
        let junk_r = WotsSig::from_hashes(WotsParams::for_bytes(42), &chess::auth_message(&new_head), vec![[0x11; 20]; STATE_DIGITS]).unwrap();
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
        let mut w = refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair_sig, &[&junk_r]);
        let mover_sig = sign_tx(g.payment_of(instance::mover_at(d)), tx, a_prev, &p.leaf.script);
        w.push(mover_sig);
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        tx
    }

    /// The claimant's disprove spend over the parked tuple (built at
    /// runtime — the claimant's own money claim): the kind's exhibit
    /// (computed from the parked heads), then the pair reveal copied from
    /// the refutation's published witness. Caller mines or rejects.
    fn disprove(&self, rt: &Regtest, g: &Game, d: u32, p_op: OutPoint, p_prev: &TxOut, kind: Kind) -> Transaction {
        let _ = rt;
        let ctx = g.ctx();
        let p_tree = g.inst.refuted_tree(&ctx, d).unwrap();
        let name = format!("disprove_{}", chess::leaf_name(kind));
        let l = p_tree.leaf(&name).unwrap();
        let claimant = instance::mover_at(d).other();
        let payout = g.keys_of_pub(claimant).payout_spk.clone();
        let mut tx = lngap_btc::tx::build_spend(
            p_op,
            &l.timelock,
            vec![TxOut { value: p_prev.value - g.params.presign_fee, script_pubkey: payout }],
        );
        let dsig = sign_tx(g.payment_of(claimant), &tx, p_prev, &l.script);
        // the exhibit from the parked tuple (at depth 1 the prior is the
        // constant initial board)
        let new_state = ChessState::from_e(self.venue.head(d)[8..48].try_into().unwrap()).unwrap();
        let prior_state = if d >= 2 {
            ChessState::from_e(self.venue.head(d - 1)[8..48].try_into().unwrap()).unwrap()
        } else {
            ChessState::initial()
        };
        let exhibit = find_kind(&prior_state.pos, new_state.mv, &new_state.pos, kind)
            .map(|c| exhibit_values(c))
            .unwrap_or_else(|| vec![0; kind.exhibit_len()]);
        // bottom-first: the exhibit IN ORDER (Kind::exhibit()[0] deepest —
        // sim_chess.rs's note), then the pair reveal, then the claimant's
        // signature
        let mut w: Vec<Vec<u8>> = exhibit.iter().map(|&v| lngap_script32::sim::encode(v)).collect();
        w.extend(refute::wots_wire(self.pair_sig.as_ref().expect("the refutation went first")));
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block(&name).unwrap());
        tx
    }

    /// The claimant's `wrong_slot` disprove off a refuted output (no
    /// exhibit; a ttt-shaped OP_VERIFY leaf): the parked prior head's word0
    /// is not this game's — the empty slot's zero head, say.
    fn disprove_wrong_slot(&self, g: &Game, d: u32, p_op: OutPoint, p_prev: &TxOut) -> Transaction {
        let ctx = g.ctx();
        let p_tree = g.inst.refuted_tree(&ctx, d).unwrap();
        let l = p_tree.leaf("disprove_wrong_slot").unwrap();
        let claimant = instance::mover_at(d).other();
        let mut tx = lngap_btc::tx::build_spend(p_op, &l.timelock, vec![TxOut { value: p_prev.value - g.params.presign_fee, script_pubkey: g.keys_of_pub(claimant).payout_spk.clone() }]);
        let dsig = sign_tx(g.payment_of(claimant), &tx, p_prev, &l.script);
        let mut w = refute::wots_wire(self.pair_sig.as_ref().expect("the refutation went first"));
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block("disprove_wrong_slot").unwrap());
        tx
    }

    /// A timeout-split witness off the claim output (the claimant's code).
    fn timeout_witness(&self, g: &mut Game, d: u32, code: u8) -> Vec<Vec<u8>> {
        self.timeout_witness_under(g, d, code, &format!("absent_{d}"))
    }

    /// As [`Path::timeout_witness`] under the claim-shaped output `base`.
    fn timeout_witness_under(&self, g: &mut Game, d: u32, code: u8, base: &str) -> Vec<Vec<u8>> {
        let p = skel(&self.graph, &format!("{base}/split_{}", self.outcome_name(code)));
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
        self.checked_witness_under(g, d, code, reveal, &format!("absent_{d}"))
    }

    /// As [`Path::checked_witness_with`] under the claim-shaped output
    /// `base` (its refuted output's splits are `{base}/refuted/split_*`).
    fn checked_witness_under(&self, g: &Game, d: u32, code: u8, reveal: &lngap_lamport::Reveal, base: &str) -> Vec<Vec<u8>> {
        let p = skel(&self.graph, &format!("{base}/refuted/split_{}", self.outcome_name(code)));
        let sig_u = sign_tx(&g.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        ttt::checked_split_witness(sig_u, sig_h, reveal, self.pair_sig.as_ref().expect("the refutation went first"))
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
        Role::User => Seed::from_label("posc/user-ks"),
        Role::Hub => Seed::from_label("posc/hub-ks"),
    };
    let sk = lngap_lamport::SecretKey::from_entropy(
        lngap_contract::CODE_BITS,
        seed.derive_bytes(&format!("lamport/{}", instance::code_label(CONTRACT_ID, 1, d))),
    );
    sk.reveal_bits(&lngap_lamport::uint_to_bits(u32::from(code), lngap_contract::CODE_BITS))
        .unwrap()
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
fn wired_pos_chess_graph() {
    let rt = Regtest::start().unwrap();
    let tables = epoch_tables();
    // the deepest path (claim -> counter -> refute -> split, D44) takes
    // four 60k-sat pre-sign fees: the pot must cover them
    let value = Amount::from_sat(400_000);

    // ====== path A: an illegal move (a bishop jumps a pawn) is killed ======
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        assert_eq!(
            path.graph.len(),
            1 + MAX_DEPTH as usize * 8 + MAX_DEPTH as usize + (MAX_DEPTH as usize - 1) * 8,
            "the wired chess graph: settle + {MAX_DEPTH} x (claim, refute, 3 + 3 splits) + {MAX_DEPTH} per-depth equivocation exhibits (D39, D43) + {} x (counter, refute, 3 + 3 splits) (D44); NO exhibit family (D42)",
            MAX_DEPTH - 1
        );
        // slot 1: user's legal e2e4; slot 2: hub's c8e6 — a bishop jumping
        // the d7 pawn
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(1).unwrap();
        path.seal(&mut g, 2, "c8e6", false);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        let (_a_op, _a_prev) = path.claim(&rt, &g, D);
        let (p_op, p_prev) = path.refute(&rt, &mut g, D);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        // the wrong leaf cannot fire (the bishop moved fine as such — the
        // board is honestly derived — so Board does not fire)
        let bad = path.disprove(&rt, &g, D, p_op, &p_prev, Kind::Board);
        match rt.test_accept(&bad) {
            Err(e) => println!("note: chess_board correctly rejected: {e}"),
            Ok(v) => panic!("chess_board must not fire on a honestly-derived board (accepted at {v} vB)"),
        }
        // the mover's split cannot beat the disprove window
        let w = path.checked_witness(&mut g, D, 1);
        let early = dry(skel(&path.graph, "absent_2/refuted/split_HubWins"), w);
        assert!(rt.test_accept(&early).is_err(), "the mover's split must wait out the disprove window");
        // the jumped pawn is disproved: the user takes the pot
        let dtx = path.disprove(&rt, &g, D, p_op, &p_prev, Kind::Ray);
        rt.mine_with(&[dtx.clone()]).unwrap_or_else(|e| panic!("the ray disprove must mine: {e}"));
        println!("REGTEST PC: disprove chess_ray: {} vB", dtx.vsize());
    }

    // ====== path B: a legal refutation stands ======
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(1).unwrap();
        path.seal(&mut g, 2, "e7e5", true);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, D);
        let (p_op, p_prev) = path.refute(&rt, &mut g, D);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        // no disprove fires on the legal tuple
        for kind in chess::kinds() {
            let bad = path.disprove(&rt, &g, D, p_op, &p_prev, kind);
            assert!(rt.test_accept(&bad).is_err(), "{kind:?} must not fire on a legal move");
        }
        // the wrong code is rejected in-leaf
        let w = path.checked_witness_with(&g, D, 0, &adversarial_code_reveal(D, 0));
        let wrong = dry(skel(&path.graph, "absent_2/refuted/split_UserWins"), w);
        assert!(rt.test_accept(&wrong).is_err(), "code != R(parked) must fail in-leaf");
        // the right code pays after delta + delta': R(parked) — white to
        // move forfeits — HubWins
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        let w = path.checked_witness(&mut g, D, 1);
        let split = run(&rt, skel(&path.graph, "absent_2/refuted/split_HubWins"), w);
        println!("REGTEST PC: checked split (legal refutation): {} vB", split.vsize());
    }

    // ====== path C: no publication — the timeout split pays ======
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(1).unwrap();
        path.venue.seal_empty(2);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, D);
        // too early: the timeout split must wait out delta
        let w = path.timeout_witness(&mut g, D, 0);
        let early = dry(skel(&path.graph, "absent_2/split_UserWins"), w.clone());
        assert!(rt.test_accept(&early).is_err(), "the timeout split must wait out delta");
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let split = run(&rt, skel(&path.graph, "absent_2/split_UserWins"), w);
        println!("REGTEST PC: timeout split: {} vB", split.vsize());
    }

    // ====== path D: the depth-1 single-head form ======
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, 1);
        let (p_op, p_prev) = path.refute(&rt, &mut g, 1);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        // hub's disprove cannot fire on the legal opening (the constant
        // prior is the initial board)
        let bad = path.disprove(&rt, &g, 1, p_op, &p_prev, Kind::Destination);
        assert!(rt.test_accept(&bad).is_err(), "no leaf fires on a legal opening");
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        // R(parked): black to move forfeits -> UserWins
        let w = path.checked_witness(&mut g, 1, 0);
        let split = run(&rt, skel(&path.graph, "absent_1/refuted/split_UserWins"), w);
        println!("REGTEST PC: depth-1 checked split: {} vB", split.vsize());
    }

    // ====== path E: fool's mate — the absence path IS the terminal path ======
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        // 1. f3 e5 2. g4 Qh4#
        for (slot, uci) in [(1, "f2f3"), (2, "e7e5"), (3, "g2g4"), (4, "d8h4")] {
            rt.mine(1).unwrap();
            path.seal(&mut g, slot, uci, true);
        }
        assert!(lngap_chess::terminal(&path.state.pos).is_some(), "the fixture must be terminal");
        // E1: the mated user has no move at depth 5; slot 5 seals empty;
        // hub's absence claim pays by timeout with code HubWins
        rt.mine(1).unwrap();
        path.venue.seal_empty(5);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, 5);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let w = path.timeout_witness(&mut g, 5, 1);
        let split = run(&rt, skel(&path.graph, "absent_5/split_HubWins"), w);
        println!("REGTEST PC: the mated side's absence resolves by timeout: {} vB", split.vsize());
    }
    {
        // E2: same game, but the mated user ANSWERS with an illegal g4g5
        // (the king still attacked): the refutation parks it and hub's
        // chess_kingattacked disprove — a TWO-ELEMENT exhibit — takes it
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        for (slot, uci) in [(1, "f2f3"), (2, "e7e5"), (3, "g2g4"), (4, "d8h4")] {
            rt.mine(1).unwrap();
            path.seal(&mut g, slot, uci, true);
        }
        rt.mine(1).unwrap();
        path.seal(&mut g, 5, "g4g5", false);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, 5);
        let (p_op, p_prev) = path.refute(&rt, &mut g, 5);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let dtx = path.disprove(&rt, &g, 5, p_op, &p_prev, Kind::KingAttacked);
        rt.mine_with(&[dtx.clone()]).unwrap_or_else(|e| panic!("the king-attacked disprove must mine: {e}"));
        println!("REGTEST PC: disprove chess_kingattacked: {} vB", dtx.vsize());
    }

    // ====== path F1: the claim one depth AHEAD is countered (D44) ======
    {
        // the hub stalls at slot 2, then claims `absent_3` ("the user did
        // not move at 3" — vacuously true: the user's turn never came).
        // Before D44 this raced the user's honest `absent_2` on CLTV order
        // alone and the staller's timeout split could take the pot.
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(1).unwrap();
        path.venue.seal_empty(2);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, 3); // the staller's vacuous claim
        // the user counters: "you did not move at 2"
        let (c_op, c_prev) = path.counter(&rt, &g, 3);
        // the staller's only defence is a refutation at depth 2 — the
        // venue attested the EMPTY slot's zero head, and the hub can sign
        // its region, so the readout itself passes...
        path.pair_sig = None;
        let (p_op, p_prev) = path.refute_under(&rt, &mut g, 2, "absent_3/counter");
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        // ...and the user's `wrong_slot` kills it (word0 of the zero head
        // is not (game, 2, hub)): the user takes the pot
        let dtx = path.disprove_wrong_slot(&g, 2, p_op, &p_prev);
        rt.mine_with(&[dtx.clone()]).unwrap_or_else(|e| panic!("wrong_slot must fire on the zero head: {e}"));
        println!("REGTEST PC: claim-ahead countered, zero-head refutation disproved by wrong_slot: {} vB", dtx.vsize());
        let _ = (c_op, c_prev);
    }
    {
        // the same attack, the staller declining the hopeless refutation:
        // the user's timeout split off the counter output pays after delta
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(1).unwrap();
        path.venue.seal_empty(2);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, 3);
        path.counter(&rt, &g, 3);
        let before = rt.balance_of(&g.user.public().payout_spk).unwrap();
        let w = path.timeout_witness_under(&mut g, 2, 0, "absent_3/counter");
        let early = dry(skel(&path.graph, "absent_3/counter/split_UserWins"), w.clone());
        assert!(rt.test_accept(&early).is_err(), "the counter's timeout split must wait out delta");
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let split = run(&rt, skel(&path.graph, "absent_3/counter/split_UserWins"), w);
        println!("REGTEST PC: claim-ahead countered, timeout split: {} vB", split.vsize());
        assert_eq!(rt.balance_of(&g.user.public().payout_spk).unwrap() - before, value - g.params.presign_fee - g.params.presign_fee - g.params.presign_fee, "the pot less three hops' fees");
    }

    // ====== path F2: a FALSE counter to a due claim is refuted (D44) ======
    {
        // the hub's e7e5 is on the venue at slot 2; the user stalls at 3;
        // the hub's `absent_3` is due. The user counters anyway ("you did
        // not move at 2" — false): the hub refutes on the counter output
        // with the (1, 2) pair readout, nothing disproves it, and the
        // hub's self-checking split pays R(parked) = HubWins
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(1).unwrap();
        path.seal(&mut g, 2, "e7e5", true);
        rt.mine(1).unwrap();
        path.venue.seal_empty(3);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, 3);
        path.counter(&rt, &g, 3);
        let (p_op, p_prev) = path.refute_under(&rt, &mut g, 2, "absent_3/counter");
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let bad = path.disprove(&rt, &g, 2, p_op, &p_prev, Kind::Ray);
        assert!(rt.test_accept(&bad).is_err(), "no leaf fires on the legal e7e5");
        let bad = path.disprove_wrong_slot(&g, 2, p_op, &p_prev);
        assert!(rt.test_accept(&bad).is_err(), "wrong_slot does not fire on the real heads");
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        let before = rt.balance_of(&g.hub.public().payout_spk).unwrap();
        let reveal = g.keys_of(Role::Hub).0.reveal_uint(&instance::code_label(CONTRACT_ID, 1, 2), 1).unwrap();
        let w = path.checked_witness_under(&g, 2, 1, &reveal, "absent_3/counter");
        let split = run(&rt, skel(&path.graph, "absent_3/counter/refuted/split_HubWins"), w);
        println!("REGTEST PC: false counter refuted; checked split: {} vB", split.vsize());
        assert_eq!(rt.balance_of(&g.hub.public().payout_spk).unwrap() - before, value - g.params.presign_fee - g.params.presign_fee - g.params.presign_fee - g.params.presign_fee, "the pot less four hops' fees");
    }

    // ====== path G: a garbage-signed entry admits no refutation ======
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let mut path = Path::open(&rt, &g, &tables);
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, "e2e4", true);
        rt.mine(1).unwrap();
        // slot 2 seals a legal-looking move with JUNK preimages
        let junk_state = play(&path.state, "e7e5").unwrap();
        path.venue.seal_move_junk(2, &junk_state);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        path.claim(&rt, &g, D);
        let junk_refute = path.refute_with_junk(&mut g, D);
        assert!(rt.test_accept(&junk_refute).is_err(), "a garbage-signed entry must admit no refutation");
        // the absence path resolves instead
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let w = path.timeout_witness(&mut g, D, 0);
        let split = run(&rt, skel(&path.graph, "absent_2/split_UserWins"), w);
        println!("REGTEST PC: garbage-signed entry; timeout split: {} vB", split.vsize());
    }
}
