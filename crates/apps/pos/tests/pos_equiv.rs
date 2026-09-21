//! Step 6 of POS_FACTCHAIN_PLAN.md (D39): the player-equivocation leaf on
//! regtest. The venue entry's signature is the mover's reveal of the state
//! under the per-depth Lamport state key; a mover who plays TWICE at one
//! depth (a reorg-aided double-play — GAME_PROTOCOL.md section 5 item 4,
//! the standing gap this step closes) exposes both preimages of every state
//! bit the two states differ in, and the `equiv_{d}_{i}` leaf on the
//! contract output pays the exhibitor the pot.
//!
//! Paths mined (the node enforcing real timelocks):
//!
//! - U: the USER double-plays depth 1 — the venue seals X@4 signed for
//!   real, a fork block at slot 1 carries a hand-reproduced conflicting
//!   reveal (the honest keystore refuses to equivocate, asserted), the
//!   client names the event `Observation::Equivocation`, and the hub
//!   exhibits a differing bit: `equiv_1_{i}` takes the pot to the hub
//!   (the no-csv branch: the exhibitor is not the broadcaster);
//! - H: the HUB double-plays depth 2 — symmetric, and the csv branch (the
//!   exhibitor IS the broadcaster): the spend is rejected before
//!   `to_self_delay` and mines after.
//!
//! Negatives: the same preimage twice is not evidence, a wrong value is not
//! a preimage, the right preimages under the WRONG (depth, bit) leaf fail,
//! and the honest keystore's refusal is asserted in both directions.

use bitcoin::key::Keypair;
use bitcoin::{Amount, Transaction};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PresignedTx, Role};
use lngap_contract::Contract;
use lngap_ec_wots::{Attester, EpochTable};
use lngap_factchain::slot::{SlotEntry, STATE_BITS};
use lngap_factchain::{entry_head, entry_root, Header};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::Reveal;
use lngap_pos::instance::{self, PosInstance};
use lngap_pos::{PosClient, PosMiner, SealedBlock, HEADER_CHUNKS};
use lngap_tictactoe::{Board, TicTacToe};

/// The venue's attester seed (the single key standing in for the FROST
/// group key, per the ec-wots design).
const SEED: [u8; 32] = [0x66; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
const MAX_DEPTH: u32 = 9;

fn state_bits(b: &Board) -> Vec<bool> {
    let v = TicTacToe.state_bits(b);
    assert_eq!(v.len(), STATE_BITS, "the state key covers exactly the state bits");
    v
}

/// The venue's epoch tables, published at contract open.
fn epoch_tables() -> Vec<EpochTable> {
    let attester = Attester::new(SEED);
    (0..=MAX_DEPTH as u64).map(|s| attester.epoch_table(s, HEADER_CHUNKS)).collect()
}

/// The venue, sealing entries with REAL state signatures (unlike the
/// 4b/4c fixture's dummies — the signature IS the evidence here).
struct Venue {
    miner: PosMiner,
    sealed: std::collections::HashMap<u32, SealedBlock>,
}

impl Venue {
    fn new() -> (Venue, lngap_n4bit::Digest) {
        let attester = Attester::new(SEED);
        let (gen, _t0) = lngap_pos::genesis(&attester);
        let g = gen.header.digest();
        (Venue { miner: PosMiner::new(SEED, g, 0), sealed: Default::default() }, g)
    }
    /// Seal `slot` carrying `mv` from `board`, signed with the mover's real
    /// state-key reveal from `ks`. Returns the new board and the reveal.
    fn seal_move_signed(&mut self, slot: u32, board: &Board, mv: u8, ks: &mut KeyStore) -> (Board, Reveal) {
        let mover = instance::mover_at(slot);
        let new = TicTacToe.transition(board, &mv, mover).unwrap();
        let reveal = ks.reveal_bits(&instance::state_label(CONTRACT_ID, 1, slot), &state_bits(&new)).unwrap();
        let entry = SlotEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            mv,
            state: lngap_lamport::bits_to_uint(&state_bits(&new)),
            sigs: reveal.preimages.clone(),
        };
        self.miner.submit(entry.encode());
        let (block, table) = self.miner.seal_next(slot).unwrap();
        assert!(block.verify_seal(&table).is_ok());
        self.sealed.insert(slot, block);
        (new, reveal)
    }
    /// The equivocation: a SECOND sealed block at `slot`, same parent,
    /// carrying a conflicting move whose signature was reproduced by hand
    /// (the honest keystore refuses to produce it). Returns the block.
    fn fork_move(&self, slot: u32, parent: &lngap_n4bit::Digest, board: &Board, mv: u8, reveal: &Reveal, tables: &[EpochTable]) -> SealedBlock {
        let mover = instance::mover_at(slot);
        let new = TicTacToe.transition(board, &mv, mover).unwrap();
        let entry = SlotEntry {
            game_id: GAME_ID,
            depth: slot as u8,
            mover: mover.idx() as u8,
            mv,
            state: lngap_lamport::bits_to_uint(&state_bits(&new)),
            sigs: reveal.preimages.clone(),
        }
        .encode();
        let header = Header::new(parent, &entry_root(&entry), &entry_head(&entry), slot);
        let attestation = self.miner.attester().attest(&tables[slot as usize], header.as_bytes());
        SealedBlock { header, entry, attestation }
    }
}

/// A conflicting reveal of the mover's depth-`d` state key, reproduced by
/// hand from the keystore's derivation because the honest keystore refuses
/// to equivocate (asserted at each use site).
fn adversarial_state_reveal(ks_seed_label: &str, d: u32, bits: &[bool]) -> Reveal {
    let seed = Seed::from_label(ks_seed_label);
    let sk = lngap_lamport::SecretKey::from_entropy(STATE_BITS, seed.derive_bytes(&format!("lamport/{}", instance::state_label(CONTRACT_ID, 1, d))));
    sk.reveal_bits(bits).unwrap()
}

/// The two parties, their keystores, and the agreed instance (pos_graph.rs's
/// draft, state keys included since this step).
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
    fn open(btc_open: u32, deadline: u32, value: Amount, tables: &[EpochTable]) -> Game {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("pos6/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("pos6/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("pos6/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("pos6/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH, instance::Game::Ttt).unwrap();
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH, instance::Game::Ttt).unwrap();
        let keys_u = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH).unwrap();
        let keys_h = instance::collect_keys(&offer_h, &offer_u, MAX_DEPTH).unwrap();
        assert_eq!(keys_u, keys_h, "the merged key sets must agree");
        let inst_u = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, instance::Game::Ttt, btc_open, 1, keys_u).unwrap();
        let inst_h = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, instance::Game::Ttt, btc_open, 1, keys_h).unwrap();
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
        let pubs = [user.public(), hub.public()];
        let g = Game { user, hub, user_ks, hub_ks, params, pubs, inst: inst_u };
        let ctx = g.ctx();
        assert_eq!(
            g.inst.tree(&ctx, tables).unwrap().script_pubkey(),
            inst_h.tree(&ctx, tables).unwrap().script_pubkey(),
            "both parties must build the same contract output"
        );
        g
    }
    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] }
    }
    fn payout_spk_of(&self, r: Role) -> bitcoin::ScriptBuf {
        match r {
            Role::User => self.user.public().payout_spk,
            Role::Hub => self.hub.public().payout_spk,
        }
    }
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &bitcoin::TxOut, leaf: &bitcoin::ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

fn skel<'a>(graph: &'a [PresignedTx], label: &str) -> &'a PresignedTx {
    graph.iter().find(|p| p.label == label).unwrap_or_else(|| panic!("no skeleton {label}"))
}

/// The equivocation exhibit's witness for the pre-signed skeleton: the two
/// preimages (bit-1's above bit-0's), then both parties' signatures — the
/// leaf checks the 2-of-2 first, so `sig_user` rides on top (consumed
/// first), exactly the claim leaf's convention.
fn exhibit_witness(g: &Game, p: &PresignedTx, p0: [u8; 20], p1: [u8; 20]) -> Vec<Vec<u8>> {
    let sig_u = sign_tx(&g.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
    let sig_h = sign_tx(&g.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
    vec![p0.to_vec(), p1.to_vec(), sig_h, sig_u]
}

/// The (p0, p1) exhibit of a differing state bit from the two entries'
/// reveals; asserts the preimages really open the depth key's bit.
fn differing_bit(inst: &PosInstance, d: u32, board_a: &Board, reveal_a: &Reveal, board_b: &Board, reveal_b: &Reveal) -> (usize, [u8; 20], [u8; 20]) {
    let bits_a = state_bits(board_a);
    let bits_b = state_bits(board_b);
    let i = (0..STATE_BITS).find(|&i| bits_a[i] != bits_b[i]).expect("conflicting states differ at some bit");
    let (pa, pb) = (reveal_a.preimages[i], reveal_b.preimages[i]);
    let (p0, p1) = if bits_a[i] { (pb, pa) } else { (pa, pb) };
    let c = &inst.depth_keys(d).state.bits[i];
    assert_eq!(lngap_btc::hash160(&p0), c.h0, "p0 must open the bit's h0");
    assert_eq!(lngap_btc::hash160(&p1), c.h1, "p1 must open the bit's h1");
    (i, p0, p1)
}

#[test]
fn player_equivocation_leaf() {
    let rt = Regtest::start().unwrap();
    let tables = epoch_tables();
    let value = Amount::from_sat(200_000);

    // ============ path U: the user double-plays depth 1 (no csv) ============
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let ctx = g.ctx();
        let tree = g.inst.tree(&ctx, &tables).unwrap();
        let (c_op, c_prev) = rt.fund(&tree.script_pubkey(), g.inst.value).unwrap();
        let graph = g.inst.graph(&ctx, c_op, &c_prev, &tables).unwrap();
        assert_eq!(
            graph.len(),
            282,
            "settle + 9 x (claim, refute, 3 + 3 splits) + 5 x (exhibit, 3 splits) + 9 x 21 equivocation exhibits"
        );
        let (venue, gen_digest) = Venue::new();
        let mut venue = venue;
        let mut client = PosClient::from_checkpoint(0, gen_digest);
        // the honest depth-1 move, signed for real: X@4
        rt.mine(1).unwrap();
        let (board_a, reveal_a) = venue.seal_move_signed(1, &Board::empty(), 4, &mut g.user_ks);
        client.verify_and_append(&venue.sealed[&1], &tables[1]).unwrap();
        // the double-play: X@0 from the empty board. The honest keystore
        // refuses; the conflicting reveal is reproduced by hand.
        let board_b = TicTacToe.transition(&Board::empty(), &0, Role::User).unwrap();
        assert!(
            g.user_ks.reveal_bits(&instance::state_label(CONTRACT_ID, 1, 1), &state_bits(&board_b)).is_err(),
            "the honest keystore refuses to equivocate"
        );
        let reveal_b = adversarial_state_reveal("pos6/user-ks", 1, &state_bits(&board_b));
        let fork = venue.fork_move(1, &gen_digest, &Board::empty(), 0, &reveal_b, &tables);
        assert!(
            matches!(client.observe(&fork, &tables[1]), Ok(lngap_pos::Observation::Equivocation(_))),
            "the second sealed block at slot 1 is the equivocation"
        );
        let (i, p0, p1) = differing_bit(&g.inst, 1, &board_a, &reveal_a, &board_b, &reveal_b);
        let p = skel(&graph, &format!("equiv_1_{i}"));
        // the payout is pinned to the VICTIM (the hub) at setup
        assert_eq!(p.tx.output[0].script_pubkey, g.payout_spk_of(Role::Hub), "the exhibit pays the non-mover");
        // negatives, dry (never broadcast; one spend of C comes last):
        // the same preimage twice is not evidence
        let bad = {
            let mut t = p.tx.clone();
            let w = exhibit_witness(&g, p, p0, p0);
            t.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
            t
        };
        assert!(rt.test_accept(&bad).is_err(), "the same preimage twice must not pay");
        // a wrong value is not a preimage
        let bad = {
            let mut t = p.tx.clone();
            let w = exhibit_witness(&g, p, [0x42; 20], p1);
            t.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
            t
        };
        assert!(rt.test_accept(&bad).is_err(), "a wrong value must not pay");
        // the right preimages under the WRONG bit's leaf (depth 1, bit != i)
        let k = (i + 1) % STATE_BITS;
        let pk = skel(&graph, &format!("equiv_1_{k}"));
        let bad = {
            let mut t = pk.tx.clone();
            let w = exhibit_witness(&g, pk, p0, p1);
            t.input[0].witness = tapscript_witness(&w, &pk.leaf.script, &pk.control_block);
            t
        };
        assert!(rt.test_accept(&bad).is_err(), "the exhibit is pinned to its (depth, bit) leaf");
        // the real exhibit: the hub takes the pot
        let mut t = p.tx.clone();
        let w = exhibit_witness(&g, p, p0, p1);
        t.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        rt.mine_with(&[t.clone()]).unwrap_or_else(|e| panic!("the equivocation exhibit must mine: {e}"));
        println!("REGTEST 6: player-equivocation exhibit (user double-played depth 1, bit {i}): {} vB", t.vsize());
    }

    // ============ path H: the hub double-plays depth 2 (csv branch) =========
    {
        let mut g = Game::open(rt.height().unwrap() + 1, rt.height().unwrap() + 400, value, &tables);
        let ctx = g.ctx();
        let tree = g.inst.tree(&ctx, &tables).unwrap();
        let (c_op, c_prev) = rt.fund(&tree.script_pubkey(), g.inst.value).unwrap();
        let graph = g.inst.graph(&ctx, c_op, &c_prev, &tables).unwrap();
        let (venue, gen_digest) = Venue::new();
        let mut venue = venue;
        let mut client = PosClient::from_checkpoint(0, gen_digest);
        // slot 1: the user's honest X@4; slot 2: the hub's honest O@0
        rt.mine(1).unwrap();
        let (board1, _) = venue.seal_move_signed(1, &Board::empty(), 4, &mut g.user_ks);
        client.verify_and_append(&venue.sealed[&1], &tables[1]).unwrap();
        rt.mine(1).unwrap();
        let (board_a, reveal_a) = venue.seal_move_signed(2, &board1, 0, &mut g.hub_ks);
        client.verify_and_append(&venue.sealed[&2], &tables[2]).unwrap();
        // the hub's double-play: O@1 from the post-slot-1 board
        let board_b = TicTacToe.transition(&board1, &1, Role::Hub).unwrap();
        assert!(
            g.hub_ks.reveal_bits(&instance::state_label(CONTRACT_ID, 1, 2), &state_bits(&board_b)).is_err(),
            "the honest keystore refuses to equivocate"
        );
        let reveal_b = adversarial_state_reveal("pos6/hub-ks", 2, &state_bits(&board_b));
        let parent = venue.sealed[&1].header.digest();
        let fork = venue.fork_move(2, &parent, &board1, 1, &reveal_b, &tables);
        assert!(
            matches!(client.observe(&fork, &tables[2]), Ok(lngap_pos::Observation::Equivocation(_))),
            "the second sealed block at slot 2 is the equivocation"
        );
        let (j, p0, p1) = differing_bit(&g.inst, 2, &board_a, &reveal_a, &board_b, &reveal_b);
        let p = skel(&graph, &format!("equiv_2_{j}"));
        assert_eq!(p.tx.output[0].script_pubkey, g.payout_spk_of(Role::User), "the exhibit pays the non-mover");
        // the csv branch: the exhibitor IS the broadcaster, so the spend
        // waits out to_self_delay
        let early = {
            let mut t = p.tx.clone();
            let w = exhibit_witness(&g, p, p0, p1);
            t.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
            t
        };
        assert!(rt.test_accept(&early).is_err(), "the broadcaster's exhibit must wait out to_self_delay");
        rt.mine(u64::from(g.params.to_self_delay) + 1).unwrap();
        let mut t = p.tx.clone();
        let w = exhibit_witness(&g, p, p0, p1);
        t.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        rt.mine_with(&[t.clone()]).unwrap_or_else(|e| panic!("the equivocation exhibit must mine after the delay: {e}"));
        println!("REGTEST 6: player-equivocation exhibit (hub double-played depth 2, bit {j}): {} vB", t.vsize());
    }
}
