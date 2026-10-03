//! The wired PoS graph for BLACKJACK on regtest (D57): real signed venue
//! entries carrying share strings in their bodies, the members' registered
//! check, two-head refutations, and the blackjack disprove family with
//! share strings as witness elements.
//!
//! - A: the house deals a WRONG up-card at depth 2: the player claims
//!   absence, the house refutes, and `bj_card_2` (the two strings from the
//!   entry bodies) takes the pot; a card leaf for a correct card fails.
//! - B: an honest hand the PLAYER wins at the showdown (depth 4, a house
//!   move): the player claims absence at 4, the house parks its own losing
//!   terminal state, no disprove fires, and after `delta + delta'` the
//!   player broadcasts the UNGATED checked split paying R = UserWins; the
//!   HubWins split fails in-leaf. (With the chess split's mover-code gate
//!   the house could have locked the pot here.)
//! - C: the player committed an OUT-OF-RANGE share (value 14) at position
//!   0: honest members refuse its DEAL entry (the registered check); a
//!   rogue seals it; the house claims absence at 1, the player refutes
//!   (depth 1: the single-head form), and the house's `bj_share_0` takes
//!   the pot.
//! - D: the dealer DRAWS AT 17 (to beat the player's 19): `bj_dealer`
//!   takes the pot.

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_blackjack as bj;
use lngap_blackjack::{Commitments, Share, State, K as POSITIONS};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PresignedTx, Role};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSig;
use lngap_pos::blackjack;
use lngap_pos::graph::proposer_witness;
use lngap_pos::instance::{self, Game as WhichGame, GameClock, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNKS, HEAD_CHUNK_START};
use lngap_pos::{Authorship, Member, PosMiner, Registry, SealedBlock};
use rand::{rngs::StdRng, SeedableRng};

const SEED: [u8; 32] = [9u8; 32];
const GAME_ID: u16 = 1;
const CONTRACT_ID: u32 = 1;
const MAX_DEPTH: u32 = 5;
const K: usize = 5;

fn members() -> Vec<Member> {
    (0..K as u8).map(|i| Member::new([SEED[0] + i; 32])).collect()
}

fn registry() -> Registry {
    PosMiner::new(SEED, members()).registry(CONTRACT_ID, MAX_DEPTH).unwrap()
}

/// Both sides' shares, with the house's chosen to make `ranks` (card k's
/// rank; unlisted positions random). `bad_a0`: the player's position-0
/// share opens to that value instead (out of range).
struct Deck {
    a: Vec<Share>,
    b: Vec<Share>,
}

impl Deck {
    fn new(ranks: &[(usize, u8)], bad_a0: Option<u8>, seed: u64) -> Deck {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut a: Vec<Share> = (0..POSITIONS).map(|_| Share::random(&mut rng)).collect();
        let b: Vec<Share> = (0..POSITIONS)
            .map(|k| match ranks.iter().find(|(p, _)| *p == k) {
                Some(&(_, r)) => Share::new((r + 13 - a[k].value) % 13, &mut rng),
                None => Share::random(&mut rng),
            })
            .collect();
        if let Some(v) = bad_a0 {
            a[0] = Share::new(v, &mut rng);
        }
        Deck { a, b }
    }
    fn commitments(&self) -> Commitments {
        Commitments { player: std::array::from_fn(|k| self.a[k].commitment()), house: std::array::from_fn(|k| self.b[k].commitment()) }
    }
    fn card(&self, k: usize) -> u8 {
        bj::card(self.a[k].value, self.b[k].value)
    }
    fn of(&self, r: Role, k: usize) -> &Share {
        match r {
            Role::User => &self.a[k],
            Role::Hub => &self.b[k],
        }
    }
}

struct Game {
    user: PartyKeys,
    hub: PartyKeys,
    user_ks: KeyStore,
    hub_ks: KeyStore,
    params: ChannelParams,
    pubs: [lngap_channel::PartyPubKeys; 2],
    inst: PosInstance,
    deck: Deck,
}

impl Game {
    fn open(clock: GameClock, deadline: u32, value: Amount, registry: &Registry, deck: Deck) -> Game {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("posb/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("posb/hub"));
        let mut user_ks = KeyStore::new(Seed::from_label("posb/user-ks"));
        let mut hub_ks = KeyStore::new(Seed::from_label("posb/hub-ks"));
        let offer_u = instance::gen_pos_keys(&mut user_ks, Role::User, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Blackjack).unwrap();
        let offer_h = instance::gen_pos_keys(&mut hub_ks, Role::Hub, CONTRACT_ID, 1, MAX_DEPTH, WhichGame::Blackjack).unwrap();
        let keys = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH).unwrap();
        let inst = PosInstance::new(CONTRACT_ID, value, deadline, GAME_ID, WhichGame::Blackjack, clock, keys, registry.clone())
            .unwrap()
            .with_commitments(deck.commitments())
            .unwrap();
        let params = ChannelParams { presign_fee: Amount::from_sat(60_000), ..ChannelParams::regtest(Amount::from_sat(400_000)) };
        let pubs = [user.public(), hub.public()];
        Game { user, hub, user_ks, hub_ks, params, pubs, inst, deck }
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
    fn payout(&self, r: Role) -> ScriptBuf {
        self.pubs[r.idx()].payout_spk.clone()
    }
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

fn sign_with(secret: &SecretKey, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tx(&Keypair::from_secret_key(SECP256K1, secret), tx, prev, leaf)
}

fn skel<'a>(graph: &'a [PresignedTx], label: &str) -> &'a PresignedTx {
    graph.iter().find(|p| p.label == label).unwrap_or_else(|| panic!("no skeleton {label}"))
}

fn head(s: &State, d: u32) -> [u8; 48] {
    s.head(GAME_ID, d, instance::mover_at(d).idx() as u8)
}

struct Path {
    miner: PosMiner,
    sealed: std::collections::HashMap<u32, SealedBlock>,
    graph: Vec<PresignedTx>,
    pair_sig: Option<WotsSig>,
}

impl Path {
    fn open(rt: &Regtest, g: &Game) -> Path {
        let ctx = g.ctx();
        let tree = g.inst.tree(&ctx).unwrap();
        let (c_op, c_prev) = rt.fund(&tree.script_pubkey(), g.inst.value).unwrap();
        let graph = g.inst.graph(&ctx, c_op, &c_prev).unwrap();
        let auth: Authorship = g.inst.authorship();
        let mut miner = PosMiner::new(SEED, members());
        miner.register(CONTRACT_ID, MAX_DEPTH, auth).unwrap();
        Path { miner, sealed: Default::default(), graph, pair_sig: None }
    }

    /// The signed entry for `s` at depth `d`, carrying the mover's strings
    /// for the positions it reveals.
    fn entry(g: &mut Game, d: u32, s: &State) -> Vec<u8> {
        let h = head(s, d);
        let mover = instance::mover_at(d);
        let sig = g.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &blackjack::auth_message(&h)).unwrap();
        let strings: Vec<Vec<u8>> = bj::revealed(s).map(|k| g.deck.of(mover, k).string.clone()).collect();
        let refs: Vec<&[u8]> = strings.iter().map(|v| v.as_slice()).collect();
        blackjack::entry(&h, &sig, &refs)
    }

    /// Seal depth `d` by its designated member (the registered check runs).
    fn seal(&mut self, g: &mut Game, d: u32, s: &State) {
        let e = Path::entry(g, d, s);
        let sealer = self.miner.default_sealer(CONTRACT_ID, d).unwrap();
        let block = self.miner.seal_entry(CONTRACT_ID, d, sealer, &e).unwrap_or_else(|err| panic!("depth {d}: {err}"));
        self.sealed.insert(d, block);
    }

    fn head(&self, d: u32) -> [u8; 48] {
        self.sealed[&d].header.head()
    }

    fn claim(&self, rt: &Regtest, g: &Game, d: u32) {
        let p = skel(&self.graph, &format!("absent_{d}"));
        let mut tx = p.tx.clone();
        let sig_u = sign_tx(&g.user.payment, &tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &tx, &p.prevouts[0], &p.leaf.script);
        tx.input[0].witness = tapscript_witness(&[sig_h, sig_u], &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the absence claim must mine: {e}"));
        println!("REGTEST BJ: absence claim at depth {d}: {} vB", tx.vsize());
    }

    fn refute(&mut self, rt: &Regtest, g: &mut Game, d: u32) -> (OutPoint, TxOut) {
        let p = skel(&self.graph, &format!("absent_{d}/refute")).clone();
        let tx0 = p.tx.clone();
        let a_prev = p.prevouts[0].clone();
        let new_head = self.head(d);
        let mover = instance::mover_at(d);
        let new_sig = g.ks(mover).sign_wots(&instance::state_label(CONTRACT_ID, 1, d), &blackjack::auth_message(&new_head)).unwrap();
        let new_block = self.sealed[&d].clone();
        let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx0, &a_prev, &p.leaf.script)).collect();
        let mut w = if d >= 2 {
            let prev_head = self.head(d - 1);
            let msg = [prev_head.as_slice(), new_head.as_slice()].concat();
            let pair = g.ks(mover).sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &msg).unwrap();
            self.pair_sig = Some(pair.clone());
            let prev_block = &self.sealed[&(d - 1)];
            // the prior is bound by the claimant's signature, from its entry
            let prev_key = g.ks(mover.other()).wots_public(&instance::state_label(CONTRACT_ID, 1, d - 1)).unwrap();
            let prev_sig = refute::entry_auth_sig(&prev_key, &blackjack::auth_message(&prev_head), &prev_block.entry).expect("the prior entry carries its mover's signature");
            refute::refute_witness_pair_signed(&sigs_new, &pair, [&new_sig, &prev_sig])
        } else {
            let sig = g.ks(mover).sign_wots(&instance::refute_label(CONTRACT_ID, 1, d), &new_head).unwrap();
            self.pair_sig = Some(sig.clone());
            refute::refute_witness(&sigs_new, &sig, &new_sig)
        };
        w.extend(proposer_witness(sign_with(&new_block.proposer_secret, &tx0, &a_prev, &p.leaf.script), new_block.proposer));
        // the refutation is 2-of-2: the hub's signature, then the user's
        w.push(sign_tx(&g.hub.payment, &tx0, &a_prev, &p.leaf.script));
        w.push(sign_tx(&g.user.payment, &tx0, &a_prev, &p.leaf.script));
        let mut tx = tx0;
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the refutation at depth {d} must mine: {e}"));
        println!("REGTEST BJ: refutation at depth {d}: {} vB", tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone())
    }

    /// The claimant's disprove through leaf `name` with witness strings
    /// `wits` (bottom first) below the pair reveal.
    fn disprove(&self, g: &Game, d: u32, p_op: OutPoint, p_prev: &TxOut, name: &str, wits: &[&[u8]]) -> Transaction {
        let p_tree = g.inst.refuted_tree(&g.ctx(), d).unwrap();
        let name = format!("disprove_{name}");
        let l = p_tree.leaf(&name).unwrap();
        let claimant = instance::mover_at(d).other();
        let mut tx = lngap_btc::tx::build_spend(p_op, &l.timelock, vec![TxOut { value: p_prev.value - g.params.presign_fee, script_pubkey: g.payout(claimant) }]);
        let dsig = sign_tx(g.payment(claimant), &tx, p_prev, &l.script);
        let mut w = blackjack::leaf_wits(wits);
        w.extend(refute::wots_wire(self.pair_sig.as_ref().expect("the refutation went first")));
        w.push(dsig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &p_tree.control_block(&name).unwrap());
        tx
    }

    /// The ungated checked split `split_{name}` off the depth-`d` refuted
    /// output: both pre-signatures and the pair reveal (either party).
    fn split(&self, g: &Game, d: u32, name: &str) -> Transaction {
        let p = skel(&self.graph, &format!("absent_{d}/refuted/split_{name}"));
        let sig_u = sign_tx(&g.user.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&g.hub.payment, &p.tx, &p.prevouts[0], &p.leaf.script);
        let w = blackjack::checked_split_witness(sig_u, sig_h, self.pair_sig.as_ref().unwrap());
        let mut tx = p.tx.clone();
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        tx
    }
}

fn clock(rt: &Regtest) -> GameClock {
    GameClock { t0: rt.mtp().unwrap(), ell: 60, margin: 60 }
}

fn deadline(rt: &Regtest) -> u32 {
    rt.mtp().unwrap() + 100_000
}

/// Deal, reveal, stand, the dealer phase: the honest states for depths 1-4.
fn to_showdown(deck: &Deck) -> Vec<State> {
    let s1 = bj::deal(&State::initial());
    let s2 = bj::house_reveal(&s1, |k| deck.card(k)).unwrap();
    let s3 = bj::stand(&s2);
    let s4 = bj::house_reveal(&s3, |k| deck.card(k)).unwrap();
    vec![s1, s2, s3, s4]
}

#[test]
fn wired_pos_blackjack_graph() {
    let rt = Regtest::start().unwrap();
    let registry = registry();
    let value = Amount::from_sat(400_000);
    // the player: ten and nine (19); the dealer: a ten up, a seven in the
    // hole (17, stands); position 3 would be a three
    let ranks = [(0, 9), (1, 8), (2, 9), (15, 6), (3, 2)];

    // ====== A: a wrong up-card ======
    {
        let mut g = Game::open(clock(&rt), deadline(&rt), value, &registry, Deck::new(&ranks, None, 1));
        let mut path = Path::open(&rt, &g);
        let s1 = bj::deal(&State::initial());
        let mut s2 = bj::house_reveal(&s1, |k| g.deck.card(k)).unwrap();
        assert_eq!(s2.cards[2], 9);
        s2.cards[2] = 0; // the house shows itself an ace instead of the ten
        rt.mine(1).unwrap();
        path.seal(&mut g, 1, &s1);
        rt.mine(1).unwrap();
        path.seal(&mut g, 2, &s2); // the venue checks openings, never the cards
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        rt.make_time_final(g.inst.claim_from(2)).unwrap();
        path.claim(&rt, &g, 2);
        let (p_op, p_prev) = path.refute(&rt, &mut g, 2);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let (a0, b0) = (g.deck.a[0].string.clone(), g.deck.b[0].string.clone());
        let bad = path.disprove(&g, 2, p_op, &p_prev, "bj_card_0", &[&a0, &b0]);
        assert!(rt.test_accept(&bad).is_err(), "card 0 is right: bj_card_0 must not fire");
        let (a2, b2) = (g.deck.a[2].string.clone(), g.deck.b[2].string.clone());
        let tx = path.disprove(&g, 2, p_op, &p_prev, "bj_card_2", &[&a2, &b2]);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("bj_card_2 must mine: {e}"));
        println!("REGTEST BJ: disprove bj_card_2: {} vB", tx.vsize());
    }

    // ====== B: the player wins the showdown; the house parks its loss ======
    {
        let mut g = Game::open(clock(&rt), deadline(&rt), value, &registry, Deck::new(&ranks, None, 2));
        let mut path = Path::open(&rt, &g);
        let states = to_showdown(&g.deck);
        assert_eq!((states[3].player_total(), states[3].dealer_total(), states[3].status), (19, 17, bj::status::PLAYER));
        for (i, s) in states.iter().enumerate() {
            rt.mine(1).unwrap();
            path.seal(&mut g, i as u32 + 1, s);
        }
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        rt.make_time_final(g.inst.claim_from(4)).unwrap();
        path.claim(&rt, &g, 4);
        let (p_op, p_prev) = path.refute(&rt, &mut g, 4);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        // nothing fires on the honest dealer phase
        let (a15, b15) = (g.deck.a[15].string.clone(), g.deck.b[15].string.clone());
        for (name, wits) in [("bj_status", vec![]), ("bj_dealer", vec![]), ("bj_card_15", vec![a15.clone(), b15.clone()])] {
            let refs: Vec<&[u8]> = wits.iter().map(|v| v.as_slice()).collect();
            assert!(rt.test_accept(&path.disprove(&g, 4, p_op, &p_prev, name, &refs)).is_err(), "{name} must not fire");
        }
        // too early for the split
        assert!(rt.test_accept(&path.split(&g, 4, "UserWins")).is_err(), "the split waits out delta + delta'");
        rt.mine(u64::from(g.params.delta_prime) + 1).unwrap();
        assert!(rt.test_accept(&path.split(&g, 4, "HubWins")).is_err(), "R(parked) is UserWins: HubWins fails in-leaf");
        let tx = path.split(&g, 4, "UserWins");
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the ungated UserWins split must mine: {e}"));
        println!("REGTEST BJ: ungated checked split (player wins, the house parked it): {} vB", tx.vsize());
    }

    // ====== C: an out-of-range share, refused by honest members ======
    {
        let mut g = Game::open(clock(&rt), deadline(&rt), value, &registry, Deck::new(&ranks, Some(14), 3));
        let mut path = Path::open(&rt, &g);
        let s1 = bj::deal(&State::initial());
        let e = Path::entry(&mut g, 1, &s1);
        let err = path.miner.seal_entry(CONTRACT_ID, 1, 0, &e).unwrap_err();
        assert!(err.contains("refuses"), "an honest member refuses an out-of-range reveal: {err}");
        let block = path.miner.seal_unchecked(CONTRACT_ID, 1, 1, &e).unwrap(); // a rogue
        path.sealed.insert(1, block);
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        rt.make_time_final(g.inst.claim_from(1)).unwrap();
        path.claim(&rt, &g, 1);
        let (p_op, p_prev) = path.refute(&rt, &mut g, 1);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let a0 = g.deck.a[0].string.clone();
        let tx = path.disprove(&g, 1, p_op, &p_prev, "bj_share_0", &[&a0]);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("bj_share_0 must mine: {e}"));
        println!("REGTEST BJ: disprove bj_share_0 (depth 1): {} vB", tx.vsize());
    }

    // ====== D: the dealer draws at 17 ======
    {
        let mut g = Game::open(clock(&rt), deadline(&rt), value, &registry, Deck::new(&ranks, None, 4));
        let mut path = Path::open(&rt, &g);
        let mut states = to_showdown(&g.deck);
        // the house draws position 3 (a three) at 17 to reach 20 and win
        let s4 = &mut states[3];
        s4.cards[3] = g.deck.card(3);
        s4.np = 4;
        s4.status = bj::showdown(s4);
        assert_eq!((s4.dealer_total(), s4.status), (20, bj::status::HOUSE));
        for (i, s) in states.iter().enumerate() {
            rt.mine(1).unwrap();
            path.seal(&mut g, i as u32 + 1, s);
        }
        rt.mine(u64::from(g.params.to_self_delay) + 2).unwrap();
        rt.make_time_final(g.inst.claim_from(4)).unwrap();
        path.claim(&rt, &g, 4);
        let (p_op, p_prev) = path.refute(&rt, &mut g, 4);
        rt.mine(u64::from(g.params.delta) + 1).unwrap();
        let tx = path.disprove(&g, 4, p_op, &p_prev, "bj_dealer", &[]);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("bj_dealer must mine: {e}"));
        println!("REGTEST BJ: disprove bj_dealer: {} vB", tx.vsize());
    }
}
