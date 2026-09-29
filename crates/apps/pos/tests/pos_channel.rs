//! Blackjack hands as contract outputs of a real Poon-Dryja channel
//! (CHANNEL_DEMO_PLAN.md step 1): `PosInstance` is a `ContractOutput`.
//!
//! - Hand 1 is added by a channel update and, after an honest hand,
//!   REMOVED by the next update with the cooperative payout: no chain
//!   transaction at all.
//! - Hand 2 is added; the house deals a wrong up-card; the player
//!   FORCE-CLOSES. The commitment confirms with the contract output on it;
//!   the player's absence claim (with its `to_self_delay`, the claimant
//!   being the broadcaster), the house's refutation and the player's
//!   `bj_card_2` disprove all spend off that commitment version's graph.
//!   The channel's own outputs are swept by the channel's watch loop.

use std::sync::Arc;

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_blackjack as bj;
use lngap_blackjack::{Commitments, Share, State, K as POSITIONS};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::chain::Chain;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::presign::GraphKey;
use lngap_channel::protocol::{funding_tree, run_bus, ChannelParty, Policy};
use lngap_channel::wire::WireEnvelope;
use lngap_channel::{ChannelParams, ChannelState, ContractOutput, PartyKeys, PresignedTx, Role};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSig;
use lngap_pos::blackjack;
use lngap_pos::graph::proposer_witness;
use lngap_pos::instance::{self, Game as WhichGame, GameClock, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNKS, HEAD_CHUNK_START};
use lngap_pos::{Member, PosMiner, SealedBlock};
use rand::{rngs::StdRng, SeedableRng};

const SEED: [u8; 32] = [0x5a; 32];
const GAME_ID: u16 = 1;
const MAX_DEPTH: u32 = 5;
const FUNDING: Amount = Amount::from_sat(3_000_000);
const HALF: Amount = Amount::from_sat(1_500_000);
const STAKE: Amount = Amount::from_sat(500_000);
const DEPOSIT: Amount = Amount::from_sat(250_000);

fn members() -> Vec<Member> {
    (0..5u8).map(|i| Member::new([SEED[0] + i; 32])).collect()
}

fn params() -> ChannelParams {
    ChannelParams { presign_fee: Amount::from_sat(60_000), ..ChannelParams::regtest(FUNDING) }
}

struct Deck {
    a: Vec<Share>,
    b: Vec<Share>,
}

impl Deck {
    fn new(ranks: &[(usize, u8)], seed: u64) -> Deck {
        let mut rng = StdRng::seed_from_u64(seed);
        let a: Vec<Share> = (0..POSITIONS).map(|_| Share::random(&mut rng)).collect();
        let b = (0..POSITIONS)
            .map(|k| match ranks.iter().find(|(p, _)| *p == k) {
                Some(&(_, r)) => Share::new((r + 13 - a[k].value) % 13, &mut rng),
                None => Share::random(&mut rng),
            })
            .collect();
        Deck { a, b }
    }
    fn commitments(&self) -> Commitments {
        Commitments { player: std::array::from_fn(|k| self.a[k].commitment()), house: std::array::from_fn(|k| self.b[k].commitment()) }
    }
    fn card(&self, k: usize) -> u8 {
        bj::card(self.a[k].value, self.b[k].value)
    }
    fn of(&self, r: Role, k: usize) -> &Share {
        if r == Role::User { &self.a[k] } else { &self.b[k] }
    }
}

/// One hand: its instance (contract id `id`), keys and deck.
struct Hand {
    inst: PosInstance,
    deck: Deck,
    sealed: std::collections::HashMap<u32, SealedBlock>,
    pair_sig: Option<WotsSig>,
}

struct World {
    rt: Arc<Regtest>,
    user: ChannelParty,
    hub: ChannelParty,
    ks: [KeyStore; 2],
    miner: PosMiner,
}

impl World {
    fn open() -> World {
        let rt = Arc::new(Regtest::start().unwrap());
        let params = params();
        let user_keys = PartyKeys::from_seed(Role::User, Seed::from_label("posch/user"));
        let hub_keys = PartyKeys::from_seed(Role::Hub, Seed::from_label("posch/hub"));
        let pubs = [user_keys.public(), hub_keys.public()];
        let (u_op, u_prev) = rt.fund(&pubs[0].payout_spk, HALF + Amount::from_sat(10_000)).unwrap();
        let (h_op, h_prev) = rt.fund(&pubs[1].payout_spk, HALF + Amount::from_sat(10_000)).unwrap();
        let ftree = funding_tree(&pubs);
        let mut ftx = build_funding_tx(&[(u_op, u_prev.clone()), (h_op, h_prev.clone())], ftree.script_pubkey(), FUNDING);
        let funding = (OutPoint { txid: ftx.compute_txid(), vout: 0 }, ftx.output[0].clone());
        let initial = ChannelState { seq: 0, balances: [HALF, HALF], contracts: vec![] };
        let accept = || -> Policy { Box::new(|_, _| Ok(())) };
        let user_rev = [user_keys.revocation_hash(0), user_keys.revocation_hash(1)];
        let hub_rev = [hub_keys.revocation_hash(0), hub_keys.revocation_hash(1)];
        let chain: Arc<dyn Chain> = rt.clone();
        let mut user = ChannelParty::new(user_keys, pubs[1].clone(), params, funding.clone(), initial.clone(), hub_rev, chain.clone(), accept()).unwrap();
        let mut hub = ChannelParty::new(hub_keys, pubs[0].clone(), params, funding, initial, user_rev, chain, accept()).unwrap();
        let (m1, m2) = (user.initial_commit_sigs().unwrap(), hub.initial_commit_sigs().unwrap());
        run_bus(&mut user, &mut hub, vec![m1, m2]).unwrap();
        assert!(user.ready_to_fund() && hub.ready_to_fund());
        let prevouts = [u_prev, h_prev];
        sign_funding_input(&mut ftx, 0, &prevouts, &user.keys.payout_tree(), &user.keys.payout).unwrap();
        sign_funding_input(&mut ftx, 1, &prevouts, &hub.keys.payout_tree(), &hub.keys.payout).unwrap();
        rt.send_and_confirm(&ftx).unwrap();
        let ks = [KeyStore::new(Seed::from_label("posch/user-ks")), KeyStore::new(Seed::from_label("posch/hub-ks"))];
        World { rt, user, hub, ks, miner: PosMiner::new(SEED, members()) }
    }

    /// Hand `id`: both sides' per-hand keys, the venue's registry for the
    /// hand, the instance; the venue registers its check.
    fn hand(&mut self, id: u32, deck: Deck) -> Hand {
        let offer_u = instance::gen_pos_keys(&mut self.ks[0], Role::User, id, 1, MAX_DEPTH, WhichGame::Blackjack).unwrap();
        let offer_h = instance::gen_pos_keys(&mut self.ks[1], Role::Hub, id, 1, MAX_DEPTH, WhichGame::Blackjack).unwrap();
        let keys = instance::collect_keys(&offer_u, &offer_h, MAX_DEPTH).unwrap();
        let registry = self.miner.registry(id, MAX_DEPTH).unwrap();
        let t0 = self.rt.mtp().unwrap();
        let clock = GameClock { t0, ell: 60, margin: 60 };
        let inst = PosInstance::new(id, STAKE * 2 + DEPOSIT * 2, t0 + 100_000, GAME_ID, WhichGame::Blackjack, clock, keys, registry)
            .unwrap()
            .with_deposit(DEPOSIT)
            .unwrap()
            .with_commitments(deck.commitments())
            .unwrap();
        self.miner.register(id, MAX_DEPTH, inst.authorship()).unwrap();
        Hand { inst, deck, sealed: Default::default(), pair_sig: None }
    }

    /// A channel update: the user proposes, the hub answers; every message
    /// crosses as JSON (the wire format), its contract ids resolved against
    /// the receiver's own instances.
    fn update(&mut self, balances: [Amount; 2], contracts: Vec<Arc<dyn ContractOutput>>) {
        let seq = self.user.current_seq() + 1;
        let known = contracts.clone();
        let msgs = self.user.propose(ChannelState { seq, balances, contracts }).unwrap();
        let mut queue: std::collections::VecDeque<_> = msgs.into();
        while let Some(env) = queue.pop_front() {
            let json = serde_json::to_string(&WireEnvelope::from_env(&env).unwrap()).unwrap();
            let back: WireEnvelope = serde_json::from_str(&json).unwrap();
            let env = back.into_env(|id| known.iter().find(|c| c.id() == id).cloned()).unwrap();
            let target = if env.to == Role::User { &mut self.user } else { &mut self.hub };
            queue.extend(target.handle(env).unwrap());
        }
        assert_eq!((self.user.current_seq(), self.hub.current_seq()), (seq, seq));
        assert!(self.user.pending_seq().is_none() && self.hub.pending_seq().is_none());
    }

    fn balances(&self) -> [Amount; 2] {
        self.user.current_state().balances
    }

    /// Seal depth `d` of hand `h` with the mover's entry for `s`.
    fn seal(&mut self, h: &mut Hand, d: u32, s: &State) {
        let mover = instance::mover_at(d);
        let head = s.head(GAME_ID, d, mover.idx() as u8);
        let sig = self.ks[mover.idx()].sign_wots(&instance::state_label(h.inst.id, 1, d), &blackjack::auth_message(&head)).unwrap();
        let strings: Vec<Vec<u8>> = bj::revealed(s).map(|k| h.deck.of(mover, k).string.clone()).collect();
        let refs: Vec<&[u8]> = strings.iter().map(|v| v.as_slice()).collect();
        let e = blackjack::entry(&head, &sig, &refs);
        let sealer = self.miner.default_sealer(h.inst.id, d).unwrap();
        h.sealed.insert(d, self.miner.seal_entry(h.inst.id, d, sealer, &e).unwrap());
    }

    /// Mine `n` blocks one at a time, both channel parties watching.
    fn advance(&mut self, n: u32) {
        for _ in 0..n {
            self.rt.mine(1).unwrap();
            let h = self.rt.height().unwrap();
            let txs = self.rt.block_txs(h).unwrap();
            self.user.on_block(h, &txs).unwrap();
            self.hub.on_block(h, &txs).unwrap();
        }
    }
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

fn sign_with(secret: &SecretKey, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tx(&Keypair::from_secret_key(SECP256K1, secret), tx, prev, leaf)
}

#[test]
fn blackjack_hands_in_a_channel() {
    let mut w = World::open();
    let start = w.rt.height().unwrap();
    // the player: ten and nine (19); the dealer: a ten up, a seven in the
    // hole (17): the player wins the showdown
    let ranks = [(0, 9), (1, 8), (2, 9), (15, 6)];

    // ====== hand 1: added, played, folded — no chain transaction ======
    let mut h1 = w.hand(1, Deck::new(&ranks, 1));
    let inst1: Arc<dyn ContractOutput> = Arc::new(h1.inst.clone());
    w.update([HALF - STAKE - DEPOSIT, HALF - STAKE - DEPOSIT], vec![inst1]);
    let s1 = bj::deal(&State::initial());
    let s2 = bj::house_reveal(&s1, |k| h1.deck.card(k)).unwrap();
    let s3 = bj::stand(&s2);
    let s4 = bj::house_reveal(&s3, |k| h1.deck.card(k)).unwrap();
    for (d, s) in [(1, s1), (2, s2), (3, s3), (4, s4)] {
        w.seal(&mut h1, d, &s);
    }
    assert_eq!(s4.status, bj::status::PLAYER);
    let [pu, ph] = h1.inst.cooperative_payout(lngap_contract::Payout::UserAll);
    let b = w.balances();
    w.update([b[0] + pu, b[1] + ph], vec![]);
    assert_eq!(w.balances(), [HALF + STAKE, HALF - STAKE], "the player won the other stake; both deposits returned");
    assert_eq!(w.rt.height().unwrap(), start, "hand 1 settled with no chain transaction");
    println!("CHANNEL: hand 1 folded in the channel: balances {:?}", w.balances());

    // ====== hand 2: a wrong up-card, the player force-closes ======
    let mut h2 = w.hand(2, Deck::new(&ranks, 2));
    let inst2: Arc<dyn ContractOutput> = Arc::new(h2.inst.clone());
    let b = w.balances();
    w.update([b[0] - STAKE - DEPOSIT, b[1] - STAKE - DEPOSIT], vec![inst2]);
    let seq = w.user.current_seq();
    let s1 = bj::deal(&State::initial());
    let mut s2 = bj::house_reveal(&s1, |k| h2.deck.card(k)).unwrap();
    s2.cards[2] = 0; // the house shows itself an ace instead of the ten
    w.seal(&mut h2, 1, &s1);
    w.seal(&mut h2, 2, &s2);

    // the player force-closes: its commitment for the current state
    let ctxid = w.user.force_close().unwrap();
    w.advance(1);
    let commit = w.user.my_commitment(seq).unwrap().clone();
    assert_eq!(commit.txid(), ctxid);
    let o = commit.output(lngap_channel::commit::OutputKind::Contract(2)).expect("the hand's contract output");
    let (c_op, c_prev) = (commit.outpoint(o), commit.txout(o));
    println!("CHANNEL: commitment {seq} confirmed ({} vB); the hand's contract output {c_op} carries {}", commit.tx.vsize(), c_prev.value);
    // that version's graph (the user's), fully signed by both
    let graph: Vec<PresignedTx> = w.user.record(seq).unwrap().graph.iter().filter(|(k, _)| k.version == Role::User && k.contract_id == 2).map(|(_, p)| p.clone()).collect();
    let skel = |label: &str| graph.iter().find(|p| p.label == label).unwrap_or_else(|| panic!("no {label}")).clone();
    // the claim: the claimant broadcast the commitment, so its claim waits
    // out to_self_delay; and the move's due time plus the margin (MTP)
    w.advance(u32::from(w.user.params.to_self_delay));
    w.rt.make_time_final(h2.inst.claim_from(2)).unwrap();
    let p = skel("absent_2");
    assert_eq!(p.tx.input[0].previous_output, c_op, "the claim spends the contract output on this commitment");
    let mut claim = p.tx.clone();
    let (su, sh) = (p.sigs[0].unwrap(), p.sigs[1].unwrap());
    claim.input[0].witness = tapscript_witness(&[sh.as_ref().to_vec(), su.as_ref().to_vec()], &p.leaf.script, &p.control_block);
    w.rt.mine_with(&[claim.clone()]).unwrap_or_else(|e| panic!("the claim must mine: {e}"));
    println!("CHANNEL: absence claim off the commitment: {} vB", claim.vsize());

    // the house refutes (it still has its seal)
    let p = skel("absent_2/refute");
    let a_prev = p.prevouts[0].clone();
    let (prev_head, new_head) = (h2.sealed[&1].header.head(), h2.sealed[&2].header.head());
    let pair = w.ks[1].sign_wots(&instance::refute_label(2, 1, 2), &[prev_head.as_slice(), new_head.as_slice()].concat()).unwrap();
    let auth = w.ks[1].sign_wots(&instance::state_label(2, 1, 2), &blackjack::auth_message(&new_head)).unwrap();
    let chunk_sigs = |b: &SealedBlock| -> Vec<Vec<u8>> { (0..HEAD_CHUNKS).map(|j| sign_with(&b.attestation.secrets[HEAD_CHUNK_START + j], &p.tx, &a_prev, &p.leaf.script)).collect() };
    let mut wit = refute::refute_witness_pair(&chunk_sigs(&h2.sealed[&1]), &chunk_sigs(&h2.sealed[&2]), &pair, &[&auth]);
    let blk = &h2.sealed[&2];
    wit.extend(proposer_witness(sign_with(&blk.proposer_secret, &p.tx, &a_prev, &p.leaf.script), blk.proposer));
    wit.push(sign_tx(&w.hub.keys.payment, &p.tx, &a_prev, &p.leaf.script));
    let mut rtx = p.tx.clone();
    rtx.input[0].witness = tapscript_witness(&wit, &p.leaf.script, &p.control_block);
    w.rt.mine_with(&[rtx.clone()]).unwrap_or_else(|e| panic!("the refutation must mine: {e}"));
    h2.pair_sig = Some(pair);
    let r_op = OutPoint { txid: rtx.compute_txid(), vout: 0 };
    let r_prev = rtx.output[0].clone();
    println!("CHANNEL: refutation off the commitment: {} vB", rtx.vsize());

    // the player's disprove, built at run time against this version's refuted tree
    w.advance(u32::from(w.user.params.delta) + 1);
    let tree = h2.inst.refuted_tree(&w.user.commit_ctx(seq, Role::User).unwrap(), 2).unwrap();
    let l = tree.leaf("disprove_bj_card_2").unwrap();
    let mut dtx = lngap_btc::tx::build_spend(r_op, &l.timelock, vec![TxOut { value: r_prev.value - w.user.params.presign_fee, script_pubkey: w.user.my_payout_spk() }]);
    let dsig = sign_tx(&w.user.keys.payment, &dtx, &r_prev, &l.script);
    let mut dw = blackjack::leaf_wits(&[&h2.deck.a[2].string, &h2.deck.b[2].string]);
    dw.extend(refute::wots_wire(h2.pair_sig.as_ref().unwrap()));
    dw.push(dsig);
    dtx.input[0].witness = tapscript_witness(&dw, &l.script, &tree.control_block("disprove_bj_card_2").unwrap());
    w.rt.mine_with(&[dtx.clone()]).unwrap_or_else(|e| panic!("the disprove must mine: {e}"));
    println!("CHANNEL: disprove bj_card_2 off the commitment: {} vB, paying the player {}", dtx.vsize(), dtx.output[0].value);
    // the channel's own outputs: the hub's to_remote is swept at once, the
    // user's to_local after its delay (the watch loop)
    w.advance(3);
    let _ = GraphKey { version: Role::User, contract_id: 2, label: String::new() };
}
