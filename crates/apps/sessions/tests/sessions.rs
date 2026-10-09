//! V25_POC_PLAN.md Phase 6 on regtest: sessions over a toy L2, a venue of
//! two members dating moves, the withdrawal statement mocked by a BitVMX
//! program (`guest/`), the dispute through lngap-v25's graph.
//!
//! - F, the cooperative withdrawal: activation by a hashlocked transfer,
//!   a return of b on the L2, the hub's check, the fold: nothing on chain;
//! - R, the hub refuses a valid claim: the search is played (the hub
//!   challenging); the hub forces the final step on chain (an absence
//!   claim at the last depth); Alice's dated record parks it; her
//!   pre-signed proof pays the binary-decomposed b: she spends a set bit,
//!   the hub a clear one, both with her signature on b;
//! - X, Alice claims a return that isn't on the L2: her execution halts
//!   with exit 1; the hub forces the final step and its `zk_halt_exit`
//!   disprove takes the pot;
//! - S, the hub stalls: it never answers Alice's claim at depth 2; her
//!   absence claim stands and its timeout split pays b;
//! - H8, H1: the SESSION contract carries only `default` and Alice's start
//!   (no absence claim before a withdrawal: a force-close gives the hub
//!   nothing to spend); with the hub gone, Alice starts unilaterally
//!   (`escalate`: her first move into the ladder) and its split pays b
//!   after w;
//! - E1, escalation mid-game: in a game contract, after five moves played
//!   off-chain, the hub escalates: it posts Alice's move 1 and REPLAYS
//!   moves 2 to 5 from the signatures it holds (one pre-signed ladder per
//!   contract, at the price of the whole history on chain); then it stops,
//!   and Alice's ladder split pays b;
//! - A6: had Alice signed two values of b, the hub takes a bit output of
//!   hers with `equiv_b` before her delay runs out;
//! - settle: a game in which the hub never forces the last step settles
//!   after its end, paying b;
//! - D, the default: no withdrawal by T_close; the hub takes the session
//!   contract.
//!
//! Disputes run in GAME contracts (deadlines counted from the start,
//! `settle`, no default); the session contract precedes any withdrawal.
//!
//! Run with `--test-threads=1` or 2.

use std::collections::HashMap;
use std::sync::Arc;

use bitcoin::hashes::Hash;
use bitcoin::key::Keypair;
use bitcoin::secp256k1::SECP256K1;
use bitcoin::{absolute, Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxOut};
use emulator::decision::challenge::ForceCondition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::{build_spend, build_tx};
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, Role};
use lngap_contract::{Contract, Outcome};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsPublic, WotsSecret, WotsSig};
use lngap_pos::blackjack::auth_message;
use lngap_pos::instance::{self, mover_at, PosDepthKeys};
use lngap_pos::rebut::{wots_wire, wots_wire_tied};
use lngap_pos::ttt::Layout;
use lngap_seal::dating::{Choice, PeriodTree, PAD_LEAF};
use lngap_seal::{ceremony, first_tree, Member, PresignedChain, SealSpec};
use lngap_sessions::l2::{Op, HUB, L2};
use lngap_sessions::session::{bit_tree, default_leaf, payout, settle_leaf, Terms};
use lngap_sessions::statement::{input, write_program};
use lngap_tictactoe::TicTacToe;
use lngap_v25::{carrier_tree, claim_tree, ladder_tree, level_message, rebuttal_tree, escalate_leaf, WindowMember, ZkDated, CARRIER_SAT, LEVEL_BYTES};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::{search, Behaviour};
use lngap_zk::family::ZkFamily;
use lngap_zk::final_d60::{input_key_params, input_message};
use lngap_zk::game::{final_witness, play, Entry, Search};
use lngap_zk::nibble_witness;

const GAME_ID: u16 = 1;
const SEQ: u64 = 1;
const LEVELS: usize = 2;
/// Blocks between a game's last deadline and `settle`.
const SETTLE_GAP: u32 = 30;

// ---------------------------------------------------------------- venue

struct VenueMember {
    member: Member,
    chain: PresignedChain,
}

fn venue(rt: &Regtest, base: u32) -> Vec<VenueMember> {
    (0..2u8)
        .map(|i| {
            let spec = SealSpec {
                value: Amount::from_sat(300_000),
                start: base + u32::from(i),
                period: 4,
                periods: 3,
                grace: 2,
                release_delay: 5,
                fanout_depth: LEVELS as u32,
                leaf_value: Amount::from_sat(330),
                split_fee: Amount::from_sat(400),
                anchor_value: Amount::from_sat(240),
                closing_fee: Amount::from_sat(3_000),
            };
            let member = Member::new([0x90 + i; 32], &spec);
            let seed = [0xD0 + i; 32];
            let tree = first_tree(&spec, &member.public(), &seed).unwrap();
            let (op, _) = rt.fund(&tree.script_pubkey(), spec.value).unwrap();
            let chain = ceremony(&spec, &member.public(), op, &seed).unwrap();
            VenueMember { member, chain }
        })
        .collect()
}

fn window_member(m: usize, v: &VenueMember, s: u32) -> WindowMember {
    let p = &v.chain.member;
    WindowMember { member: m, period: 1, slot: s, root_key: p.roots[0].clone(), empty_hash: p.empties[0], leaf: v.chain.leaf_connector(1, s).unwrap() }
}

fn path_of(tree: &PeriodTree, s: u32) -> (Vec<[u8; 20]>, Vec<[u8; 20]>) {
    let p = tree.path(s as usize).unwrap();
    (p.digests(tree.leaves()[s as usize]), p.siblings.clone())
}

fn sig(kp: &Keypair, tx: &Transaction, input: usize, prevouts: &[TxOut], leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, input, prevouts, leaf).unwrap().as_ref().to_vec()
}

// -------------------------------------------------------------- session

/// One session contract between Alice (the user, the prover) and the hub.
struct Session {
    terms: Terms,
    user: PartyKeys,
    hub: PartyKeys,
    ks: [KeyStore; 2],
    params: ChannelParams,
    pubs: [PartyPubKeys; 2],
    keys: Vec<PosDepthKeys>,
    family: Arc<ZkFamily>,
    /// Alice's input-word keys: word 0 signs `b`, word 1 `c`.
    input_secrets: Vec<WotsSecret>,
    outcomes: Vec<Outcome>,
    level_keys: HashMap<u32, Vec<WotsPublic>>,
    pdf: String,
    heads: Vec<[u8; 48]>,
    entries: Vec<Entry>,
}

/// The contract output: its tree, outpoint, output.
struct Funded {
    tree: TapTree,
    op: OutPoint,
    out: TxOut,
}

/// A claim at depth `d`: the pre-signed transaction, `A_d`, the carriers.
struct Claim {
    d: u32,
    a_tree: TapTree,
    tx: Transaction,
    a_out: TxOut,
    window: Vec<WindowMember>,
    carriers: Vec<(OutPoint, TxOut, TapTree)>,
}

impl Session {
    fn new(terms: Terms, pdf: &str, rounds: u32) -> Session {
        let id = terms.id;
        let user = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("sess/{id}/alice")));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("sess/{id}/hub")));
        let mut ks = [KeyStore::new(Seed::from_label(&format!("sess/{id}/alice-ks"))), KeyStore::new(Seed::from_label(&format!("sess/{id}/hub-ks")))];
        let search = Search { game_id: GAME_ID, rounds };
        let m = search.depths();
        let ou = instance::gen_pos_keys(&mut ks[0], Role::User, id, SEQ, m, instance::Game::Zk).unwrap();
        let oh = instance::gen_pos_keys(&mut ks[1], Role::Hub, id, SEQ, m, instance::Game::Zk).unwrap();
        let keys = instance::collect_keys(&ou, &oh, m).unwrap();
        let info = ProgramInfo::load(pdf).unwrap();
        assert_eq!(info.input_words, 2, "the statement's input is (b, c)");
        let input_secrets: Vec<WotsSecret> = (0..2u8).map(|j| WotsSecret::from_entropy(input_key_params(), [0x60 + j + id as u8; 32])).collect();
        let family = ZkFamily::new(search, info, input_secrets.iter().map(|k| k.public()).collect());
        let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::from_sat(20_000_000)) };
        let pubs = [user.public(), hub.public()];
        Session { terms, user, hub, ks, params, pubs, keys, family, input_secrets, outcomes: Contract::outcomes(&TicTacToe), level_keys: HashMap::new(), pdf: pdf.to_string(), heads: vec![], entries: vec![] }
    }
    fn m(&self) -> u32 {
        self.keys.len() as u32
    }
    fn g(&self) -> ZkDated<'_> {
        ZkDated { family: self.family.as_ref(), prove_presigned: true }
    }
    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::Hub, seq: SEQ, rev_hash: [0u8; 20] }
    }
    fn k(&self, d: u32) -> &PosDepthKeys {
        &self.keys[(d - 1) as usize]
    }
    fn b_key(&self) -> WotsPublic {
        self.input_secrets[0].public()
    }
    /// Alice's signature on her claimed `b` (her depth-1 input word 0).
    fn b_sig(&self, b: u32) -> WotsSig {
        self.input_secrets[0].sign(&input_message(b)).unwrap()
    }
    /// Play the search on Alice's claim `(b, c)`: BitVMX's parties, the hub
    /// challenging; the game's entries.
    fn play(&mut self, b: u32) {
        let dir = std::env::temp_dir().join(format!("lngap-sess-{}-{}", std::process::id(), self.terms.id));
        let _ = std::fs::remove_dir_all(&dir);
        let s = search(&self.pdf, &input(b, self.terms.id), &dir, &Behaviour::default(), &Behaviour::default(), ForceCondition::ValidInputStepAndHash).unwrap().expect("the hub challenges");
        let _ = std::fs::remove_dir_all(&dir);
        let rounds = self.m().div_ceil(2) - 1;
        self.entries = play(&s, &Search { game_id: GAME_ID, rounds }).unwrap();
        self.heads = self.entries.iter().map(|e| e.head).collect();
        println!("SESS {}: Alice claims b = {b}: the program {:?} at step {}", self.terms.id, s.claim.0, s.claim.1);
    }
    fn level_keys(&mut self, d: u32) -> Vec<WotsPublic> {
        if let Some(k) = self.level_keys.get(&d) {
            return k.clone();
        }
        let id = self.terms.id;
        let k: Vec<WotsPublic> = (0..LEVELS).map(|ell| self.ks[mover_at(d).idx()].generate_wots(&format!("sess/level/{id}/{d}/{ell}"), LEVEL_BYTES).unwrap()).collect();
        self.level_keys.insert(d, k.clone());
        k
    }
    fn p_tree(&mut self, d: u32, w: &WindowMember) -> TapTree {
        let lk = self.level_keys(d);
        let l = Layout::at(d, GAME_ID, mover_at(d));
        rebuttal_tree(&self.g(), &self.ctx(), &l, self.k(d), w, &lk, self.terms.id, &self.outcomes).unwrap()
    }
    /// The SESSION contract, before any withdrawal: only `default` (the
    /// hub, after `T_close`) and `escalate`, Alice's unilateral start (her
    /// first move on chain, into the ladder). No absence claims: a
    /// force-close mid-session gives the hub nothing to spend before
    /// `T_close`.
    fn fund_session(&mut self, rt: &Regtest) -> Funded {
        let ctx = self.ctx();
        let l = Layout::at(1, GAME_ID, mover_at(1));
        let leaves = vec![default_leaf(&ctx, self.terms.t_close), escalate_leaf(&self.g(), &ctx, &l, self.k(1))];
        let tree = TapTree::new(leaves).unwrap();
        let (op, out) = rt.fund(&tree.script_pubkey(), self.value()).unwrap();
        Funded { tree, op, out }
    }
    /// The GAME contract, signed at a cooperative start at height `h0`
    /// (Alice's first move already sent): `absent_d` for every later depth,
    /// its deadline counted from the start (`h0 + d`), `escalate` (either
    /// party takes the game onto the ladder, replaying the moves so far),
    /// and `settle` after the last deadline; no default.
    fn fund_game(&mut self, rt: &Regtest, h0: u32) -> Funded {
        let ctx = self.ctx();
        let l1 = Layout::at(1, GAME_ID, mover_at(1));
        let mut leaves = vec![settle_leaf(&ctx, self.settle_at(h0)), escalate_leaf(&self.g(), &ctx, &l1, self.k(1))];
        for d in 2..=self.m() {
            leaves.push(lngap_pos::graph::absent_leaf(&ctx, &format!("absent_{d}"), mover_at(d).other(), h0 + d));
        }
        let tree = TapTree::new(leaves).unwrap();
        let (op, out) = rt.fund(&tree.script_pubkey(), self.value()).unwrap();
        Funded { tree, op, out }
    }
    /// `V_max` and a fee reserve.
    fn value(&self) -> Amount {
        self.terms.v_max() + Amount::from_sat(2_000_000)
    }
    /// When a game started at `h0` settles: after the last depth's deadline
    /// and time for the hub to force the last step on chain.
    fn settle_at(&self, h0: u32) -> u32 {
        h0 + self.m() + SETTLE_GAP
    }
    fn ladder(&self, j: u32) -> TapTree {
        ladder_tree(&self.g(), &self.ctx(), GAME_ID, j, &self.keys, &self.outcomes).unwrap()
    }
    /// The pre-signed absence claim at `d` through window `window`.
    fn claim(&mut self, c: &Funded, d: u32, window: Vec<WindowMember>) -> Claim {
        let lk = self.level_keys(d);
        let ctx = self.ctx();
        let l = Layout::at(d, GAME_ID, mover_at(d));
        let a_tree = claim_tree(&self.g(), &ctx, &l, self.k(d), (d >= 2).then(|| self.k(d - 1)), self.keys.get(d as usize), &window, &self.outcomes).unwrap();
        let trees: Vec<TapTree> = lk.iter().map(|k| carrier_tree(&ctx, mover_at(d), k).unwrap()).collect();
        let carry = Amount::from_sat(CARRIER_SAT);
        let a_out = TxOut { value: c.out.value - self.params.presign_fee - carry * trees.len() as u64, script_pubkey: a_tree.script_pubkey() };
        let name = format!("absent_{d}");
        let leaf = c.tree.leaf(&name).unwrap();
        let mut outs = vec![a_out.clone()];
        outs.extend(trees.iter().map(|t| TxOut { value: carry, script_pubkey: t.script_pubkey() }));
        let mut tx = build_spend(c.op, &leaf.timelock, outs);
        let w = vec![sig(&self.hub.payment, &tx, 0, std::slice::from_ref(&c.out), &leaf.script), sig(&self.user.payment, &tx, 0, std::slice::from_ref(&c.out), &leaf.script)];
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &c.tree.control_block(&name).unwrap());
        let txid = tx.compute_txid();
        let carriers = trees.into_iter().enumerate().map(|(k, t)| (OutPoint { txid, vout: k as u32 + 1 }, tx.output[k + 1].clone(), t)).collect();
        Claim { d, a_tree, tx, a_out, window, carriers }
    }
    /// The pair reveal at `d` and both heads' authorship, wire order.
    fn post_wire(&mut self, d: u32) -> (Vec<Vec<u8>>, WotsSig) {
        let id = self.terms.id;
        let (new, mv) = (self.heads[(d - 1) as usize], mover_at(d));
        let new_auth = self.ks[mv.idx()].sign_wots(&instance::state_label(id, SEQ, d), &auth_message(&new)).unwrap();
        let mut w = vec![];
        let pair = if d == 1 {
            self.ks[mv.idx()].sign_wots(&instance::rebut_label(id, SEQ, d), &new).unwrap()
        } else {
            let prev = self.heads[(d - 2) as usize];
            let prior_auth = self.ks[mover_at(d - 1).idx()].sign_wots(&instance::state_label(id, SEQ, d - 1), &auth_message(&prev)).unwrap();
            w.extend(wots_wire_tied(&prior_auth));
            self.ks[mv.idx()].sign_wots(&instance::rebut_label(id, SEQ, d), &[prev.as_slice(), new.as_slice()].concat()).unwrap()
        };
        w.extend(wots_wire_tied(&new_auth));
        w.extend(wots_wire(&pair));
        (w, pair)
    }
    /// Post move `j` from `(op, out)` (the ladder output at `j - 1`, or for
    /// move 1 the contract output `c` through `escalate`), with the
    /// signatures the poster holds: an escalation replays the moves made.
    fn post(&mut self, rt: &Regtest, j: u32, op: OutPoint, out: &TxOut, c: Option<&Funded>) -> (OutPoint, TxOut) {
        let (tree, name) = match c {
            Some(c) => (c.tree.clone(), "escalate"),
            None => (self.ladder(j - 1), "post"),
        };
        let leaf = tree.leaf(name).unwrap();
        let t_out = TxOut { value: out.value - self.params.presign_fee, script_pubkey: self.ladder(j).script_pubkey() };
        let mut tx = build_spend(op, &leaf.timelock, vec![t_out.clone()]);
        let (mut w, _) = self.post_wire(j);
        w.push(sig(&self.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        w.push(sig(&self.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("posting move {j}: {e:#}"));
        println!("SESS {}: ladder post of move {j}: {} vB", self.terms.id, tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, t_out)
    }
    /// The mover's rebuttal of claim `c` through window member `wm`.
    fn rebut(&mut self, rt: &Regtest, c: &Claim, wm: usize, venue: &[VenueMember], tree: &PeriodTree, root_sig: &WotsSig) -> (OutPoint, TxOut, WotsSig) {
        let d = c.d;
        let w = c.window[wm].clone();
        let vm = &venue[w.member];
        let unfold: Vec<Transaction> = vm.chain.connector_path(w.period, w.slot).unwrap().into_iter().filter(|t| rt.confirmations(&t.compute_txid()).ok().flatten().is_none()).collect();
        if !unfold.is_empty() {
            rt.mine_with(&unfold).unwrap();
        }
        let p_tree = self.p_tree(d, &w);
        let a_op = OutPoint { txid: c.tx.compute_txid(), vout: 0 };
        let carried: u64 = c.carriers.iter().map(|x| x.1.value.to_sat()).sum();
        let p_out = TxOut { value: c.a_out.value + w.leaf.1.value + Amount::from_sat(carried) - self.params.presign_fee, script_pubkey: p_tree.script_pubkey() };
        let mut ins = vec![(a_op, Sequence::ENABLE_RBF_NO_LOCKTIME), (w.leaf.0, Sequence::ENABLE_RBF_NO_LOCKTIME)];
        ins.extend(c.carriers.iter().map(|x| (x.0, Sequence::ENABLE_RBF_NO_LOCKTIME)));
        let mut tx = build_tx(&ins, vec![p_out.clone()], absolute::LockTime::ZERO);
        let (digests, siblings) = path_of(tree, w.slot);
        let id = self.terms.id;
        let levels: Vec<WotsSig> = (0..LEVELS).map(|ell| self.ks[mover_at(d).idx()].sign_wots(&format!("sess/level/{id}/{d}/{ell}"), &level_message(&digests[ell], &siblings[ell])).unwrap()).collect();
        let (post, pair) = self.post_wire(d);
        let name = format!("rebut_{}", w.member);
        let leaf = c.a_tree.leaf(&name).unwrap();
        let mut prevouts = vec![c.a_out.clone(), w.leaf.1.clone()];
        prevouts.extend(c.carriers.iter().map(|x| x.1.clone()));
        let mut wit = wots_wire(root_sig);
        wit.extend(post);
        wit.push(sig(&self.hub.payment, &tx, 0, &prevouts, &leaf.script));
        wit.push(sig(&self.user.payment, &tx, 0, &prevouts, &leaf.script));
        tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &c.a_tree.control_block(&name).unwrap());
        tx.input[1].witness = vm.chain.leaf_witness(w.period, w.slot, &vm.member.leaf_preimage(w.period, w.slot)).unwrap();
        let kp = if mover_at(d) == Role::User { &self.user.payment } else { &self.hub.payment };
        for (k, (cr, lv)) in c.carriers.iter().zip(&levels).enumerate() {
            let leaf = cr.2.leaf("carry").unwrap();
            let mut cw = wots_wire(lv);
            cw.push(sig(kp, &tx, k + 2, &prevouts, &leaf.script));
            tx.input[k + 2].witness = tapscript_witness(&cw, &leaf.script, &cr.2.control_block("carry").unwrap());
        }
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("the rebuttal at {d} must mine: {e:#}"));
        println!("SESS {id}: rebuttal at {d} through member {}: {} vB", w.member, tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, p_out, pair)
    }
    /// A 2-of-2 spend of `(op, out)` under `tree`'s leaf `name`, `wire`
    /// below the signatures, paying the withdrawal's decomposition.
    fn pay_b(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
        let outs = payout(&self.ctx(), &self.terms, &self.b_key(), out.value, self.params.presign_fee).unwrap();
        let mut tx = build_spend(op, &leaf.timelock, outs);
        let mut w = wire;
        w.push(sig(&self.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        w.push(sig(&self.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
        tx
    }
    /// Spend bit output `i` of a payout `tx` with Alice's signature on `b`:
    /// by Alice if the bit is set, else by the hub.
    fn spend_bit(&self, rt: &Regtest, tx: &Transaction, i: u32, b: u32) -> Transaction {
        let tree = bit_tree(&self.ctx(), i, &self.b_key()).unwrap();
        let set = (b >> i) & 1 == 1;
        let (name, who, kp) = if set { (format!("alice_bit_{i}"), Role::User, &self.user.payment) } else { (format!("hub_bit_{i}"), Role::Hub, &self.hub.payment) };
        let leaf = tree.leaf(&name).unwrap();
        let prev = tx.output[i as usize].clone();
        let op = OutPoint { txid: tx.compute_txid(), vout: i };
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs[who.idx()].payout_spk.clone() }]);
        let mut w = wots_wire(&self.b_sig(b));
        w.push(sig(kp, &s, 0, std::slice::from_ref(&prev), &leaf.script));
        s.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(&name).unwrap());
        // the other side's leaf fails on the same signature
        let (other, okp) = if set { (format!("hub_bit_{i}"), &self.hub.payment) } else { (format!("alice_bit_{i}"), &self.user.payment) };
        let oleaf = tree.leaf(&other).unwrap();
        let mut o = s.clone();
        let mut ow = wots_wire(&self.b_sig(b));
        ow.push(sig(okp, &o, 0, std::slice::from_ref(&prev), &oleaf.script));
        o.input[0].witness = tapscript_witness(&ow, &oleaf.script, &tree.control_block(&other).unwrap());
        assert!(rt.test_accept(&o).is_err(), "bit {i}: {other} must fail on b = {b}");
        if set {
            // Alice's leaf waits delta (the hub's equivocation window)
            rt.mine(u64::from(self.params.delta)).unwrap();
        }
        rt.mine_with(std::slice::from_ref(&s)).unwrap_or_else(|e| panic!("bit {i}: {name}: {e:#}"));
        s
    }
    /// The hub takes bit output `i` with two different signatures on `b`
    /// (Alice equivocated). Dry.
    fn equiv_bit(&self, tx: &Transaction, i: u32, b1: u32, b2: u32) -> Transaction {
        let tree = bit_tree(&self.ctx(), i, &self.b_key()).unwrap();
        let name = format!("equiv_b_{i}");
        let leaf = tree.leaf(&name).unwrap();
        let prev = tx.output[i as usize].clone();
        let op = OutPoint { txid: tx.compute_txid(), vout: i };
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs[1].payout_spk.clone() }]);
        let mut w = [wots_wire(&self.b_sig(b1)), wots_wire(&self.b_sig(b2))].concat();
        w.push(sig(&self.hub.payment, &s, 0, std::slice::from_ref(&prev), &leaf.script));
        s.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(&name).unwrap());
        s
    }
}

fn zk_leaf(id: u32, d: u32, head: &[u8; 48]) -> [u8; 20] {
    Choice { contract: id, depth: d as u16, value: ZkDated::choice_of(head) }.leaf()
}

fn terms(id: u32, t_close: u32) -> Terms {
    Terms { id, unit: Amount::from_sat(100_000), bits: 4, deposit: 10, t_close }
}

#[test]
fn sessions_on_regtest() {
    let rt = Regtest::start().unwrap();
    let mut l2 = L2::new(Keypair::from_seckey_slice(SECP256K1, &[0x5e; 32]).unwrap());
    l2.submit(Op::Mint { amount: 1_000 }).unwrap();
    let dir = std::env::temp_dir().join(format!("lngap-sess-prog-{}", std::process::id()));

    // ===== F: activation and a cooperative withdrawal =====
    {
        let t = terms(41, 0);
        let s = b"alice's session secret".to_vec();
        let hash = bitcoin::hashes::hash160::Hash::hash(&s).to_byte_array();
        let lock = l2.submit(Op::Lock { to: "alice".into(), amount: t.deposit, hash }).unwrap();
        l2.seal();
        l2.submit(Op::Claim { id: lock, preimage: s.clone() }).unwrap();
        l2.seal();
        // the hub learns s from the L2 and activates the contract
        assert_eq!(l2.balance("alice"), t.deposit);
        l2.submit(Op::Return { from: "alice".into(), amount: 5, memo: t.id }).unwrap();
        l2.seal();
        assert!(l2.is_final_return(5, t.id), "the hub's check of the withdrawal");
        let (alice, hub) = (t.unit * 5, t.v_max() - t.unit * 5);
        println!("SESS F: activated (s revealed on the L2), returned 5, folded: Alice {alice}, hub {hub}; nothing on chain");
    }
    // the venue, the sessions' programs and the search's shape
    let base = rt.height().unwrap() + 12;
    let venue = venue(&rt, base);
    let t_close = base + 400;
    // Alice's returns on the L2 (R and S); X's claim has no return
    for (b, c) in [(9u32, 42u32), (12, 44)] {
        l2.submit(Op::Transfer { from: HUB.into(), to: "alice".into(), amount: b }).unwrap();
        l2.submit(Op::Return { from: "alice".into(), amount: b, memo: c }).unwrap();
    }
    l2.seal();
    let returns = l2.final_returns();
    let pdf = |id: u32| write_program(&dir.join(id.to_string()), id, &returns).unwrap();
    let rounds = emulator::loader::program_definition::ProgramDefinition::from_config(&pdf(42)).unwrap().nary_def().total_rounds() as u32;
    let (mut r, mut x, mut st, mut df) = (
        Session::new(terms(42, t_close), &pdf(42), rounds),
        Session::new(terms(43, t_close), &pdf(43), rounds),
        Session::new(terms(44, t_close), &pdf(44), rounds),
        Session::new(terms(45, t_close), &pdf(45), rounds),
    );
    let (mut u, mut t) = (Session::new(terms(46, t_close), &pdf(46), rounds), Session::new(terms(47, t_close), &pdf(47), rounds));
    let mut e = Session::new(terms(48, t_close), &pdf(48), rounds);
    let m = r.m();
    println!("SESS the statement: {rounds} rounds, {m} depths; V_max {} in {} bits of {}", r.terms.v_max(), r.terms.bits, r.terms.unit);
    assert!(!l2.is_final_return(6, 43));
    r.play(9);
    x.play(6);
    u.play(12);
    e.play(3);

    // the members date Alice's final records (R at slot 0, X at slot 1)
    let tree = PeriodTree::new(vec![zk_leaf(42, m, &r.heads[(m - 1) as usize]), zk_leaf(43, m, &x.heads[(m - 1) as usize]), PAD_LEAF, PAD_LEAF]);
    rt.mine_to_height(venue[0].chain.spec.height(1) - 1).unwrap();
    for vm in &venue {
        rt.mine_with(&[vm.chain.close(&vm.member, 1, &tree.root()).unwrap()]).unwrap();
    }
    let roots: Vec<WotsSig> = venue.iter().map(|vm| vm.member.sign_root(1, &tree.root()).unwrap()).collect();

    let lock = base + 4;
    let wm = |i: usize, s: u32| window_member(i, &venue[i], s);
    let (cr, cx, cs) = (r.fund_game(&rt, lock), x.fund_game(&rt, lock), st.fund_game(&rt, lock));
    let (cd, cu) = (df.fund_session(&rt), u.fund_session(&rt));
    let ct = t.fund_game(&rt, lock);
    let ce = e.fund_game(&rt, lock);
    let claim_r = r.claim(&cr, m, vec![wm(0, 0), wm(1, 0)]);
    let claim_x = x.claim(&cx, m, vec![wm(0, 1), wm(1, 1)]);
    let claim_s = st.claim(&cs, 2, vec![wm(0, 2), wm(1, 2)]);
    rt.mine_to_height(lock + m + u32::from(r.params.to_self_delay)).unwrap();
    for c in [&claim_r, &claim_x, &claim_s] {
        rt.mine_with(std::slice::from_ref(&c.tx)).unwrap_or_else(|e| panic!("claim: {e:#}"));
    }
    let (delta, w) = (r.params.delta, r.params.delta + r.params.delta_prime);
    let w_win = w;
    // settle's transaction exists from the start, but not before the game's end
    let settle = t.pay_b(&ct.tree, ct.op, &ct.out, "settle", vec![]);
    assert!(rt.height().unwrap() < t.settle_at(lock) && rt.test_accept(&settle).is_err(), "settle: not before the game's end");

    // ===== R: the hub refused; the final step is proved; b paid =====
    {
        let (p_op, p_out, pair) = r.rebut(&rt, &claim_r, 0, &venue, &tree, &roots[0]);
        let p_tree = r.p_tree(m, &claim_r.window[0].clone());
        let last = r.entries.last().unwrap().clone();
        let rec = last.record.unwrap();
        let class = lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap();
        let proof = r.pay_b(&p_tree, p_op, &p_out, &format!("zk_prove_{class}"), [final_witness(&last.state, &rec), wots_wire(&pair)].concat());
        assert!(rt.test_accept(&proof).is_err(), "R: the proof waits out the hub's window");
        rt.mine(u64::from(w)).unwrap();
        rt.mine_with(std::slice::from_ref(&proof)).unwrap_or_else(|e| panic!("R: the pre-signed proof: {e:#}"));
        println!("SESS R: zk_prove_{class} (pre-signed) paying b = 9 in {} bit outputs: {} vB", r.terms.bits, proof.vsize());
        for i in 0..r.terms.bits {
            r.spend_bit(&rt, &proof, i, 9);
        }
        println!("SESS R: Alice took bits 0 and 3 (9 x {}), the hub bits 1 and 2", r.terms.unit);
    }

    // ===== X: a false claim; halt_exit =====
    {
        let (p_op, p_out, pair) = x.rebut(&rt, &claim_x, 1, &venue, &tree, &roots[1]);
        let p_tree = x.p_tree(m, &claim_x.window[1].clone());
        let last = x.entries.last().unwrap().clone();
        let (rec, cl) = (last.record.unwrap(), x.entries[0].claim.unwrap());
        rt.mine(u64::from(delta)).unwrap();
        let leaf = p_tree.leaf("disprove_zk_halt_exit").unwrap();
        let mut tx = build_spend(p_op, &leaf.timelock, vec![TxOut { value: p_out.value - x.params.presign_fee, script_pubkey: x.pubs[1].payout_spk.clone() }]);
        let mut wit = [nibble_witness(&rec.to_bytes()), nibble_witness(&cl.to_bytes()), wots_wire(&pair)].concat();
        wit.push(sig(&x.hub.payment, &tx, 0, std::slice::from_ref(&p_out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &p_tree.control_block("disprove_zk_halt_exit").unwrap());
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("X: halt_exit must fire: {e:#}"));
        println!("SESS X: the execution halted with exit 1; disprove_zk_halt_exit: {} vB. The hub wins.", tx.vsize());
    }

    // ===== S: the hub stalls at depth 2; the timeout split pays b =====
    {
        let a_op = OutPoint { txid: claim_s.tx.compute_txid(), vout: 0 };
        let id = st.terms.id;
        let reveal = st.ks[0].reveal_uint(&instance::ccode_label(id, SEQ, 2), 0).unwrap();
        let mut wire = reveal.consumption_order();
        wire.reverse();
        let split = st.pay_b(&claim_s.a_tree, a_op, &claim_s.a_out, "split_UserWins", wire);
        rt.mine(u64::from(delta)).unwrap();
        rt.mine_with(std::slice::from_ref(&split)).unwrap_or_else(|e| panic!("S: the timeout split: {e:#}"));
        println!("SESS S: the hub never answered; the timeout split pays b = 12: {} vB", split.vsize());
        for i in 0..st.terms.bits {
            st.spend_bit(&rt, &split, i, 12);
        }
    }

    // ===== H8, H1, A6: the session contract; the hub force-closes, then disappears =====
    {
        // H8: before any withdrawal the session output carries only the
        // default and Alice's start, so the hub can spend nothing before T_close
        let names: Vec<&str> = cu.tree.leaves().iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names.len(), 2, "H8: {names:?}");
        assert!(names.contains(&"default") && names.contains(&"escalate"), "H8: {names:?}");
        println!("SESS H8: the session output carries only {names:?}: no absence claim exists before a withdrawal starts");
        // H1: Alice starts unilaterally, her first move on chain, into the ladder
        let leaf = cu.tree.leaf("escalate").unwrap();
        let l1 = u.ladder(1);
        let t_out = TxOut { value: cu.out.value - u.params.presign_fee, script_pubkey: l1.script_pubkey() };
        let mut tx = build_spend(cu.op, &leaf.timelock, vec![t_out.clone()]);
        let (mut w, _) = u.post_wire(1);
        w.push(sig(&u.hub.payment, &tx, 0, std::slice::from_ref(&cu.out), &leaf.script));
        w.push(sig(&u.user.payment, &tx, 0, std::slice::from_ref(&cu.out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &cu.tree.control_block("escalate").unwrap());
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("H1: the unilateral start: {e:#}"));
        println!("SESS H1: Alice's unilateral start (escalate: her claim on chain): {} vB", tx.vsize());
        // the hub never posts move 2: after w, Alice's ladder split pays b
        let l1_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
        let split = u.pay_b(&l1, l1_op, &t_out, "split_UserWins", vec![]);
        assert!(rt.test_accept(&split).is_err(), "H1: not before the hub's window ends");
        rt.mine(u64::from(w_win)).unwrap();
        rt.mine_with(std::slice::from_ref(&split)).unwrap_or_else(|e| panic!("H1: the ladder split: {e:#}"));
        println!("SESS H1: the hub never answered; the ladder split pays b = 12: {} vB", split.vsize());
        // A6: had Alice also signed b = 13, the hub takes a bit of hers (bit 2
        // is set in 12) before her delay runs out, with the two signatures
        let eq = u.equiv_bit(&split, 2, 12, 13);
        rt.mine_with(std::slice::from_ref(&eq)).unwrap_or_else(|e| panic!("A6: equiv_b: {e:#}"));
        println!("SESS A6: two signatures on b: the hub takes bit 2 with equiv_b: {} vB", eq.vsize());
        for i in [0, 1, 3] {
            u.spend_bit(&rt, &split, i, 12);
        }
    }

    // ===== E1: the hub escalates mid-game; the whole history is replayed =====
    {
        // five moves were played off-chain; the hub escalates (after
        // to_self_delay) and replays them from the signatures it holds
        let mut at = e.post(&rt, 1, ce.op, &ce.out, Some(&ce));
        for j in 2..=5 {
            at = e.post(&rt, j, at.0, &at.1, None);
        }
        // the hub, whose move 6 is next, stops: after w, Alice's split pays b
        let split = e.pay_b(&e.ladder(5), at.0, &at.1, "split_UserWins", vec![]);
        assert!(rt.test_accept(&split).is_err(), "E1: not before the hub's window ends");
        rt.mine(u64::from(w_win)).unwrap();
        rt.mine_with(std::slice::from_ref(&split)).unwrap_or_else(|e| panic!("E1: the ladder split: {e:#}"));
        println!("SESS E1: the hub escalated after 5 moves and replayed them; then it stopped; Alice's split pays b = 3: {} vB", split.vsize());
        for i in 0..e.terms.bits {
            e.spend_bit(&rt, &split, i, 3);
        }
    }

    // ===== settle: a game where the hub never forces the last step =====
    {
        if rt.height().unwrap() < t.settle_at(lock) {
            rt.mine_to_height(t.settle_at(lock)).unwrap();
        }
        rt.mine_with(std::slice::from_ref(&settle)).unwrap_or_else(|e| panic!("settle: {e:#}"));
        println!("SESS settle: after the game's end, Alice's claim accepted, b = 5 paid: {} vB", settle.vsize());
        for i in 0..t.terms.bits {
            t.spend_bit(&rt, &settle, i, 5);
        }
    }

    // ===== D: no claim by T_close; the hub takes the contract =====
    {
        let leaf = cd.tree.leaf("default").unwrap();
        let mut tx = build_spend(cd.op, &leaf.timelock, vec![TxOut { value: cd.out.value - Amount::from_sat(2_000), script_pubkey: df.pubs[1].payout_spk.clone() }]);
        let s0 = sig(&df.hub.payment, &tx, 0, std::slice::from_ref(&cd.out), &leaf.script);
        tx.input[0].witness = tapscript_witness(&[s0], &leaf.script, &cd.tree.control_block("default").unwrap());
        assert!(rt.test_accept(&tx).is_err(), "D: not before T_close");
        rt.mine_to_height(t_close).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("D: the default: {e:#}"));
        println!("SESS D: the default after T_close: {} vB", tx.vsize());
    }
    let _ = std::fs::remove_dir_all(&dir);
}
