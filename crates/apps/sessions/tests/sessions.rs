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
//! - D, the default: no claim by T_close; the hub takes the contract.
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
use lngap_sessions::session::{bit_tree, default_leaf, payout, Terms};
use lngap_sessions::statement::{input, write_program};
use lngap_tictactoe::TicTacToe;
use lngap_v25::{carrier_tree, claim_tree, level_message, rebuttal_tree, self_post_leaf, WindowMember, ZkDated, CARRIER_SAT, LEVEL_BYTES};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::{search, Behaviour};
use lngap_zk::family::ZkFamily;
use lngap_zk::final_d60::{input_key_params, input_message};
use lngap_zk::game::{final_witness, play, Entry, Search};
use lngap_zk::nibble_witness;

const GAME_ID: u16 = 1;
const SEQ: u64 = 1;
const LEVELS: usize = 2;

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
    /// The contract output: `absent_d` and `self_post_d` at every depth
    /// (a claim at `d` valid after `lock + d`: each depth's deadline
    /// follows the last), and the default after `T_close`.
    fn fund(&mut self, rt: &Regtest, lock: u32) -> Funded {
        let ctx = self.ctx();
        let mut leaves = vec![default_leaf(&ctx, self.terms.t_close)];
        for d in 1..=self.m() {
            let l = Layout::at(d, GAME_ID, mover_at(d));
            leaves.push(lngap_pos::graph::absent_leaf(&ctx, &format!("absent_{d}"), mover_at(d).other(), lock + d));
            let mut sp = self_post_leaf(&self.g(), &ctx, &l, self.k(d), (d >= 2).then(|| self.k(d - 1)));
            sp.name = format!("self_post_{d}");
            leaves.push(sp);
        }
        let tree = TapTree::new(leaves).unwrap();
        let value = self.terms.v_max() + Amount::from_sat(2_000_000); // V_max and a fee reserve
        let (op, out) = rt.fund(&tree.script_pubkey(), value).unwrap();
        Funded { tree, op, out }
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
        rt.mine_with(std::slice::from_ref(&s)).unwrap_or_else(|e| panic!("bit {i}: {name}: {e:#}"));
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
    let m = r.m();
    println!("SESS the statement: {rounds} rounds, {m} depths; V_max {} in {} bits of {}", r.terms.v_max(), r.terms.bits, r.terms.unit);
    assert!(!l2.is_final_return(6, 43));
    r.play(9);
    x.play(6);

    // the members date Alice's final records (R at slot 0, X at slot 1)
    let tree = PeriodTree::new(vec![zk_leaf(42, m, &r.heads[(m - 1) as usize]), zk_leaf(43, m, &x.heads[(m - 1) as usize]), PAD_LEAF, PAD_LEAF]);
    rt.mine_to_height(venue[0].chain.spec.height(1) - 1).unwrap();
    for vm in &venue {
        rt.mine_with(&[vm.chain.close(&vm.member, 1, &tree.root()).unwrap()]).unwrap();
    }
    let roots: Vec<WotsSig> = venue.iter().map(|vm| vm.member.sign_root(1, &tree.root()).unwrap()).collect();

    let lock = base + 4;
    let wm = |i: usize, s: u32| window_member(i, &venue[i], s);
    let (cr, cx, cs, cd) = (r.fund(&rt, lock), x.fund(&rt, lock), st.fund(&rt, lock), df.fund(&rt, lock));
    let claim_r = r.claim(&cr, m, vec![wm(0, 0), wm(1, 0)]);
    let claim_x = x.claim(&cx, m, vec![wm(0, 1), wm(1, 1)]);
    let claim_s = st.claim(&cs, 2, vec![wm(0, 2), wm(1, 2)]);
    rt.mine_to_height(lock + m + u32::from(r.params.to_self_delay)).unwrap();
    for c in [&claim_r, &claim_x, &claim_s] {
        rt.mine_with(std::slice::from_ref(&c.tx)).unwrap_or_else(|e| panic!("claim: {e:#}"));
    }
    let (delta, w) = (r.params.delta, r.params.delta + r.params.delta_prime);

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
