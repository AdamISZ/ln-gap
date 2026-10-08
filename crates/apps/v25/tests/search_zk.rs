//! V25_POC_PLAN.md Phase 5 on regtest: the search over a verifier
//! (`lngap-zk`, hello-world in binary search: 11 rounds, 23 depths; the
//! prover is the user, at odd depths) with its moves dated by members.
//! The dated choice is the 44 head bytes the mover's state key signs.
//!
//! - Z1, the honest O(1) path: the verifier claims the prover absent at
//!   depth 5; the prover rebuts through member 1; the level disproves don't
//!   fire; the prover's split pays after `delta + delta'`;
//! - Z2, the final step: the verifier claims the prover absent at 23; the
//!   prover rebuts through member 0 and proves the step (D59), after the
//!   verifier's window;
//! - Z4, depth 1: a false claim at the prover's first move (no prior head),
//!   rebutted;
//! - Z3, a member fault forces the ladder: member 0 equivocated; the user
//!   claims the verifier absent at 2; the hub rebuts through member 0; the
//!   pair sends the game on chain (`pair_continue`), where depths 3..23
//!   are posted and the prover proves the final step. Measured: each post,
//!   the ladder's total vsize, its worst-case block count.
//!
//! Run with `--test-threads=1` or 2.

mod common;

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Instant;

use bitcoin::{absolute, Amount, OutPoint, Sequence, Transaction, TxOut};
use common::{mine_missing, path_of, sig, venue, window_member, Open, VenueMember, GAME_ID, LEVELS, SEQ};
use emulator::decision::challenge::ForceCondition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
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
use lngap_seal::dating::{Choice, PeriodTree};
use lngap_tictactoe::TicTacToe;
use lngap_v25::{carrier_tree, claim_tree, ladder_tree, level_message, rebuttal_tree, self_post_leaf, WindowMember, ZkDated, CARRIER_SAT, LEVEL_BYTES};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::{search, Behaviour, Searched};
use lngap_zk::family::ZkFamily;
use lngap_zk::final_d60::input_key_params;
use lngap_zk::game::{final_witness, play, Entry, Search};

const VALID: [u8; 4] = [0x11; 4];

fn pdf() -> String {
    format!("{}/../zk/programs/hello-world-binary.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn run_search(pdf: &str, input: &[u8]) -> Searched {
    let dir = std::env::temp_dir().join(format!("lngap-v25-zk-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let s = search(pdf, input, &dir, &Behaviour::default(), &Behaviour::default(), ForceCondition::ValidInputStepAndHash).unwrap().expect("the verifier challenges");
    let _ = std::fs::remove_dir_all(&dir);
    s
}

/// The leaf a member dates for depth `d` of contract `id`.
fn zk_leaf(id: u32, d: u32, head: &[u8; 48]) -> [u8; 20] {
    Choice { contract: id, depth: d as u16, value: ZkDated::choice_of(head) }.leaf()
}

/// One search contract between the user (prover) and the hub (verifier).
struct Z {
    id: u32,
    user: PartyKeys,
    hub: PartyKeys,
    ks: [KeyStore; 2],
    params: ChannelParams,
    pubs: [PartyPubKeys; 2],
    keys: Vec<PosDepthKeys>,
    family: Arc<ZkFamily>,
    outcomes: Vec<Outcome>,
    level_keys: HashMap<u32, Vec<WotsPublic>>,
    heads: Vec<[u8; 48]>,
}

impl Z {
    fn new(id: u32, entries: &[Entry], search: Search, pdf: &str) -> Z {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("v25z/{id}/user")));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("v25z/{id}/hub")));
        let mut ks = [KeyStore::new(Seed::from_label(&format!("v25z/{id}/user-ks"))), KeyStore::new(Seed::from_label(&format!("v25z/{id}/hub-ks")))];
        let m = search.depths();
        let ou = instance::gen_pos_keys(&mut ks[0], Role::User, id, SEQ, m, instance::Game::Zk).unwrap();
        let oh = instance::gen_pos_keys(&mut ks[1], Role::Hub, id, SEQ, m, instance::Game::Zk).unwrap();
        let keys = instance::collect_keys(&ou, &oh, m).unwrap();
        let info = ProgramInfo::load(pdf).unwrap();
        let input_keys: Vec<WotsPublic> = (0..info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0xa0 + j as u8 + id as u8; 32]).public()).collect();
        let family = ZkFamily::new(search, info, input_keys);
        // posts and proofs run to tens of kvB: the pre-sign fee clears the
        // relay floor for them
        let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::from_sat(4_000_000)) };
        let pubs = [user.public(), hub.public()];
        let heads = entries.iter().map(|e| e.head).collect();
        Z { id, user, hub, ks, params, pubs, keys, family, outcomes: Contract::outcomes(&TicTacToe), level_keys: HashMap::new(), heads }
    }
    fn g(&self) -> ZkDated<'_> {
        ZkDated(self.family.as_ref())
    }
    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::Hub, seq: SEQ, rev_hash: [0u8; 20] }
    }
    fn head(&self, d: u32) -> [u8; 48] {
        self.heads[(d - 1) as usize]
    }
    fn k(&self, d: u32) -> &PosDepthKeys {
        &self.keys[(d - 1) as usize]
    }
    /// The mover's level keys for depth `d`, one per path level.
    fn level_keys(&mut self, d: u32) -> Vec<WotsPublic> {
        if let Some(k) = self.level_keys.get(&d) {
            return k.clone();
        }
        let id = self.id;
        let k: Vec<WotsPublic> = (0..LEVELS).map(|ell| self.ks[mover_at(d).idx()].generate_wots(&level_label(id, d, ell), LEVEL_BYTES).unwrap()).collect();
        self.level_keys.insert(d, k.clone());
        k
    }
    /// The level reveals of `tree`'s path at `slot`, for depth `d`.
    fn sign_levels(&mut self, d: u32, tree: &PeriodTree, slot: u32) -> Vec<WotsSig> {
        let (digests, siblings) = path_of(tree, slot);
        let id = self.id;
        (0..LEVELS).map(|ell| self.ks[mover_at(d).idx()].sign_wots(&level_label(id, d, ell), &level_message(&digests[ell], &siblings[ell])).unwrap()).collect()
    }
    fn p_tree(&mut self, d: u32, w: &WindowMember) -> TapTree {
        let lk = self.level_keys(d);
        let l = Layout::at(d, GAME_ID, mover_at(d));
        rebuttal_tree(&self.g(), &self.ctx(), &l, self.k(d), w, &lk, self.id, &self.outcomes).unwrap()
    }
    fn ladder(&self, j: u32) -> TapTree {
        ladder_tree(&self.g(), &self.ctx(), GAME_ID, j, &self.keys, &self.outcomes).unwrap()
    }
    /// The pair reveal of depth `d` and both heads' authorship, wire order.
    fn post_wire(&mut self, d: u32) -> (Vec<Vec<u8>>, WotsSig) {
        let id = self.id;
        let (new, mv) = (self.head(d), mover_at(d));
        let new_auth = self.ks[mv.idx()].sign_wots(&instance::state_label(id, SEQ, d), &auth_message(&new)).unwrap();
        let mut w = vec![];
        let pair = if d == 1 {
            // no prior: the reveal is of the head alone
            self.ks[mv.idx()].sign_wots(&instance::rebut_label(id, SEQ, d), &new).unwrap()
        } else {
            let prev = self.head(d - 1);
            let prior_auth = self.ks[mover_at(d - 1).idx()].sign_wots(&instance::state_label(id, SEQ, d - 1), &auth_message(&prev)).unwrap();
            w.extend(wots_wire_tied(&prior_auth));
            self.ks[mv.idx()].sign_wots(&instance::rebut_label(id, SEQ, d), &[prev.as_slice(), new.as_slice()].concat()).unwrap()
        };
        w.extend(wots_wire_tied(&new_auth));
        w.extend(wots_wire(&pair));
        (w, pair)
    }
}

fn level_label(id: u32, d: u32, ell: usize) -> String {
    format!("v25z/level/{id}/{d}/{ell}")
}

/// Fund the contract output (`absent_d` after `lock`, `self_post_d`) and
/// pre-sign the claim.
fn open(rt: &Regtest, z: &mut Z, d: u32, window: Vec<WindowMember>, lock: u32) -> Open {
    let lk = z.level_keys(d);
    let ctx = z.ctx();
    let l = Layout::at(d, GAME_ID, mover_at(d));
    let (kp, kn) = ((d >= 2).then(|| z.k(d - 1)), z.k(d));
    let a_tree = claim_tree(&z.g(), &ctx, &l, kn, kp, z.keys.get(d as usize), &window, &z.outcomes).unwrap();
    let name = format!("absent_{d}");
    let absent = lngap_pos::graph::absent_leaf(&ctx, &name, mover_at(d).other(), lock);
    let c_tree = TapTree::new(vec![absent, self_post_leaf(&z.g(), &ctx, &l, kn, kp)]).unwrap();
    // enough for a ladder of 59 posts at the pre-sign fee
    let value = Amount::from_sat(6_000_000);
    let (c_op, c_out) = rt.fund(&c_tree.script_pubkey(), value).unwrap();
    let trees: Vec<TapTree> = lk.iter().map(|k| carrier_tree(&ctx, mover_at(d), k).unwrap()).collect();
    let carry = Amount::from_sat(CARRIER_SAT);
    let a_out = TxOut { value: value - z.params.presign_fee - carry * trees.len() as u64, script_pubkey: a_tree.script_pubkey() };
    let leaf = c_tree.leaf(&name).unwrap();
    let mut outs = vec![a_out.clone()];
    outs.extend(trees.iter().map(|t| TxOut { value: carry, script_pubkey: t.script_pubkey() }));
    let mut claim = build_spend(c_op, &leaf.timelock, outs);
    let w = vec![sig(&z.hub.payment, &claim, 0, std::slice::from_ref(&c_out), &leaf.script), sig(&z.user.payment, &claim, 0, std::slice::from_ref(&c_out), &leaf.script)];
    claim.input[0].witness = tapscript_witness(&w, &leaf.script, &c_tree.control_block(&name).unwrap());
    let txid = claim.compute_txid();
    let carriers = trees.into_iter().enumerate().map(|(k, t)| (OutPoint { txid, vout: k as u32 + 1 }, claim.output[k + 1].clone(), t)).collect();
    Open { a_tree, claim, a_out, window, c_tree, c_op, c_out, carriers }
}

/// The mover's rebuttal at `d` through window member `wm`.
#[allow(clippy::too_many_arguments)]
fn rebut(rt: &Regtest, z: &mut Z, d: u32, o: &Open, wm: usize, venue: &[VenueMember], tree: &PeriodTree, root_sig: &WotsSig) -> (OutPoint, TxOut, WotsSig, Vec<WotsSig>) {
    let w = o.window[wm].clone();
    let vm = &venue[w.member];
    mine_missing(rt, &vm.chain.connector_path(w.period, w.slot).unwrap());
    let p_tree = z.p_tree(d, &w);
    let a_op = OutPoint { txid: o.claim.compute_txid(), vout: 0 };
    let carried: u64 = o.carriers.iter().map(|c| c.1.value.to_sat()).sum();
    let p_out = TxOut { value: o.a_out.value + w.leaf.1.value + Amount::from_sat(carried) - z.params.presign_fee, script_pubkey: p_tree.script_pubkey() };
    let mut ins = vec![(a_op, Sequence::ENABLE_RBF_NO_LOCKTIME), (w.leaf.0, Sequence::ENABLE_RBF_NO_LOCKTIME)];
    ins.extend(o.carriers.iter().map(|c| (c.0, Sequence::ENABLE_RBF_NO_LOCKTIME)));
    let mut tx = build_tx(&ins, vec![p_out.clone()], absolute::LockTime::ZERO);
    let levels = z.sign_levels(d, tree, w.slot);
    let (post, pair) = z.post_wire(d);
    let name = format!("rebut_{}", w.member);
    let leaf = o.a_tree.leaf(&name).unwrap();
    let mut prevouts = vec![o.a_out.clone(), w.leaf.1.clone()];
    prevouts.extend(o.carriers.iter().map(|c| c.1.clone()));
    let mut wit = wots_wire(root_sig);
    wit.extend(post);
    wit.push(sig(&z.hub.payment, &tx, 0, &prevouts, &leaf.script));
    wit.push(sig(&z.user.payment, &tx, 0, &prevouts, &leaf.script));
    tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &o.a_tree.control_block(&name).unwrap());
    tx.input[1].witness = vm.chain.leaf_witness(w.period, w.slot, &vm.member.leaf_preimage(w.period, w.slot)).unwrap();
    let kp = if mover_at(d) == Role::User { &z.user.payment } else { &z.hub.payment };
    for (k, (c, lv)) in o.carriers.iter().zip(&levels).enumerate() {
        let leaf = c.2.leaf("carry").unwrap();
        let mut cw = wots_wire(lv);
        cw.push(sig(kp, &tx, k + 2, &prevouts, &leaf.script));
        tx.input[k + 2].witness = tapscript_witness(&cw, &leaf.script, &c.2.control_block("carry").unwrap());
    }
    rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("the rebuttal at {d} must mine: {e:#}"));
    let carrier_vb = (tx.input[2].witness.size() as f64 / 4.0 + 41.0).round();
    println!("V25Z rebuttal at {d} through member {}: {} vB (one carrier input: {carrier_vb} vB)", w.member, tx.vsize());
    (OutPoint { txid: tx.compute_txid(), vout: 0 }, p_out, pair, levels)
}

/// A spend of `(op, out)` under `tree`'s leaf `name`: `below`, the pair
/// reveal, then `who`'s signature; paid to `who`. Dry.
#[allow(clippy::too_many_arguments)]
fn mover_spend(z: &Z, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, below: Vec<Vec<u8>>, pair: &WotsSig, who: Role) -> Transaction {
    spend(z, tree, op, out, name, [below, wots_wire(pair)].concat(), who)
}

/// A spend of `(op, out)` under `tree`'s leaf `name`: `wire`, then `who`'s
/// signature; paid to `who`. Dry.
fn spend(z: &Z, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>, who: Role) -> Transaction {
    let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
    let mut tx = build_spend(op, &leaf.timelock, vec![TxOut { value: out.value - z.params.presign_fee, script_pubkey: z.pubs[who.idx()].payout_spk.clone() }]);
    let kp = if who == Role::User { &z.user.payment } else { &z.hub.payment };
    let mut w = wire;
    w.push(sig(kp, &tx, 0, std::slice::from_ref(out), &leaf.script));
    tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
    tx
}

/// A 2-of-2 spend of `(op, out)` under `tree`'s leaf `name`, with `wire`
/// below the signatures, to `outs`. Dry.
fn two_of_two(z: &Z, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>, outs: Vec<TxOut>) -> Transaction {
    let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
    let mut tx = build_spend(op, &leaf.timelock, outs);
    let mut w = wire;
    w.push(sig(&z.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
    w.push(sig(&z.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
    tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
    tx
}

fn prove_name(e: &Entry) -> String {
    let r = e.record.unwrap();
    format!("zk_prove_{}", lngap_zk::guard::key_of(r.read.opcode, r.read.micro).expect("a decodable class"))
}

/// The pre-signed transactions of one contract with a window of `wn`
/// members at every depth, counted from the built trees (every leaf a
/// party signs ahead: claims, self-posts, rebuttals, waivers, splits,
/// continuations, posts; not the disproves and proofs, which carry their
/// spender's signature at dispute time), and the build time.
fn presigned(z: &mut Z, venue: &[VenueMember], wn: usize) -> (usize, std::time::Duration) {
    let t = Instant::now();
    let m = z.keys.len() as u32;
    // members beyond the venue's reuse its chains with another period's
    // keys (the scripts must differ; the count is what matters)
    let v = venue.len();
    let window: Vec<WindowMember> = (0..wn)
        .map(|i| {
            let base = window_member(i % v, &venue[i % v], 0);
            let pk = &venue[i % v].chain.member;
            WindowMember { member: i, period: 1 + (i / v) as u32, root_key: pk.roots[i / v].clone(), empty_hash: pk.empties[i / v], ..base }
        })
        .collect();
    let signed = |t: &TapTree, runtime: &[&str]| t.leaves().iter().filter(|l| !runtime.iter().any(|r| l.name.starts_with(r)) && !l.script.as_bytes().ends_with(&[bitcoin::opcodes::all::OP_RETURN.to_u8()])).count();
    let runtime = ["disprove_", "leaf_hash", "node_", "zk_prove_"];
    let mut n = 0;
    for d in 1..=m {
        let ctx = z.ctx();
        let l = Layout::at(d, GAME_ID, mover_at(d));
        let (kp, kn) = ((d >= 2).then(|| z.k(d - 1)), z.k(d));
        let a = claim_tree(&z.g(), &ctx, &l, kn, kp, z.keys.get(d as usize), &window, &z.outcomes).unwrap();
        n += 2 + signed(&a, &runtime); // absent_d and self_post_d, then A_d's
        for w in &window {
            let p = z.p_tree(d, w);
            n += signed(&p, &runtime);
        }
        n += signed(&z.ladder(d), &runtime);
    }
    (n, t.elapsed())
}

/// The scenarios on one program: the search is run by BitVMX, played as
/// the game, and four contracts are disputed with members dating moves.
fn scenarios(pdf: &str, input: &[u8], tag: &str) {
    let rt = Regtest::start().unwrap();
    let t0 = Instant::now();
    let a = run_search(pdf, input);
    let rounds = emulator::loader::program_definition::ProgramDefinition::from_config(pdf).unwrap().nary_def().total_rounds() as u32;
    let search = Search { game_id: GAME_ID, rounds };
    let entries = play(&a, &search).unwrap();
    let m = search.depths();
    assert_eq!(entries.len() as u32, m);
    println!("V25Z [{tag}] the search: {rounds} rounds, {m} depths, step {}; {:.1?}", a.step, t0.elapsed());
    let last = entries.last().unwrap().clone();
    let (z1d, z2d, z3d, z4d) = (5u32, m, 2u32, 1u32);
    let mk = |id| Z::new(id, &entries, search, pdf);
    let (mut z1, mut z2, mut z3, mut z4) = (mk(31), mk(32), mk(33), mk(34));

    let base = rt.height().unwrap() + 12;
    let venue = venue(&rt, base, 2);
    // the members' period-1 trees: Z1 at slot 0, Z2 at 1, Z3 at 2, Z4 at 3
    let mut leaves = vec![
        zk_leaf(31, z1d, &z1.head(z1d)),
        zk_leaf(32, z2d, &z2.head(z2d)),
        zk_leaf(33, z3d, &z3.head(z3d)),
        zk_leaf(34, z4d, &z4.head(z4d)),
    ];
    let tree = PeriodTree::new(leaves.clone());
    leaves[3] = [0xEE; 20];
    let second = PeriodTree::new(leaves); // member 0's second root
    rt.mine_to_height(venue[0].chain.spec.height(1) - 1).unwrap();
    for vm in &venue {
        rt.mine_with(&[vm.chain.close(&vm.member, 1, &tree.root()).unwrap()]).unwrap();
    }
    let roots: Vec<WotsSig> = venue.iter().map(|vm| vm.member.sign_root(1, &tree.root()).unwrap()).collect();
    let root0_second = venue[0].member.sign_root(1, &second.root()).unwrap();

    let (n, took) = presigned(&mut z1, &venue, 4);
    println!("V25Z [{tag}] one contract, a window of 4 at every depth: {n} pre-signed transactions; all trees built in {took:.1?}");

    let lock = base + 4;
    let wm = |i: usize, s: u32| window_member(i, &venue[i], s);
    let o1 = open(&rt, &mut z1, z1d, vec![wm(0, 0), wm(1, 0)], lock);
    let o2 = open(&rt, &mut z2, z2d, vec![wm(0, 1), wm(1, 1)], lock);
    let o3 = open(&rt, &mut z3, z3d, vec![wm(0, 2), wm(1, 2)], lock);
    let o4 = open(&rt, &mut z4, z4d, vec![wm(0, 3), wm(1, 3)], lock);
    rt.mine_to_height(lock + u32::from(z1.params.to_self_delay)).unwrap();
    for o in [&o1, &o2, &o3, &o4] {
        rt.mine_with(std::slice::from_ref(&o.claim)).unwrap_or_else(|e| panic!("claim: {e:#}"));
    }
    let (delta, w) = (z1.params.delta, z1.params.delta + z1.params.delta_prime);
    let pay = |z: &Z, out: &TxOut, r: Role| vec![TxOut { value: out.value - z.params.presign_fee, script_pubkey: z.pubs[r.idx()].payout_spk.clone() }];

    // ---- Z1: a false claim at 5; the prover's split after w ----
    let (p_op, p_out, pair, levels) = rebut(&rt, &mut z1, z1d, &o1, 1, &venue, &tree, &roots[1]);
    let p_tree = z1.p_tree(z1d, &o1.window[1].clone());
    rt.mine(u64::from(delta)).unwrap();
    let lh = spend(&z1, &p_tree, p_op, &p_out, "leaf_hash", [wots_wire(&pair), wots_wire(&levels[0])].concat(), Role::Hub);
    assert!(rt.test_accept(&lh).is_err(), "Z1: leaf_hash does not fire on an honest dating");
    let top = spend(&z1, &p_tree, p_op, &p_out, &format!("node_{}", LEVELS - 1), [wots_wire(&levels[LEVELS - 1]), wots_wire(&roots[1])].concat(), Role::Hub);
    assert!(rt.test_accept(&top).is_err(), "Z1: the top level leads to the member's root");
    println!("V25Z leaf_hash (dry): {} vB; node_{} (dry): {} vB", lh.vsize(), LEVELS - 1, top.vsize());
    rt.mine(u64::from(w - delta)).unwrap();
    let s1 = two_of_two(&z1, &p_tree, p_op, &p_out, "split_UserWins", vec![], pay(&z1, &p_out, Role::User));
    rt.mine_with(std::slice::from_ref(&s1)).unwrap_or_else(|e| panic!("Z1: the prover's split: {e:#}"));
    println!("V25Z Z1 the prover's split after w: {} vB", s1.vsize());

    // ---- Z4: a false claim at depth 1 (no prior head) ----
    let (p_op, p_out, _, _) = rebut(&rt, &mut z4, z4d, &o4, 1, &venue, &tree, &roots[1]);
    let p_tree = z4.p_tree(z4d, &o4.window[1].clone());
    rt.mine(u64::from(w)).unwrap();
    let s4 = two_of_two(&z4, &p_tree, p_op, &p_out, "split_UserWins", vec![], pay(&z4, &p_out, Role::User));
    rt.mine_with(std::slice::from_ref(&s4)).unwrap_or_else(|e| panic!("Z4: the prover's split at depth 1: {e:#}"));
    println!("V25Z Z4 depth 1 rebutted, the prover's split: {} vB", s4.vsize());

    // ---- Z2: the final step; the prover proves after w ----
    let (p_op, p_out, pair, _) = rebut(&rt, &mut z2, z2d, &o2, 0, &venue, &tree, &roots[0]);
    let p_tree = z2.p_tree(z2d, &o2.window[0].clone());
    let (state, record) = (last.state, last.record.unwrap());
    let proof = mover_spend(&z2, &p_tree, p_op, &p_out, &prove_name(&last), final_witness(&state, &record), &pair, Role::User);
    assert!(rt.test_accept(&proof).is_err(), "Z2: not inside the verifier's window");
    rt.mine(u64::from(w)).unwrap();
    rt.mine_with(std::slice::from_ref(&proof)).unwrap_or_else(|e| panic!("Z2: the proof: {e:#}"));
    println!("V25Z Z2 {}: {} vB", prove_name(&last), proof.vsize());

    // ---- Z3: member 0 equivocated; the ladder from 2 to the final proof ----
    let (p_op, p_out, _, _) = rebut(&rt, &mut z3, z3d, &o3, 0, &venue, &tree, &roots[0]);
    let p_tree = z3.p_tree(z3d, &o3.window[0].clone());
    let t_out = TxOut { value: p_out.value - z3.params.presign_fee, script_pubkey: z3.ladder(z3d).script_pubkey() };
    let cont = two_of_two(&z3, &p_tree, p_op, &p_out, "pair_continue", [wots_wire(&roots[0]), wots_wire(&root0_second)].concat(), vec![t_out.clone()]);
    rt.mine_with(std::slice::from_ref(&cont)).unwrap_or_else(|e| panic!("Z3: pair_continue: {e:#}"));
    println!("V25Z Z3 pair_continue: {} vB", cont.vsize());
    let mut at = (OutPoint { txid: cont.compute_txid(), vout: 0 }, t_out);
    let (mut total, mut posts, mut pair) = (0usize, 0u32, None);
    for j in z3d + 1..=m {
        let prev = z3.ladder(j - 1);
        let out = TxOut { value: at.1.value - z3.params.presign_fee, script_pubkey: z3.ladder(j).script_pubkey() };
        let (wire, pr) = z3.post_wire(j);
        let tx = two_of_two(&z3, &prev, at.0, &at.1, "post", wire, vec![out.clone()]);
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("Z3: post {j}: {e:#}"));
        if j <= z3d + 2 {
            println!("V25Z ladder post of {j} ({}): {} vB", mover_at(j).name(), tx.vsize());
        }
        total += tx.vsize();
        posts += 1;
        at = (OutPoint { txid: tx.compute_txid(), vout: 0 }, out);
        pair = Some(pr);
    }
    let fin = z3.ladder(m);
    let proof = mover_spend(&z3, &fin, at.0, &at.1, &prove_name(&last), final_witness(&state, &record), pair.as_ref().unwrap(), Role::User);
    rt.mine(u64::from(w)).unwrap();
    rt.mine_with(std::slice::from_ref(&proof)).unwrap_or_else(|e| panic!("Z3: the final proof from the ladder: {e:#}"));
    total += proof.vsize() + cont.vsize();
    println!("V25Z [{tag}] Z3 ladder: {posts} posts + the proof = {total} vB in all; worst case {} blocks at w = {w} per move", (posts + 1) * u32::from(w));
    println!("V25Z [{tag}] total {:.1?}", t0.elapsed());
}

/// hello-world in binary search: 11 rounds, 23 depths.
#[test]
fn search_dated_by_members() {
    scenarios(&pdf(), &VALID, "hello-world");
}

/// The Groth16 verifier (RISC0's, patched ELF; DEMOS_PLAN.md): 29 rounds,
/// 59 depths. Opt-in: `ZK_GROTH16_DIR` holds groth16-binary.yaml, the ELF
/// and input.hex. About ten minutes, most of it BitVMX's search.
#[test]
#[ignore]
fn groth16_dated_by_members() {
    let Ok(gdir) = std::env::var("ZK_GROTH16_DIR") else { panic!("set ZK_GROTH16_DIR") };
    let input = hex::decode(std::fs::read_to_string(format!("{gdir}/input.hex")).unwrap().trim()).unwrap();
    scenarios(&format!("{gdir}/groth16-binary.yaml"), &input, "groth16");
}
