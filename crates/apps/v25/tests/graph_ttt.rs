//! V25_POC_PLAN.md Phase 4a on regtest: tic-tac-toe disputes whose moves
//! are dated by members' seal closings.
//!
//! A venue of two members (seal chains from `lngap-seal`, four slots per
//! period) dates the hub's move at depth 2 of four contracts, one per
//! slot. Each contract plays one path from its funded output:
//!
//! - S2, a false claim: the hub moved legally and in time; the user claims
//!   absence anyway; the hub rebuts through member 0 (unfolding its
//!   connector leaf), no disprove fires, and the hub's checked split pays
//!   R(state) = HubWins after `delta + delta'`;
//! - S4, an illegal move dated: the hub played onto the user's cell; it can
//!   still rebut (the move was dated), and the user's `cell_occupied`
//!   disprove takes the pot;
//! - S3, a substituted move (the option attack): a colluding member dated
//!   a move A the hub never signed; the hub later signs B and rebuts with
//!   B's heads and A's path; the rebuttal's own checks pass (the path's
//!   top is the root), and the user's `leaf_hash` disprove takes the pot
//!   (here the substitution loses; it would win only if B were the dated
//!   leaf, i.e. if the member had dated B in time);
//! - S1, a stall: the hub never moved; no member dated anything for this
//!   contract; the user's absence claim and timeout split pay UserWins.
//!
//! Run with `--test-threads=1` or 2.

use bitcoin::key::Keypair;
use bitcoin::{absolute, Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::{build_spend, build_tx};
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, Role};
use lngap_contract::{Contract, Outcome};
use lngap_factchain::slot::SlotEntry;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_pos::instance::{self, PosDepthKeys};
use lngap_pos::rebut::{wots_wire, wots_wire_tied};
use lngap_pos::ttt::{self, Layout};
use lngap_seal::dating::{Choice, PeriodTree, PAD_LEAF};
use lngap_seal::{ceremony, first_tree, Member, PresignedChain, SealSpec};
use lngap_tictactoe::{Board, TicTacToe};
use lngap_v25::{claim_tree, path_message, path_params, rebuttal_tree, WindowMember};

const GAME_ID: u16 = 1;
const D: u32 = 2;
const LEVELS: usize = 2; // Q = 4 slots per period
const SEQ: u64 = 1;

// ---------------------------------------------------------------- venue

fn seal_spec(start: u32) -> SealSpec {
    SealSpec {
        value: Amount::from_sat(300_000),
        start,
        period: 4,
        periods: 3,
        grace: 2,
        release_delay: 5,
        fanout_depth: LEVELS as u32,
        leaf_value: Amount::from_sat(330),
        split_fee: Amount::from_sat(400),
        anchor_value: Amount::from_sat(240),
        closing_fee: Amount::from_sat(3_000),
    }
}

struct VenueMember {
    member: Member,
    chain: PresignedChain,
}

/// `n` members; member i's period 1 closes at `base + i`.
fn venue(rt: &Regtest, base: u32, n: u8) -> Vec<VenueMember> {
    (0..n)
        .map(|i| {
            let spec = seal_spec(base + u32::from(i));
            let member = Member::new([0x70 + i; 32], &spec);
            let seed = [0xC7 + i; 32];
            let tree = first_tree(&spec, &member.public(), &seed).unwrap();
            let (op, _) = rt.fund(&tree.script_pubkey(), spec.value).unwrap();
            let chain = ceremony(&spec, &member.public(), op, &seed).unwrap();
            VenueMember { member, chain }
        })
        .collect()
}

// ------------------------------------------------------------- contract

fn state_u32(b: &Board) -> u32 {
    lngap_lamport::bits_to_uint(&TicTacToe.state_bits(b))
}

/// One tic-tac-toe contract between the user and the hub.
struct Game {
    id: u32,
    user: PartyKeys,
    hub: PartyKeys,
    user_ks: KeyStore,
    hub_ks: KeyStore,
    params: ChannelParams,
    pubs: [PartyPubKeys; 2],
    keys: Vec<PosDepthKeys>,
    path_key: WotsPublic,
    outcomes: Vec<Outcome>,
}

impl Game {
    fn new(id: u32) -> Game {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("v25/{id}/user")));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("v25/{id}/hub")));
        let mut user_ks = KeyStore::new(Seed::from_label(&format!("v25/{id}/user-ks")));
        let mut hub_ks = KeyStore::new(Seed::from_label(&format!("v25/{id}/hub-ks")));
        let ou = instance::gen_pos_keys(&mut user_ks, Role::User, id, SEQ, D, instance::Game::Ttt).unwrap();
        let oh = instance::gen_pos_keys(&mut hub_ks, Role::Hub, id, SEQ, D, instance::Game::Ttt).unwrap();
        let keys = instance::collect_keys(&ou, &oh, D).unwrap();
        // the mover's path key for depth 2 (the hub moves at even depths)
        assert_eq!(instance::mover_at(D), Role::Hub);
        let path_key = hub_ks.generate_wots(&path_label(id), lngap_v25::path_bytes(LEVELS)).unwrap();
        assert_eq!(path_key.params, path_params(LEVELS));
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
        let pubs = [user.public(), hub.public()];
        Game { id, user, hub, user_ks, hub_ks, params, pubs, keys, path_key, outcomes: Contract::outcomes(&TicTacToe) }
    }
    /// Broadcaster: the hub, so the user's claim needs no to_self_delay.
    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::Hub, seq: SEQ, rev_hash: [0u8; 20] }
    }
    fn layout(&self) -> Layout {
        Layout::at(D, GAME_ID, instance::mover_at(D))
    }
    fn ks(&mut self, r: Role) -> &mut KeyStore {
        match r {
            Role::User => &mut self.user_ks,
            Role::Hub => &mut self.hub_ks,
        }
    }
    /// The entry head of `d`'s move from `board`, signed by the mover's
    /// state key over the claimed state (v1's D41/D43 authorship). An
    /// illegal move claims the naive overwrite.
    fn play(&mut self, d: u32, board: &Board, mv: u8) -> (Board, [u8; 48]) {
        let mover = instance::mover_at(d);
        let new = TicTacToe.transition(board, &mv, mover).unwrap_or_else(|_| {
            let mut n = board.clone();
            n.cells[mv as usize] = if mover == Role::User { 1 } else { 2 };
            n.turn = mover.other();
            n
        });
        let id = self.id;
        let sig = self.ks(mover).sign_wots(&instance::state_label(id, SEQ, d), &state_u32(&new).to_be_bytes()[1..]).unwrap();
        let entry = SlotEntry { game_id: GAME_ID, depth: d as u8, mover: mover.idx() as u8, mv, state: state_u32(&new), sigs: sig.hashes.clone() };
        (new, lngap_pos::entry_header(d, &entry.encode()).head())
    }
}

fn path_label(id: u32) -> String {
    format!("v25/path/{id}/{D}")
}

fn sig(kp: &Keypair, tx: &Transaction, input: usize, prevouts: &[TxOut], leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, input, prevouts, leaf).unwrap().as_ref().to_vec()
}

/// The contract's funded output and its pre-signed skeletons.
struct Open {
    a_tree: TapTree,
    claim: Transaction,
    a_out: TxOut,
    window: Vec<WindowMember>,
}

/// Build the contract output (one leaf: `absent_2` after `lock`), fund it,
/// and the absence claim's skeleton.
fn open(rt: &Regtest, g: &Game, window: Vec<WindowMember>, lock: u32) -> Open {
    let ctx = g.ctx();
    let l = g.layout();
    let (kp, kn) = (&g.keys[0], &g.keys[1]);
    let a_tree = claim_tree(&ctx, &l, kn, kp, &window, &g.path_key, LEVELS, &g.outcomes).unwrap();
    let absent = lngap_pos::graph::absent_leaf(&ctx, "absent_2", Role::User, lock);
    let c_tree = TapTree::new(vec![absent]).unwrap();
    let value = Amount::from_sat(100_000);
    let (c_op, c_out) = rt.fund(&c_tree.script_pubkey(), value).unwrap();
    let a_out = TxOut { value: value - g.params.presign_fee, script_pubkey: a_tree.script_pubkey() };
    let leaf = c_tree.leaf("absent_2").unwrap();
    let mut claim = build_spend(c_op, &leaf.timelock, vec![a_out.clone()]);
    let w = vec![
        sig(&g.hub.payment, &claim, 0, std::slice::from_ref(&c_out), &leaf.script),
        sig(&g.user.payment, &claim, 0, std::slice::from_ref(&c_out), &leaf.script),
    ];
    claim.input[0].witness = tapscript_witness(&w, &leaf.script, &c_tree.control_block("absent_2").unwrap());
    Open { a_tree, claim, a_out, window }
}

/// A member's window entry for slot `s` of its period 1.
fn window_member(m: usize, v: &VenueMember, s: u32) -> WindowMember {
    let pubm = &v.chain.member;
    WindowMember {
        member: m,
        period: 1,
        slot: s,
        root_key: pubm.roots[0].clone(),
        empty_hash: pubm.empties[0],
        leaf: v.chain.leaf_connector(1, s).unwrap(),
    }
}

/// Broadcast every not-yet-confirmed transaction of `txs`, in one block.
fn mine_missing(rt: &Regtest, txs: &[Transaction]) {
    let missing: Vec<Transaction> = txs.iter().filter(|t| rt.confirmations(&t.compute_txid()).ok().flatten().is_none()).cloned().collect();
    if !missing.is_empty() {
        rt.mine_with(&missing).unwrap_or_else(|e| panic!("unfolding must mine: {e:#}"));
    }
}

/// The hub's rebuttal through window member `wm` (index into the window):
/// unfold the member's connector path, then spend `A_2` and the leaf.
#[allow(clippy::too_many_arguments)]
fn rebut(rt: &Regtest, g: &mut Game, o: &Open, wm: usize, venue: &[VenueMember], heads: (&[u8; 48], &[u8; 48]), tree: &PeriodTree, root_sig: &WotsSig) -> (OutPoint, TxOut, WotsSig, WotsSig, Transaction) {
    let path = path_of(tree, o.window[wm].slot);
    rebut_with(rt, g, o, wm, venue, heads, path, root_sig, true)
}

/// As [`rebut`], with the asserted path given explicitly; `mine` false
/// returns the transaction without broadcasting it.
#[allow(clippy::too_many_arguments)]
fn rebut_with(rt: &Regtest, g: &mut Game, o: &Open, wm: usize, venue: &[VenueMember], heads: (&[u8; 48], &[u8; 48]), path: (Vec<[u8; 20]>, Vec<[u8; 20]>), root_sig: &WotsSig, mine: bool) -> (OutPoint, TxOut, WotsSig, WotsSig, Transaction) {
    let ctx_l = g.layout();
    let w = o.window[wm].clone();
    let vm = &venue[w.member];
    if mine {
        mine_missing(rt, &vm.chain.connector_path(w.period, w.slot).unwrap());
    }
    let ctx = g.ctx();
    let p_tree = rebuttal_tree(&ctx, &ctx_l, &g.keys[1], &w, &g.path_key, LEVELS, g.id, &g.outcomes).unwrap();
    let a_op = OutPoint { txid: o.claim.compute_txid(), vout: 0 };
    let p_out = TxOut { value: o.a_out.value + w.leaf.1.value - g.params.presign_fee, script_pubkey: p_tree.script_pubkey() };
    let mut tx = build_tx(
        &[(a_op, Sequence::ENABLE_RBF_NO_LOCKTIME), (w.leaf.0, Sequence::ENABLE_RBF_NO_LOCKTIME)],
        vec![p_out.clone()],
        absolute::LockTime::ZERO,
    );
    let prevouts = [o.a_out.clone(), w.leaf.1.clone()];
    let name = format!("rebut_{}", w.member);
    let leaf = o.a_tree.leaf(&name).unwrap();
    // the mover's reveals
    let (prev_head, new_head) = heads;
    let mut pair_msg = prev_head.to_vec();
    pair_msg.extend_from_slice(new_head);
    let id = g.id;
    let pair = g.ks(Role::Hub).sign_wots(&instance::rebut_label(id, SEQ, D), &pair_msg).unwrap();
    let new_auth = g.ks(Role::Hub).sign_wots(&instance::state_label(id, SEQ, D), &ttt::auth_message(new_head)).unwrap();
    let prior_auth = g.ks(Role::User).sign_wots(&instance::state_label(id, SEQ, D - 1), &ttt::auth_message(prev_head)).unwrap();
    let (digests, siblings) = path;
    let path = g.ks(Role::Hub).sign_wots(&path_label(id), &path_message(&digests, &siblings)).unwrap();
    let mut wit = wots_wire(&path);
    wit.extend(wots_wire(root_sig));
    wit.extend(wots_wire_tied(&prior_auth));
    wit.extend(wots_wire_tied(&new_auth));
    wit.extend(wots_wire(&pair));
    wit.push(sig(&g.hub.payment, &tx, 0, &prevouts, &leaf.script));
    wit.push(sig(&g.user.payment, &tx, 0, &prevouts, &leaf.script));
    tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &o.a_tree.control_block(&name).unwrap());
    tx.input[1].witness = vm.chain.leaf_witness(w.period, w.slot, &vm.member.leaf_preimage(w.period, w.slot)).unwrap();
    if !mine {
        return (OutPoint { txid: tx.compute_txid(), vout: 0 }, p_out, pair, path, tx);
    }
    rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("the rebuttal through member {} must mine: {e:#}", w.member));
    println!("V25 rebuttal through member {}: {} vB", w.member, tx.vsize());
    (OutPoint { txid: tx.compute_txid(), vout: 0 }, p_out, pair, path, tx)
}

/// The path of slot `s`: digests `c_0 .. c_L` and siblings.
fn path_of(tree: &PeriodTree, s: u32) -> (Vec<[u8; 20]>, Vec<[u8; 20]>) {
    let p = tree.path(s as usize).unwrap();
    (p.digests(tree.leaves()[s as usize]), p.siblings.clone())
}

/// A claimant's disprove spend of `P` through leaf `name`, with `wire`
/// below the claimant's signature; paying the user. Dry (not broadcast).
fn claimant_spend(g: &Game, w: &WindowMember, p_op: OutPoint, p_out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
    let ctx = g.ctx();
    let p_tree = rebuttal_tree(&ctx, &g.layout(), &g.keys[1], w, &g.path_key, LEVELS, g.id, &g.outcomes).unwrap();
    let leaf = p_tree.leaf(name).unwrap();
    let mut tx = build_spend(p_op, &leaf.timelock, vec![TxOut { value: p_out.value - g.params.presign_fee, script_pubkey: g.pubs[0].payout_spk.clone() }]);
    let mut wit = wire;
    wit.push(sig(&g.user.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script));
    tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &p_tree.control_block(name).unwrap());
    tx
}

/// The hub's checked split of `P` by outcome `code`, after `delta + delta'`.
fn checked_split(g: &mut Game, w: &WindowMember, p_op: OutPoint, p_out: &TxOut, code: u8, pair: &WotsSig) -> Transaction {
    let ctx = g.ctx();
    let p_tree = rebuttal_tree(&ctx, &g.layout(), &g.keys[1], w, &g.path_key, LEVELS, g.id, &g.outcomes).unwrap();
    let o = g.outcomes.iter().find(|o| o.code == code).unwrap().clone();
    let name = format!("split_{}", o.name);
    let leaf = p_tree.leaf(&name).unwrap();
    let [u, h] = o.payout.dist(p_out.value - g.params.presign_fee);
    let mut outs = Vec::new();
    if u > Amount::ZERO {
        outs.push(TxOut { value: u, script_pubkey: g.pubs[0].payout_spk.clone() });
    }
    if h > Amount::ZERO {
        outs.push(TxOut { value: h, script_pubkey: g.pubs[1].payout_spk.clone() });
    }
    let mut tx = build_spend(p_op, &leaf.timelock, outs);
    let id = g.id;
    let reveal = g.ks(Role::Hub).reveal_uint(&instance::code_label(id, SEQ, D), u32::from(code)).unwrap();
    let su = sig(&g.user.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script);
    let sh = sig(&g.hub.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script);
    tx.input[0].witness = tapscript_witness(&ttt::checked_split_witness(su, sh, &reveal, pair), &leaf.script, &p_tree.control_block(&name).unwrap());
    tx
}

/// The user's timeout split off `A_2` (UserWins) after `delta`.
fn timeout_split(g: &mut Game, o: &Open) -> Transaction {
    let o_win = g.outcomes.iter().find(|x| x.code == 0).unwrap().clone();
    let name = format!("split_{}", o_win.name);
    let leaf = o.a_tree.leaf(&name).unwrap();
    let a_op = OutPoint { txid: o.claim.compute_txid(), vout: 0 };
    let mut tx = build_spend(a_op, &leaf.timelock, vec![TxOut { value: o.a_out.value - g.params.presign_fee, script_pubkey: g.pubs[0].payout_spk.clone() }]);
    let id = g.id;
    let reveal = g.ks(Role::User).reveal_uint(&instance::ccode_label(id, SEQ, D), 0).unwrap();
    let mut w = reveal.consumption_order();
    w.reverse();
    w.push(sig(&g.hub.payment, &tx, 0, std::slice::from_ref(&o.a_out), &leaf.script));
    w.push(sig(&g.user.payment, &tx, 0, std::slice::from_ref(&o.a_out), &leaf.script));
    tx.input[0].witness = tapscript_witness(&w, &leaf.script, &o.a_tree.control_block(&name).unwrap());
    tx
}

fn leaf_of(id: u32, head: &[u8; 48]) -> [u8; 20] {
    Choice { contract: id, depth: D as u16, value: lngap_v25::ttt_choice(head) }.leaf()
}

#[test]
fn ttt_disputes_dated_by_members() {
    let rt = Regtest::start().unwrap();
    let base = rt.height().unwrap() + 12;
    let venue = venue(&rt, base, 2);
    // four contracts, slot s = contract index
    let mut games: Vec<Game> = (1..=4).map(Game::new).collect();

    // depth 1: the user's opening (centre) in every game; depth 2: the
    // hub's move, per game
    let mut heads = Vec::new(); // (prev head, dated head, board after depth 1)
    for g in games.iter_mut() {
        let (b1, h1) = g.play(1, &Board::empty(), 4);
        heads.push((h1, b1));
    }
    let (_, h2_ok) = games[0].play(2, &heads[0].1, 0); // S2: legal
    let (_, h2_bad) = games[1].play(2, &heads[1].1, 4); // S4: onto the user's centre
    // S3: a colluding member dates move A, which the hub never signs (the
    // option attack): the leaf is computed from A's state alone
    let board_a = TicTacToe.transition(&heads[2].1, &0, Role::Hub).unwrap();
    let leaf_a = Choice { contract: 3, depth: D as u16, value: state_u32(&board_a).to_be_bytes()[1..].to_vec() }.leaf();
    // S1: game 4's hub never moves
    // the members' period-1 trees: slot s holds game s+1's leaf (or PAD)
    let mut leaves = vec![PAD_LEAF; 4];
    leaves[0] = leaf_of(1, &h2_ok);
    leaves[1] = leaf_of(2, &h2_bad);
    leaves[2] = leaf_a;
    let tree = PeriodTree::new(leaves);
    assert_eq!(tree.depth(), LEVELS);
    let root = tree.root();
    let root_sigs: Vec<WotsSig> = venue.iter().map(|v| v.member.sign_root(1, &root).unwrap()).collect();

    // both members close period 1 with that root
    for (i, v) in venue.iter().enumerate() {
        rt.mine_to_height(v.chain.spec.height(1) - 1).unwrap();
        let tx = v.chain.close(&v.member, 1, &root).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("member {i}'s closing: {e:#}"));
    }
    let deadline = base + 1;
    let lock = deadline + 2;

    // each contract's output, with its window: both members, slot = index
    let opens: Vec<Open> = games
        .iter()
        .enumerate()
        .map(|(s, g)| {
            let window = venue.iter().enumerate().map(|(m, v)| window_member(m, v, s as u32)).collect();
            open(&rt, g, window, lock)
        })
        .collect();
    // the claims (the user claims absence in all four)
    rt.mine_to_height(lock).unwrap();
    for (i, o) in opens.iter().enumerate() {
        rt.mine_with(std::slice::from_ref(&o.claim)).unwrap_or_else(|e| panic!("claim {}: {e:#}", i + 1));
    }
    println!("V25 absence claim: {} vB", opens[0].claim.vsize());

    // ---- S2: a false claim, defeated; the checked split pays HubWins ----
    let (p_op, p_out, pair, path, _) = rebut(&rt, &mut games[0], &opens[0], 0, &venue, (&heads[0].0, &h2_ok), &tree, &root_sigs[0]);
    let w0 = opens[0].window[0].clone();
    // no disprove fires: leaf_hash and the node checks hold for an honest path
    rt.mine(u64::from(games[0].params.delta)).unwrap();
    let lh = claimant_spend(&games[0], &w0, p_op, &p_out, "leaf_hash", [wots_wire(&pair), wots_wire(&path)].concat());
    assert!(rt.mine_with(std::slice::from_ref(&lh)).is_err(), "an honest leaf digest does not fire leaf_hash");
    let n0 = claimant_spend(&games[0], &w0, p_op, &p_out, "node_0", wots_wire(&path));
    assert!(rt.mine_with(std::slice::from_ref(&n0)).is_err(), "an honest path does not fire node_0");
    rt.mine(u64::from(games[0].params.delta_prime)).unwrap();
    let split = checked_split(&mut games[0], &w0, p_op, &p_out, 1, &pair);
    rt.mine_with(std::slice::from_ref(&split)).unwrap_or_else(|e| panic!("S2: the hub's checked split must mine: {e:#}"));
    println!("V25 S2 checked split (HubWins): {} vB; leaf_hash leaf {} vB dry, node_0 {} vB dry", split.vsize(), lh.vsize(), n0.vsize());

    // ---- S4: an illegal move, dated; cell_occupied_4 fires ----
    let (p_op, p_out, pair, _, _) = rebut(&rt, &mut games[1], &opens[1], 1, &venue, (&heads[1].0, &h2_bad), &tree, &root_sigs[1]);
    let w1 = opens[1].window[1].clone();
    rt.mine(u64::from(games[1].params.delta)).unwrap();
    let dis = claimant_spend(&games[1], &w1, p_op, &p_out, "disprove_cell_occupied_4", wots_wire(&pair));
    rt.mine_with(std::slice::from_ref(&dis)).unwrap_or_else(|e| panic!("S4: cell_occupied_4 must fire: {e:#}"));
    println!("V25 S4 disprove cell_occupied_4: {} vB", dis.vsize());

    // ---- S3: a substituted move; leaf_hash fires ----
    let (_, h2_b) = games[2].play(2, &heads[2].1, 8); // B: the move the hub signs, later
    let (p_op, p_out, pair, path, _) = rebut(&rt, &mut games[2], &opens[2], 0, &venue, (&heads[2].0, &h2_b), &tree, &root_sigs[0]);
    let w2 = opens[2].window[0].clone();
    rt.mine(u64::from(games[2].params.delta)).unwrap();
    let lh = claimant_spend(&games[2], &w2, p_op, &p_out, "leaf_hash", [wots_wire(&pair), wots_wire(&path)].concat());
    rt.mine_with(std::slice::from_ref(&lh)).unwrap_or_else(|e| panic!("S3: leaf_hash must fire on a substituted move: {e:#}"));
    println!("V25 S3 leaf_hash disprove: {} vB", lh.vsize());

    // ---- S1: a stall; the timeout split pays UserWins ----
    rt.mine(u64::from(games[3].params.delta)).unwrap();
    let ts = timeout_split(&mut games[3], &opens[3]);
    rt.mine_with(std::slice::from_ref(&ts)).unwrap_or_else(|e| panic!("S1: the timeout split must mine: {e:#}"));
    println!("V25 S1 timeout split (UserWins): {} vB", ts.vsize());
}

/// Member faults. Three members; each game's window is the members named.
///
/// - S5, a skipped closing: member 0 never closes period 1 (its bond is
///   burned); a rebuttal through member 0 can never be valid (its connector
///   leaf does not exist), and the rebuttal through member 1 mines;
/// - S9, a late root: member 1's on-chain root lacks game 2's move (the hub
///   was late); member 1 signs a second root that has it, the hub rebuts
///   through member 1 with it (the connector exists: member 1 did close),
///   and the user's `pair_kill`, with the on-chain root, takes the pot;
/// - an empty closing: member 2 closed period 1 empty; a late root through
///   member 2 is killed by `empty_kill` with the revealed preimage;
/// - a malformed path: the hub asserts game 4's path with a wrong level-1
///   sibling (its top still the root); `node_1` fires.
#[test]
fn member_faults() {
    let rt = Regtest::start().unwrap();
    let base = rt.height().unwrap() + 12;
    let venue = venue(&rt, base, 3);
    let mut games: Vec<Game> = (11..=14).map(Game::new).collect();
    let mut prior = Vec::new();
    for g in games.iter_mut() {
        let (b1, h1) = g.play(1, &Board::empty(), 4);
        prior.push((h1, b1));
    }
    let (_, h_g1) = games[0].play(2, &prior[0].1, 0);
    let (_, h_g2) = games[1].play(2, &prior[1].1, 0); // sent too late for member 1
    let (_, h_g3) = games[2].play(2, &prior[2].1, 0); // sent to nobody in time
    let (_, h_g4) = games[3].play(2, &prior[3].1, 0);
    // member 1's period-1 tree: game 11 at slot 0, game 14 at slot 3
    let mut leaves = vec![PAD_LEAF; 4];
    leaves[0] = leaf_of(11, &h_g1);
    leaves[3] = leaf_of(14, &h_g4);
    let tree1 = PeriodTree::new(leaves.clone());
    // member 1's late, second root: game 12's move added at slot 1
    leaves[1] = leaf_of(12, &h_g2);
    let late1 = PeriodTree::new(leaves);
    // member 2's late root (it closed empty): game 13 at slot 2
    let mut l2 = vec![PAD_LEAF; 4];
    l2[2] = leaf_of(13, &h_g3);
    let late2 = PeriodTree::new(l2);

    // closings: member 0 skips; member 1 with tree1's root; member 2 empty
    let (m1, m2) = (&venue[1], &venue[2]);
    rt.mine_to_height(m1.chain.spec.height(1) - 1).unwrap();
    rt.mine_with(&[m1.chain.close(&m1.member, 1, &tree1.root()).unwrap()]).unwrap();
    rt.mine_with(&[m2.chain.close_empty(&m2.member, 1).unwrap()]).unwrap();
    let root1 = m1.member.sign_root(1, &tree1.root()).unwrap();
    let root1_late = m1.member.sign_root(1, &late1.root()).unwrap();
    let root2_late = m2.member.sign_root(1, &late2.root()).unwrap();
    // member 0's bond is burnable after its grace
    let m0 = &venue[0];
    rt.mine_to_height(m0.chain.spec.burn_from(1) - 1).unwrap();
    rt.send_raw_any_fee(&m0.chain.burn(1).unwrap()).unwrap();
    rt.mine(1).unwrap();

    let lock = base + 4;
    let wm = |m: usize, s: u32| window_member(m, &venue[m], s);
    let opens = [
        open(&rt, &games[0], vec![wm(0, 0), wm(1, 0)], lock),
        open(&rt, &games[1], vec![wm(1, 1)], lock),
        open(&rt, &games[2], vec![wm(2, 2)], lock),
        open(&rt, &games[3], vec![wm(1, 3)], lock),
    ];
    rt.mine_to_height(lock).unwrap();
    for o in &opens {
        rt.mine_with(std::slice::from_ref(&o.claim)).unwrap();
    }

    // ---- S5: no rebuttal through the member that skipped ----
    let (_, _, _, _, through_m0) = rebut_with(&rt, &mut games[0], &opens[0], 0, &venue, (&prior[0].0, &h_g1), path_of(&tree1, 0), &root1, false);
    assert!(rt.mine_with(std::slice::from_ref(&through_m0)).is_err(), "S5: member 0's connector leaf never existed");
    assert!(rt.mine_with(&[venue[0].chain.connector_path(1, 0).unwrap()[0].clone()]).is_err(), "S5: member 0 has no connector to unfold");
    let _ = rebut(&rt, &mut games[0], &opens[0], 1, &venue, (&prior[0].0, &h_g1), &tree1, &root1);
    println!("V25 S5: the rebuttal through member 1 mined; through member 0 it cannot");

    // ---- S9: a late root through member 1; pair_kill with the on-chain root ----
    let (p_op, p_out, _, _, _) = rebut(&rt, &mut games[1], &opens[1], 0, &venue, (&prior[1].0, &h_g2), &late1, &root1_late);
    let w = opens[1].window[0].clone();
    rt.mine(u64::from(games[1].params.delta)).unwrap();
    let kill = claimant_spend(&games[1], &w, p_op, &p_out, "pair_kill", [wots_wire(&root1), wots_wire(&root1_late)].concat());
    rt.mine_with(std::slice::from_ref(&kill)).unwrap_or_else(|e| panic!("S9: pair_kill must fire: {e:#}"));
    println!("V25 S9 pair_kill: {} vB", kill.vsize());

    // ---- empty closing: a late root through member 2; empty_kill ----
    let (p_op, p_out, _, _, _) = rebut(&rt, &mut games[2], &opens[2], 0, &venue, (&prior[2].0, &h_g3), &late2, &root2_late);
    let w = opens[2].window[0].clone();
    rt.mine(u64::from(games[2].params.delta)).unwrap();
    let z = venue[2].member.empty_preimage(1).to_vec();
    let kill = claimant_spend(&games[2], &w, p_op, &p_out, "empty_kill", vec![z]);
    rt.mine_with(std::slice::from_ref(&kill)).unwrap_or_else(|e| panic!("empty_kill must fire: {e:#}"));
    println!("V25 empty_kill: {} vB", kill.vsize());

    // ---- a malformed path: a wrong level-1 sibling; node_1 fires ----
    let (digests, mut siblings) = path_of(&tree1, 3);
    siblings[1] = [0x55; 20];
    let (p_op, p_out, _, path, _) = rebut_with(&rt, &mut games[3], &opens[3], 0, &venue, (&prior[3].0, &h_g4), (digests, siblings), &root1, true);
    let w = opens[3].window[0].clone();
    rt.mine(u64::from(games[3].params.delta)).unwrap();
    let n0 = claimant_spend(&games[3], &w, p_op, &p_out, "node_0", wots_wire(&path));
    assert!(rt.mine_with(std::slice::from_ref(&n0)).is_err(), "level 0 is honest: node_0 does not fire");
    let n1 = claimant_spend(&games[3], &w, p_op, &p_out, "node_1", wots_wire(&path));
    rt.mine_with(std::slice::from_ref(&n1)).unwrap_or_else(|e| panic!("node_1 must fire on a wrong sibling: {e:#}"));
    println!("V25 node_1 disprove: {} vB", n1.vsize());
}
