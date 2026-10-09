//! Shared regtest fixture for the v2.5 tic-tac-toe graph tests.
#![allow(dead_code)]

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
use lngap_seal::dating::{Choice, PeriodTree};
use lngap_seal::{ceremony, first_tree, Member, PresignedChain, SealSpec};
use lngap_tictactoe::{Board, TicTacToe};
use lngap_v25::{carrier_tree, claim_tree, level_message, level_params, rebuttal_tree, TttDated, WindowMember, CARRIER_SAT, LEVEL_BYTES};

pub const GAME_ID: u16 = 1;
pub const D: u32 = 2;
pub const LEVELS: usize = 2; // Q = 4 slots per period
pub const SEQ: u64 = 1;

// ---------------------------------------------------------------- venue

pub fn seal_spec(start: u32) -> SealSpec {
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

pub struct VenueMember {
    pub member: Member,
    pub chain: PresignedChain,
}

/// `n` members; member i's period 1 closes at `base + i`.
pub fn venue(rt: &Regtest, base: u32, n: u8) -> Vec<VenueMember> {
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

pub fn state_u32(b: &Board) -> u32 {
    lngap_lamport::bits_to_uint(&TicTacToe.state_bits(b))
}

/// One tic-tac-toe contract between the user and the hub.
pub struct Game {
    pub id: u32,
    pub user: PartyKeys,
    pub hub: PartyKeys,
    pub user_ks: KeyStore,
    pub hub_ks: KeyStore,
    pub params: ChannelParams,
    pub pubs: [PartyPubKeys; 2],
    /// Key sets for depths 1..=max (index depth - 1).
    pub keys: Vec<PosDepthKeys>,
    /// The mover's level keys for depth `D`, one per path level.
    pub level_keys: Vec<WotsPublic>,
    pub outcomes: Vec<Outcome>,
}

impl Game {
    pub fn new(id: u32) -> Game {
        Game::with_depth(id, D)
    }
    /// A game whose key sets cover depths 1..=max_depth.
    pub fn with_depth(id: u32, max_depth: u32) -> Game {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("v25/{id}/user")));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("v25/{id}/hub")));
        let mut user_ks = KeyStore::new(Seed::from_label(&format!("v25/{id}/user-ks")));
        let mut hub_ks = KeyStore::new(Seed::from_label(&format!("v25/{id}/hub-ks")));
        let ou = instance::gen_pos_keys(&mut user_ks, Role::User, id, SEQ, max_depth, instance::Game::Ttt).unwrap();
        let oh = instance::gen_pos_keys(&mut hub_ks, Role::Hub, id, SEQ, max_depth, instance::Game::Ttt).unwrap();
        let keys = instance::collect_keys(&ou, &oh, max_depth).unwrap();
        // the mover's level keys for depth 2 (the hub moves at even depths)
        assert_eq!(instance::mover_at(D), Role::Hub);
        let level_keys: Vec<WotsPublic> = (0..LEVELS).map(|ell| hub_ks.generate_wots(&level_label(id, ell), LEVEL_BYTES).unwrap()).collect();
        assert_eq!(level_keys[0].params, level_params());
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
        let pubs = [user.public(), hub.public()];
        Game { id, user, hub, user_ks, hub_ks, params, pubs, keys, level_keys, outcomes: Contract::outcomes(&TicTacToe) }
    }
    /// Broadcaster: the hub, so the user's claim needs no to_self_delay.
    pub fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::Hub, seq: SEQ, rev_hash: [0u8; 20] }
    }
    pub fn layout(&self) -> Layout {
        Layout::at(D, GAME_ID, instance::mover_at(D))
    }
    pub fn ks(&mut self, r: Role) -> &mut KeyStore {
        match r {
            Role::User => &mut self.user_ks,
            Role::Hub => &mut self.hub_ks,
        }
    }
    /// The entry head of `d`'s move from `board`, signed by the mover's
    /// state key over the claimed state (v1's D41/D43 authorship). An
    /// illegal move claims the naive overwrite.
    pub fn play(&mut self, d: u32, board: &Board, mv: u8) -> (Board, [u8; 48]) {
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

pub fn level_label(id: u32, ell: usize) -> String {
    format!("v25/level/{id}/{D}/{ell}")
}

pub fn sig(kp: &Keypair, tx: &Transaction, input: usize, prevouts: &[TxOut], leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, input, prevouts, leaf).unwrap().as_ref().to_vec()
}

/// The contract's funded output and its pre-signed skeletons.
pub struct Open {
    pub a_tree: TapTree,
    pub claim: Transaction,
    pub a_out: TxOut,
    pub window: Vec<WindowMember>,
    /// The contract output (for a self-post).
    pub c_tree: TapTree,
    pub c_op: OutPoint,
    pub c_out: TxOut,
    /// The claim's carrier outputs, one per path level, and their trees.
    pub carriers: Vec<(OutPoint, TxOut, TapTree)>,
}

/// Build the contract output (one leaf: `absent_2` after `lock`), fund it,
/// and the absence claim's skeleton.
pub fn open(rt: &Regtest, g: &Game, window: Vec<WindowMember>, lock: u32) -> Open {
    let ctx = g.ctx();
    let l = g.layout();
    let (kp, kn) = (&g.keys[0], &g.keys[1]);
    let a_tree = claim_tree(&TttDated, &ctx, &l, kn, Some(kp), g.keys.get(D as usize), &window, &g.outcomes).unwrap();
    let absent = lngap_pos::graph::absent_leaf(&ctx, "absent_2", Role::User, lock);
    let escalate = lngap_v25::escalate_leaf(&TttDated, &ctx, &Layout::at(1, GAME_ID, instance::mover_at(1)), &g.keys[0]);
    let c_tree = TapTree::new(vec![absent, escalate]).unwrap();
    let value = Amount::from_sat(100_000);
    let (c_op, c_out) = rt.fund(&c_tree.script_pubkey(), value).unwrap();
    let trees: Vec<TapTree> = g.level_keys.iter().map(|k| carrier_tree(&ctx, Role::Hub, k).unwrap()).collect();
    let carry = Amount::from_sat(CARRIER_SAT);
    let a_out = TxOut { value: value - g.params.presign_fee - carry * trees.len() as u64, script_pubkey: a_tree.script_pubkey() };
    let leaf = c_tree.leaf("absent_2").unwrap();
    let mut outs = vec![a_out.clone()];
    outs.extend(trees.iter().map(|t| TxOut { value: carry, script_pubkey: t.script_pubkey() }));
    let mut claim = build_spend(c_op, &leaf.timelock, outs);
    let w = vec![
        sig(&g.hub.payment, &claim, 0, std::slice::from_ref(&c_out), &leaf.script),
        sig(&g.user.payment, &claim, 0, std::slice::from_ref(&c_out), &leaf.script),
    ];
    claim.input[0].witness = tapscript_witness(&w, &leaf.script, &c_tree.control_block("absent_2").unwrap());
    let txid = claim.compute_txid();
    let carriers = trees.into_iter().enumerate().map(|(k, t)| (OutPoint { txid, vout: k as u32 + 1 }, claim.output[k + 1].clone(), t)).collect();
    Open { a_tree, claim, a_out, window, c_tree, c_op, c_out, carriers }
}

/// A member's window entry for slot `s` of its period 1.
pub fn window_member(m: usize, v: &VenueMember, s: u32) -> WindowMember {
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
pub fn mine_missing(rt: &Regtest, txs: &[Transaction]) {
    let missing: Vec<Transaction> = txs.iter().filter(|t| rt.confirmations(&t.compute_txid()).ok().flatten().is_none()).cloned().collect();
    if !missing.is_empty() {
        rt.mine_with(&missing).unwrap_or_else(|e| panic!("unfolding must mine: {e:#}"));
    }
}

/// The hub's rebuttal through window member `wm` (index into the window):
/// unfold the member's connector path, then spend `A_2` and the leaf.
#[allow(clippy::too_many_arguments)]
pub fn rebut(rt: &Regtest, g: &mut Game, o: &Open, wm: usize, venue: &[VenueMember], heads: (&[u8; 48], &[u8; 48]), tree: &PeriodTree, root_sig: &WotsSig) -> (OutPoint, TxOut, WotsSig, Vec<WotsSig>, Transaction) {
    let path = path_of(tree, o.window[wm].slot);
    rebut_with(rt, g, o, wm, venue, heads, path, root_sig, true)
}

/// As [`rebut`], with the asserted path given explicitly; `mine` false
/// returns the transaction without broadcasting it.
#[allow(clippy::too_many_arguments)]
pub fn rebut_with(rt: &Regtest, g: &mut Game, o: &Open, wm: usize, venue: &[VenueMember], heads: (&[u8; 48], &[u8; 48]), path: (Vec<[u8; 20]>, Vec<[u8; 20]>), root_sig: &WotsSig, mine: bool) -> (OutPoint, TxOut, WotsSig, Vec<WotsSig>, Transaction) {
    let ctx_l = g.layout();
    let w = o.window[wm].clone();
    let vm = &venue[w.member];
    if mine {
        mine_missing(rt, &vm.chain.connector_path(w.period, w.slot).unwrap());
    }
    let ctx = g.ctx();
    let p_tree = rebuttal_tree(&TttDated, &ctx, &ctx_l, &g.keys[1], &w, &g.level_keys, g.id, &g.outcomes).unwrap();
    let a_op = OutPoint { txid: o.claim.compute_txid(), vout: 0 };
    let carried: u64 = o.carriers.iter().map(|c| c.1.value.to_sat()).sum();
    let p_out = TxOut { value: o.a_out.value + w.leaf.1.value + Amount::from_sat(carried) - g.params.presign_fee, script_pubkey: p_tree.script_pubkey() };
    let mut ins = vec![(a_op, Sequence::ENABLE_RBF_NO_LOCKTIME), (w.leaf.0, Sequence::ENABLE_RBF_NO_LOCKTIME)];
    ins.extend(o.carriers.iter().map(|c| (c.0, Sequence::ENABLE_RBF_NO_LOCKTIME)));
    let mut tx = build_tx(&ins, vec![p_out.clone()], absolute::LockTime::ZERO);
    let mut prevouts = vec![o.a_out.clone(), w.leaf.1.clone()];
    prevouts.extend(o.carriers.iter().map(|c| c.1.clone()));
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
    let levels: Vec<WotsSig> = (0..LEVELS).map(|ell| g.ks(Role::Hub).sign_wots(&level_label(id, ell), &level_message(&digests[ell], &siblings[ell])).unwrap()).collect();
    let mut wit = wots_wire(root_sig);
    wit.extend(wots_wire_tied(&prior_auth));
    wit.extend(wots_wire_tied(&new_auth));
    wit.extend(wots_wire(&pair));
    wit.push(sig(&g.hub.payment, &tx, 0, &prevouts, &leaf.script));
    wit.push(sig(&g.user.payment, &tx, 0, &prevouts, &leaf.script));
    tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &o.a_tree.control_block(&name).unwrap());
    tx.input[1].witness = vm.chain.leaf_witness(w.period, w.slot, &vm.member.leaf_preimage(w.period, w.slot)).unwrap();
    for (k, (c, lv)) in o.carriers.iter().zip(&levels).enumerate() {
        let leaf = c.2.leaf("carry").unwrap();
        let mut cw = wots_wire(lv);
        cw.push(sig(&g.hub.payment, &tx, k + 2, &prevouts, &leaf.script));
        tx.input[k + 2].witness = tapscript_witness(&cw, &leaf.script, &c.2.control_block("carry").unwrap());
    }
    if !mine {
        return (OutPoint { txid: tx.compute_txid(), vout: 0 }, p_out, pair, levels, tx);
    }
    rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("the rebuttal through member {} must mine: {e:#}", w.member));
    println!("V25 rebuttal through member {}: {} vB", w.member, tx.vsize());
    (OutPoint { txid: tx.compute_txid(), vout: 0 }, p_out, pair, levels, tx)
}

/// The path of slot `s`: digests `c_0 .. c_L` and siblings.
pub fn path_of(tree: &PeriodTree, s: u32) -> (Vec<[u8; 20]>, Vec<[u8; 20]>) {
    let p = tree.path(s as usize).unwrap();
    (p.digests(tree.leaves()[s as usize]), p.siblings.clone())
}

/// A claimant's disprove spend of `P` through leaf `name`, with `wire`
/// below the claimant's signature; paying the user. Dry (not broadcast).
pub fn claimant_spend(g: &Game, w: &WindowMember, p_op: OutPoint, p_out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
    let ctx = g.ctx();
    let p_tree = rebuttal_tree(&TttDated, &ctx, &g.layout(), &g.keys[1], w, &g.level_keys, g.id, &g.outcomes).unwrap();
    let leaf = p_tree.leaf(name).unwrap();
    let mut tx = build_spend(p_op, &leaf.timelock, vec![TxOut { value: p_out.value - g.params.presign_fee, script_pubkey: g.pubs[0].payout_spk.clone() }]);
    let mut wit = wire;
    wit.push(sig(&g.user.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script));
    tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &p_tree.control_block(name).unwrap());
    tx
}

/// The claimant's bond in these tests.
pub const BOND: Amount = Amount::from_sat(20_000);

/// `stands` off `P` (2-of-2 pre-signed, after `delta + delta'`): the
/// user's bond to the hub, the rest into the ladder at depth 2. Dry.
pub fn stands_tx(g: &Game, w: &WindowMember, p_op: OutPoint, p_out: &TxOut) -> (Transaction, TxOut) {
    let ctx = g.ctx();
    let p_tree = rebuttal_tree(&TttDated, &ctx, &g.layout(), &g.keys[1], w, &g.level_keys, g.id, &g.outcomes).unwrap();
    let leaf = p_tree.leaf("stands").unwrap();
    let t_out = TxOut { value: p_out.value - g.params.presign_fee - BOND, script_pubkey: ladder(g, D).script_pubkey() };
    let bond = TxOut { value: BOND, script_pubkey: g.pubs[1].payout_spk.clone() };
    let mut tx = build_spend(p_op, &leaf.timelock, vec![t_out.clone(), bond]);
    let wit = vec![sig(&g.hub.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script), sig(&g.user.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script)];
    tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &p_tree.control_block("stands").unwrap());
    (tx, t_out)
}

/// The checked split of the ladder output at depth `j` by outcome `code`
/// (the mover of `j` proves R(state `j`) = code), after `delta + delta'`.
pub fn ladder_split(g: &mut Game, j: u32, op: OutPoint, out: &TxOut, code: u8, pair: &WotsSig) -> Transaction {
    let tree = ladder(g, j);
    let o = g.outcomes.iter().find(|o| o.code == code).unwrap().clone();
    let name = format!("split_{}", o.name);
    let leaf = tree.leaf(&name).unwrap();
    let [u, h] = o.payout.dist(out.value - g.params.presign_fee);
    let mut outs = Vec::new();
    if u > Amount::ZERO {
        outs.push(TxOut { value: u, script_pubkey: g.pubs[0].payout_spk.clone() });
    }
    if h > Amount::ZERO {
        outs.push(TxOut { value: h, script_pubkey: g.pubs[1].payout_spk.clone() });
    }
    let mut tx = build_spend(op, &leaf.timelock, outs);
    let id = g.id;
    let reveal = g.ks(instance::mover_at(j)).reveal_uint(&instance::code_label(id, SEQ, j), u32::from(code)).unwrap();
    let su = sig(&g.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script);
    let sh = sig(&g.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script);
    tx.input[0].witness = tapscript_witness(&ttt::checked_split_witness(su, sh, &reveal, pair), &leaf.script, &tree.control_block(&name).unwrap());
    tx
}


/// The user's timeout split off `A_2` (UserWins) after `delta`.
pub fn timeout_split(g: &mut Game, o: &Open) -> Transaction {
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

pub fn leaf_of(id: u32, head: &[u8; 48]) -> [u8; 20] {
    Choice { contract: id, depth: D as u16, value: lngap_v25::ttt_choice(head) }.leaf()
}


/// The ladder output at depth `j` for game `g`.
pub fn ladder(g: &Game, j: u32) -> TapTree {
    lngap_v25::ladder_tree(&TttDated, &g.ctx(), GAME_ID, j, &g.keys, &g.outcomes).unwrap()
}

/// A continuation off `P` through leaf `name` (2-of-2 pre-signed) into the
/// ladder at depth 2, with `wire` below the two signatures. Dry.
pub fn continue_tx(g: &Game, w: &WindowMember, p_op: OutPoint, p_out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> (Transaction, TxOut) {
    let ctx = g.ctx();
    let p_tree = rebuttal_tree(&TttDated, &ctx, &g.layout(), &g.keys[1], w, &g.level_keys, g.id, &g.outcomes).unwrap();
    let leaf = p_tree.leaf(name).unwrap();
    let t_out = TxOut { value: p_out.value - g.params.presign_fee, script_pubkey: ladder(g, D).script_pubkey() };
    let mut tx = build_spend(p_op, &leaf.timelock, vec![t_out.clone()]);
    let mut wit = wire;
    wit.push(sig(&g.hub.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script));
    wit.push(sig(&g.user.payment, &tx, 0, std::slice::from_ref(p_out), &leaf.script));
    tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &p_tree.control_block(name).unwrap());
    (tx, t_out)
}
