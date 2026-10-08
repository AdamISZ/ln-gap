//! V25_POC_PLAN.md Phase 4b on regtest: the on-chain continuation (the
//! ladder), the self-post, the waiver, and the self-mining residual.
//!
//! - S6, a member equivocates: member 0 dated the hub's move and later
//!   signed a second root; the user claims falsely, the hub rebuts through
//!   member 0, and the pair sends the game to the ladder, where it is
//!   played to the end on chain (the user posts 3, the hub 4, the user 5:
//!   a won game); the hub cannot answer, and the user's checked split pays
//!   R(terminal) = UserWins. No member action moved the pot: the game did;
//! - S7, every member censors: no member dates the hub's move; the hub
//!   posts it on chain itself from the contract output (racing the user's
//!   claim, which waits for the window), into the ladder; the user then
//!   stalls at 3, and the hub's checked split pays R = HubWins;
//! - S8, the waiver: the hub's move went undated, but the user replied to
//!   it (signed its move at 3); the user claims absence at 2, and the hub
//!   answers with the user's own signature: the claim pays the hub;
//! - S10, the self-mining residual: member 2 closes its period AFTER its
//!   grace (a block the harness mines, as a member with hashpower could),
//!   with the hub's late move in its root; the connector exists and no pair
//!   arises, so the hub's rebuttal stands; since Phase 7 that costs the
//!   user only its bond and the game continues on the ladder: the late
//!   move was rescued, but no stake moved. Documented, not prevented.
//!
//! Run with `--test-threads=1` or 2.

mod common;

use bitcoin::{OutPoint, TxOut};
use common::*;
use lngap_btc::regtest::Regtest;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::Role;
use lngap_contract::Contract;
use lngap_lamport::winternitz::WotsSig;
use lngap_pos::instance;
use lngap_pos::rebut::{wots_wire, wots_wire_tied};
use lngap_pos::ttt;
use lngap_seal::dating::{PeriodTree, PAD_LEAF};
use lngap_tictactoe::{Board, TicTacToe};

/// Heads (and boards) of a game played so far: `heads[d]` is depth `d`'s.
struct Play {
    heads: Vec<[u8; 48]>,
    board: Board,
}

impl Play {
    fn new() -> Play {
        Play { heads: vec![[0u8; 48]], board: Board::empty() }
    }
    fn mv(&mut self, g: &mut Game, mv: u8) {
        let d = self.heads.len() as u32;
        let (b, h) = g.play(d, &self.board, mv);
        self.board = b;
        self.heads.push(h);
    }
}

/// The mover of depth `j` posts move `j` into the ladder: from `(op, out)`
/// (the ladder output at `j - 1`, through its `post` leaf; or the contract
/// output, through `self_post_2`, when `from_contract`). Returns the new
/// ladder output and the pair reveal.
fn post(rt: &Regtest, g: &mut Game, p: &Play, j: u32, op: OutPoint, out: &TxOut, from_contract: Option<&Open>) -> (OutPoint, TxOut, WotsSig) {
    let (tree, name) = match from_contract {
        Some(o) => (o.c_tree.clone(), "self_post_2".to_string()),
        None => (ladder(g, j - 1), "post".to_string()),
    };
    let leaf = tree.leaf(&name).unwrap();
    let t_out = TxOut { value: out.value - g.params.presign_fee, script_pubkey: ladder(g, j).script_pubkey() };
    let mut tx = build_spend(op, &leaf.timelock, vec![t_out.clone()]);
    let (mover, prior_mover) = (instance::mover_at(j), instance::mover_at(j - 1));
    let id = g.id;
    let (prev_head, new_head) = (p.heads[(j - 1) as usize], p.heads[j as usize]);
    let mut msg = prev_head.to_vec();
    msg.extend_from_slice(&new_head);
    let pair = g.ks(mover).sign_wots(&instance::rebut_label(id, SEQ, j), &msg).unwrap();
    let new_auth = g.ks(mover).sign_wots(&instance::state_label(id, SEQ, j), &ttt::auth_message(&new_head)).unwrap();
    let prior_auth = g.ks(prior_mover).sign_wots(&instance::state_label(id, SEQ, j - 1), &ttt::auth_message(&prev_head)).unwrap();
    let mut w = wots_wire_tied(&prior_auth);
    w.extend(wots_wire_tied(&new_auth));
    w.extend(wots_wire(&pair));
    w.push(sig(&g.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
    w.push(sig(&g.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
    tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(&name).unwrap());
    rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("posting move {j} must mine: {e:#}"));
    println!("V25 ladder post of move {j} ({}): {} vB", mover.name(), tx.vsize());
    (OutPoint { txid: tx.compute_txid(), vout: 0 }, t_out, pair)
}

#[test]
fn ladder_self_post_waiver_and_the_residual() {
    let rt = Regtest::start().unwrap();
    let base = rt.height().unwrap() + 12;
    let venue = venue(&rt, base, 3);
    let mut g6 = Game::with_depth(21, 9);
    let mut g7 = Game::with_depth(22, 9);
    let mut g8 = Game::with_depth(23, 9);
    let mut g10 = Game::with_depth(24, 9);
    let (mut p6, mut p7, mut p8, mut p10) = (Play::new(), Play::new(), Play::new(), Play::new());
    for (g, p) in [(&mut g6, &mut p6), (&mut g7, &mut p7), (&mut g8, &mut p8), (&mut g10, &mut p10)] {
        p.mv(g, 4); // the user's centre
        p.mv(g, 0); // the hub's corner
    }
    // member 0 dates game 21's move (slot 0) and later equivocates
    let mut l0 = vec![PAD_LEAF; 4];
    l0[0] = leaf_of(21, &p6.heads[2]);
    let tree0 = PeriodTree::new(l0.clone());
    l0[3] = [0xEE; 20];
    let second0 = PeriodTree::new(l0);
    // member 1 closes empty (it dates nothing: games 22 and 23 go undated)
    // member 2 dates game 24's move (slot 0), but closes after its grace
    let mut l2 = vec![PAD_LEAF; 4];
    l2[0] = leaf_of(24, &p10.heads[2]);
    let tree2 = PeriodTree::new(l2);

    let (m0, m1, m2) = (&venue[0], &venue[1], &venue[2]);
    rt.mine_to_height(m0.chain.spec.height(1) - 1).unwrap();
    rt.mine_with(&[m0.chain.close(&m0.member, 1, &tree0.root()).unwrap()]).unwrap();
    rt.mine_with(&[m1.chain.close_empty(&m1.member, 1).unwrap()]).unwrap();
    // member 2: late. At its burn height the closing still races the burn;
    // the harness mines the closing (a member with hashpower)
    rt.mine_to_height(m2.chain.spec.burn_from(1) - 1).unwrap();
    rt.mine_with(&[m2.chain.close(&m2.member, 1, &tree2.root()).unwrap()]).unwrap_or_else(|e| panic!("the late closing, self-mined: {e:#}"));
    let root0 = m0.member.sign_root(1, &tree0.root()).unwrap();
    let root0_second = m0.member.sign_root(1, &second0.root()).unwrap();
    let root2 = m2.member.sign_root(1, &tree2.root()).unwrap();

    let lock = rt.height().unwrap() + 3;
    let wm = |m: usize, s: u32| window_member(m, &venue[m], s);
    let o6 = open(&rt, &g6, vec![wm(0, 0)], lock);
    let o7 = open(&rt, &g7, vec![wm(1, 1)], lock);
    let o8 = open(&rt, &g8, vec![wm(1, 2)], lock);
    let o10 = open(&rt, &g10, vec![wm(2, 0)], lock);

    // ---- S7: the hub self-posts (after to_self_delay, before the window ends) ----
    rt.mine(u64::from(g7.params.to_self_delay)).unwrap();
    let (t2_op, t2_out, pair7) = post(&rt, &mut g7, &p7, 2, o7.c_op, &o7.c_out, Some(&o7));
    assert!(rt.mine_with(std::slice::from_ref(&o7.claim)).is_err(), "S7: the self-post took the contract output first");

    // the remaining claims (the user claims absence at 2 in games 21, 23, 24)
    rt.mine_to_height(lock).unwrap();
    for (i, o) in [&o6, &o8, &o10].iter().enumerate() {
        rt.mine_with(std::slice::from_ref(&o.claim)).unwrap_or_else(|e| panic!("claim {i}: {e:#}"));
    }

    // ---- S8: the waiver (the user replied at 3, then claimed) ----
    p8.mv(&mut g8, 1); // the user's reply at depth 3: signed with its state key
    {
        let leaf = o8.a_tree.leaf("waive").unwrap();
        let a_op = OutPoint { txid: o8.claim.compute_txid(), vout: 0 };
        let mut tx = build_spend(a_op, &leaf.timelock, vec![TxOut { value: o8.a_out.value - g8.params.presign_fee, script_pubkey: g8.pubs[1].payout_spk.clone() }]);
        let id = g8.id;
        let reply = g8.ks(Role::User).sign_wots(&instance::state_label(id, SEQ, 3), &ttt::auth_message(&p8.heads[3])).unwrap();
        let mut w = wots_wire(&reply);
        w.push(sig(&g8.hub.payment, &tx, 0, std::slice::from_ref(&o8.a_out), &leaf.script));
        w.push(sig(&g8.user.payment, &tx, 0, std::slice::from_ref(&o8.a_out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &o8.a_tree.control_block("waive").unwrap());
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("S8: the waiver must mine: {e:#}"));
        println!("V25 S8 waive: {} vB (the claim pays the hub)", tx.vsize());
    }

    // ---- S6: equivocation, the ladder played to the end ----
    let (p_op, p_out, _, _, _) = rebut(&rt, &mut g6, &o6, 0, &venue, (&p6.heads[1], &p6.heads[2]), &tree0, &root0);
    let w6 = o6.window[0].clone();
    let (cont, t_out) = continue_tx(&g6, &w6, p_op, &p_out, "pair_continue", [wots_wire(&root0), wots_wire(&root0_second)].concat());
    rt.mine_with(std::slice::from_ref(&cont)).unwrap_or_else(|e| panic!("S6: pair_continue must mine: {e:#}"));
    let mut at = (OutPoint { txid: cont.compute_txid(), vout: 0 }, t_out);
    p6.mv(&mut g6, 1); // user, 3
    p6.mv(&mut g6, 2); // hub, 4
    p6.mv(&mut g6, 7); // user, 5: column 1-4-7, the user wins
    let mut last_pair = None;
    for j in 3..=5 {
        let (op, out, pair) = post(&rt, &mut g6, &p6, j, at.0, &at.1, None);
        at = (op, out);
        last_pair = Some(pair);
    }
    assert!(TicTacToe.turn(&p6.board).is_none(), "the game is over");
    rt.mine(u64::from(g6.params.delta + g6.params.delta_prime)).unwrap();
    let fin = ladder_split(&mut g6, 5, at.0, &at.1, 0, last_pair.as_ref().unwrap());
    rt.mine_with(std::slice::from_ref(&fin)).unwrap_or_else(|e| panic!("S6: the terminal split must pay UserWins: {e:#}"));
    println!("V25 S6 terminal split (UserWins): {} vB", fin.vsize());

    // ---- S7 continued: the user stalls at 3; the hub's split pays HubWins ----
    rt.mine(u64::from(g7.params.delta + g7.params.delta_prime)).unwrap();
    let s7 = ladder_split(&mut g7, 2, t2_op, &t2_out, 1, &pair7);
    rt.mine_with(std::slice::from_ref(&s7)).unwrap_or_else(|e| panic!("S7: the hub's split must pay HubWins: {e:#}"));
    println!("V25 S7 split after the user's stall (HubWins): {} vB", s7.vsize());

    // ---- S10: the late closing's root holds the late move; the rebuttal
    // stands, but it decides no game: the user's bond to the hub, the game
    // continues on the ladder, the user plays on ----
    let (p_op, p_out, _, _, _) = rebut(&rt, &mut g10, &o10, 0, &venue, (&p10.heads[1], &p10.heads[2]), &tree2, &root2);
    let w10 = o10.window[0].clone();
    rt.mine(u64::from(g10.params.delta + g10.params.delta_prime)).unwrap();
    let (s10, t_out) = stands_tx(&g10, &w10, p_op, &p_out);
    rt.mine_with(std::slice::from_ref(&s10)).unwrap_or_else(|e| panic!("S10: the rebuttal stands: {e:#}"));
    assert_eq!(s10.output.len(), 2);
    assert_eq!(s10.output[1].value, BOND, "S10: only the bond moved");
    assert_eq!(s10.output[0].script_pubkey, ladder(&g10, 2).script_pubkey(), "S10: the stake stays in the game");
    p10.mv(&mut g10, 1); // the user plays on
    let _ = post(&rt, &mut g10, &p10, 3, OutPoint { txid: s10.compute_txid(), vout: 0 }, &t_out, None);
    println!("V25 S10: a self-mined late closing rescued the late move; the rebuttal stands ({} vB), the user's bond ({BOND}) to the hub, no stake moved; the game goes on", s10.vsize());
}
