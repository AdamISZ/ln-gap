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
//!   B's heads and A's path; the rebuttal's own checks pass (the path
//!   leads to the root), and the user's `leaf_hash` disprove takes the pot
//!   (here the substitution loses; it would win only if B were the dated
//!   leaf, i.e. if the member had dated B in time);
//! - S1, a stall: the hub never moved; no member dated anything for this
//!   contract; the user's absence claim and timeout split pay UserWins.
//!
//! Run with `--test-threads=1` or 2.

mod common;

use common::*;
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_contract::Contract;
use lngap_lamport::winternitz::WotsSig;
use lngap_pos::rebut::wots_wire;
use lngap_seal::dating::{Choice, PeriodTree, PAD_LEAF};
use lngap_tictactoe::{Board, TicTacToe};

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
    let (p_op, p_out, pair, levels, _) = rebut(&rt, &mut games[0], &opens[0], 0, &venue, (&heads[0].0, &h2_ok), &tree, &root_sigs[0]);
    let w0 = opens[0].window[0].clone();
    // no disprove fires: leaf_hash and the node checks hold for an honest path
    rt.mine(u64::from(games[0].params.delta)).unwrap();
    let lh = claimant_spend(&games[0], &w0, p_op, &p_out, "leaf_hash", [wots_wire(&pair), wots_wire(&levels[0])].concat());
    assert!(rt.mine_with(std::slice::from_ref(&lh)).is_err(), "an honest leaf digest does not fire leaf_hash");
    let n0 = claimant_spend(&games[0], &w0, p_op, &p_out, "node_0", [wots_wire(&levels[0]), wots_wire(&levels[1])].concat());
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
    let (p_op, p_out, pair, levels, _) = rebut(&rt, &mut games[2], &opens[2], 0, &venue, (&heads[2].0, &h2_b), &tree, &root_sigs[0]);
    let w2 = opens[2].window[0].clone();
    rt.mine(u64::from(games[2].params.delta)).unwrap();
    let lh = claimant_spend(&games[2], &w2, p_op, &p_out, "leaf_hash", [wots_wire(&pair), wots_wire(&levels[0])].concat());
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
///   and the pair (the on-chain root and the late one) sends the game to
///   the on-chain ladder: a member's fault moves no money (`pair_continue`);
/// - an empty closing: member 2 closed period 1 empty; a late root through
///   member 2 sends the game to the ladder with the revealed preimage
///   (`empty_continue`);
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
    let (cont, _) = continue_tx(&games[1], &w, p_op, &p_out, "pair_continue", [wots_wire(&root1), wots_wire(&root1_late)].concat());
    rt.mine_with(std::slice::from_ref(&cont)).unwrap_or_else(|e| panic!("S9: pair_continue must mine: {e:#}"));
    println!("V25 S9 pair_continue: {} vB", cont.vsize());

    // ---- empty closing: a late root through member 2; empty_kill ----
    let (p_op, p_out, _, _, _) = rebut(&rt, &mut games[2], &opens[2], 0, &venue, (&prior[2].0, &h_g3), &late2, &root2_late);
    let w = opens[2].window[0].clone();
    let z = venue[2].member.empty_preimage(1).to_vec();
    let (cont, _) = continue_tx(&games[2], &w, p_op, &p_out, "empty_continue", vec![z]);
    rt.mine_with(std::slice::from_ref(&cont)).unwrap_or_else(|e| panic!("empty_continue must mine: {e:#}"));
    println!("V25 empty_continue: {} vB", cont.vsize());

    // ---- a malformed path: a wrong level-1 sibling; node_1 fires ----
    let (digests, mut siblings) = path_of(&tree1, 3);
    siblings[1] = [0x55; 20];
    let (p_op, p_out, _, levels, _) = rebut_with(&rt, &mut games[3], &opens[3], 0, &venue, (&prior[3].0, &h_g4), (digests, siblings), &root1, true);
    let w = opens[3].window[0].clone();
    rt.mine(u64::from(games[3].params.delta)).unwrap();
    let n0 = claimant_spend(&games[3], &w, p_op, &p_out, "node_0", [wots_wire(&levels[0]), wots_wire(&levels[1])].concat());
    assert!(rt.mine_with(std::slice::from_ref(&n0)).is_err(), "level 0 is honest: node_0 does not fire");
    let n1 = claimant_spend(&games[3], &w, p_op, &p_out, "node_1", [wots_wire(&levels[1]), wots_wire(&root1)].concat());
    rt.mine_with(std::slice::from_ref(&n1)).unwrap_or_else(|e| panic!("node_1 must fire on a wrong sibling: {e:#}"));
    println!("V25 node_1 disprove: {} vB", n1.vsize());
}
