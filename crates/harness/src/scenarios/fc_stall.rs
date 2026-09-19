//! Tic-tac-toe on the fact chain with the stall graph (D28): S1–S9.
//! The reference game is G's: user X, hub O, 4, 1, 0, 8, 6, 3, 2, X wins
//! at move 7. Every on-chain resolution is a stall proof or a lie exhibit
//! by the honest party, answered at most by one leaf or one dispute.

use anyhow::{ensure, Result};
use bitcoin::Amount;
use lngap_channel::Role;

use super::{Report, Scenario};
use crate::game_world::{Brain, GameWorld, RESERVE, STAKE};

const USER_MOVES: [u8; 4] = [4, 0, 6, 2];
const HUB_MOVES: [u8; 3] = [1, 8, 3];

fn honest() -> [Brain; 2] {
    [Brain { moves: USER_MOVES.to_vec(), ..Default::default() }, Brain { moves: HUB_MOVES.to_vec(), ..Default::default() }]
}

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

/// Contract transactions by kind: (commitments, claims on C, splits, disproofs, dispute and other).
pub fn summary(w: &GameWorld) -> (usize, Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let txs = w.contract_txs();
    let c = txs.iter().filter(|r| r.starts_with("commitment_")).count();
    let last = |r: &String| r.rsplit('/').next().unwrap().to_string();
    let claims: Vec<String> = txs.iter().filter(|r| !r.contains('/') && (r.starts_with("stall_") || r.starts_with("lie_") || r.starts_with("sig_"))).cloned().collect();
    let s: Vec<String> = txs.iter().filter(|r| last(r).starts_with("split_")).cloned().collect();
    let d: Vec<String> = txs.iter().filter(|r| r.starts_with("disprove_")).cloned().collect();
    let o: Vec<String> = txs.iter().filter(|r| !r.starts_with("commitment_") && !claims.contains(r) && !last(r).starts_with("split_") && !r.starts_with("disprove_")).cloned().collect();
    (c, claims, s, d, o)
}

fn report(w: &GameWorld, sc: &Scenario) -> Report {
    let mut r = Report::from_harness(&w.h, sc.id, sc.title, sc.expected);
    r.narrative = w.narrative();
    let (c, m, s, d, o) = summary(w);
    println!("=== {}: commitments {c}, claims {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}", sc.id);
    println!("=== {}: on-chain balances user {} / hub {}", sc.id, w.h.balance(Role::User), w.h.balance(Role::Hub));
    println!("\n{}", r.narrative);
    r
}

fn until_settled(w: &mut GameWorld) -> Result<()> {
    w.step_until(120, |w| w.contract_txs().iter().any(|r| r.rsplit('/').next().unwrap().starts_with("split_") || r.starts_with("disprove_")))?;
    w.steps(2)
}

pub const S1: Scenario = Scenario {
    id: "S1",
    title: "Stall graph: cooperative game, folded off-chain",
    expected: "seven moves on the fact chain, no Bitcoin transaction; 73 pre-signed transactions at open",
    run: || {
        let mut w = GameWorld::new_stall("S1", honest())?;
        w.step_until(30, |w| w.contracts() == 0)?;
        ensure!(w.depth == 7 && w.board.render() == "XOX/OX./X.O");
        ensure!(w.party_txs().is_empty(), "nothing on Bitcoin: {:?}", w.party_txs());
        ensure!(w.balances() == [sat(100_000) - STAKE - RESERVE + STAKE + STAKE + RESERVE, sat(100_000) - STAKE - RESERVE + RESERVE]);
        Ok(report(&w, &S1))
    },
};

fn stall(sc: &Scenario, stall_at: u32, expect_depth: u32) -> Result<Report> {
    let mut b = honest();
    b[Role::Hub.idx()].stall_at = Some(stall_at);
    let mut w = GameWorld::new_stall(sc.id, b)?;
    until_settled(&mut w)?;
    let (c, m, s, d, o) = summary(&w);
    ensure!(c == 1, "one force-close");
    ensure!(m == vec!["stall_user".to_string()], "one stall proof: {m:?}");
    ensure!(s == vec!["stall_user/split_1_UserWins".to_string()], "one split: {s:?}");
    ensure!(d.is_empty() && o.is_empty(), "nothing else: {d:?} {o:?}");
    ensure!(w.depth == expect_depth);
    ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "the user takes the stakes and the reserve");
    Ok(report(&w, sc))
}

pub const S2A: Scenario = Scenario {
    id: "S2A",
    title: "Stall graph: the hub stalls at move 2",
    expected: "commitment, stall_user (depth 1 revealed), stall_user/split_1_UserWins: three transactions",
    run: || stall(&S2A, 2, 1),
};

pub const S2B: Scenario = Scenario {
    id: "S2B",
    title: "Stall graph: the hub stalls at move 6",
    expected: "the same three transactions through the same leaf, the depth a revealed field",
    run: || stall(&S2B, 6, 5),
};

pub const S3: Scenario = Scenario {
    id: "S3",
    title: "Stall graph: the loser refuses the fold",
    expected: "the winner proves the hub has no move after 7: stall_user, split_1_UserWins",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].refuse_fold = true;
        let mut w = GameWorld::new_stall("S3", b)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(w.depth == 7 && c == 1);
        ensure!(m == vec!["stall_user".to_string()] && s == vec!["stall_user/split_1_UserWins".to_string()], "{m:?} {s:?}");
        ensure!(d.is_empty() && o.is_empty());
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE);
        Ok(report(&w, &S3))
    },
};

pub const S4: Scenario = Scenario {
    id: "S4",
    title: "Stall graph: a spurious stall proof is disputed",
    expected: "the hub proves a stall at depth 2 although the user's move 3 is on the venue; the claim's head check at slot 3 fails; the user disputes and the bisection lands on that step; the user takes the bond",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].ignore_at = Some(3);
        let mut w = GameWorld::new_stall("S4", b)?;
        w.step_until(120, |w| w.contract_txs().iter().any(|r| r.starts_with("cpred_") || r.starts_with("flat_") || r.starts_with("simple_") || r.contains("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["stall_hub".to_string()], "the hub's spurious stall proof: {m:?}");
        ensure!(s.is_empty() && d.is_empty(), "no split, no disproof: {s:?} {d:?}");
        ensure!(o.iter().any(|r| r == "stall_hub/d2/dispute"), "the user disputed: {o:?}");
        ensure!(o.iter().any(|r| r.starts_with("cpred_h3_b5")), "the head check at slot 3 is the failing step: {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "the user takes the bond: {}", w.h.balance(Role::User));
        Ok(report(&w, &S4))
    },
};

pub const S5A: Scenario = Scenario {
    id: "S5A",
    title: "Stall graph: an invalid move claimed as a stall proof is disproved off the stall output",
    expected: "the hub publishes an occupied cell at move 2 and proves a stall at depth 2; the user spends disprove_cell_occupied_4 off stall_hub",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].invalid_at = Some(2);
        b[Role::Hub.idx()].claim_own_invalid = true;
        b[Role::User.idx()].no_exhibit = true;
        let mut w = GameWorld::new_stall("S5A", b)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["stall_hub".to_string()], "the hub's stall proof: {m:?}");
        ensure!(d == vec!["disprove_cell_occupied_4".to_string()], "the user's disproof: {d:?}");
        ensure!(s.is_empty() && o.is_empty(), "{s:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE);
        Ok(report(&w, &S5A))
    },
};

pub const S5B: Scenario = Scenario {
    id: "S5B",
    title: "Stall graph: an invalid move is exhibited by the victim",
    expected: "the hub publishes an occupied cell at move 2 and does nothing; the user exhibits it (lie_user) and, after the hub's window, spends disprove_cell_occupied_4 off its own exhibit",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].invalid_at = Some(2);
        let mut w = GameWorld::new_stall("S5B", b)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["lie_user".to_string()], "the user's exhibit: {m:?}");
        ensure!(d == vec!["disprove_cell_occupied_4".to_string()], "the user's disproof: {d:?}");
        ensure!(s.is_empty() && o.is_empty(), "{s:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE);
        Ok(report(&w, &S5B))
    },
};

pub const S6: Scenario = Scenario {
    id: "S6",
    title: "Stall graph: a fabricated stall proof is disputed",
    expected: "the hub's slot 2 is empty; it proves a stall with the move it meant to publish (the user, passive on the venue, does not prove the stall first); the head check at slot 2 fails; the user disputes and wins the bisection",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].fabricate_at = Some(2);
        b[Role::User.idx()].passive = true;
        let mut w = GameWorld::new_stall("S6", b)?;
        w.step_until(120, |w| w.contract_txs().iter().any(|r| r.starts_with("cpred_") || r.starts_with("flat_") || r.starts_with("simple_") || r.contains("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["stall_hub".to_string()], "{m:?}");
        ensure!(s.is_empty() && d.is_empty(), "{s:?} {d:?}");
        ensure!(o.iter().any(|r| r == "stall_hub/d2/dispute"), "the user disputed: {o:?}");
        ensure!(o.iter().any(|r| r.starts_with("cpred_h2_b5")), "the head check at slot 2 is the failing step: {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE);
        Ok(report(&w, &S6))
    },
};

pub const S7: Scenario = Scenario {
    id: "S7",
    title: "Stall graph: a baseless exhibit pays the framed party",
    expected: "the user exhibits the hub's valid move 2 as a lie; no disprove leaf fires; after the window the split pays the hub",
    run: || {
        let mut b = honest();
        b[Role::User.idx()].frame_at = Some(2);
        let mut w = GameWorld::new_stall("S7", b)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["lie_user".to_string()], "{m:?}");
        ensure!(s == vec!["lie_user/split_3_HubWins".to_string()], "the split pays the hub: {s:?}");
        ensure!(d.is_empty() && o.is_empty(), "{d:?} {o:?}");
        ensure!(w.h.balance(Role::Hub) > sat(100_000) + STAKE, "the hub takes the bond: {}", w.h.balance(Role::Hub));
        Ok(report(&w, &S7))
    },
};

pub const S8: Scenario = Scenario {
    id: "S8",
    title: "Stall graph: a garbage-signed entry is exhibited",
    expected: "the hub publishes move 2 with garbage preimages; the stall claim would count the slot as held, so the user exhibits the signature (sig_user, D31); the hub cannot dispute; after delta the split pays the user",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].garbage_at = Some(2);
        let mut w = GameWorld::new_stall("S8", b)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(w.depth == 1 && c == 1);
        ensure!(m == vec!["sig_user".to_string()], "{m:?}");
        ensure!(s == vec!["sig_user/split_5_UserWins".to_string()], "{s:?}");
        ensure!(d.is_empty() && o.is_empty(), "{d:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "user balance {}", w.h.balance(Role::User));
        Ok(report(&w, &S8))
    },
};

pub const S9: Scenario = Scenario {
    id: "S9",
    title: "Stall graph: a baseless signature exhibit is disputed",
    expected: "the user exhibits the hub's soundly signed move 2 as garbage-signed; the exhibited digest equals the commitment, so the claim's first check fails; the hub disputes and wins the bisection at simple_pre_chk",
    run: || {
        let mut b = honest();
        b[Role::User.idx()].fabricate_sig_at = Some(2);
        let mut w = GameWorld::new_stall("S9", b)?;
        w.step_until(120, |w| w.contract_txs().iter().any(|r| r.starts_with("cpred_") || r.starts_with("flat_") || r.starts_with("simple_") || r.contains("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["sig_user".to_string()], "{m:?}");
        ensure!(s.is_empty() && d.is_empty(), "{s:?} {d:?}");
        ensure!(o.iter().any(|r| r == "sig_user/d5/dispute"), "the hub disputed: {o:?}");
        ensure!(o.iter().any(|r| r.starts_with("simple_pre_chk")), "the preamble check is the failing step: {o:?}");
        ensure!(w.h.balance(Role::Hub) > sat(100_000), "hub balance {}", w.h.balance(Role::Hub));
        Ok(report(&w, &S9))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![S1, S2A, S2B, S3, S4, S5A, S5B, S6, S7, S8, S9]
}
