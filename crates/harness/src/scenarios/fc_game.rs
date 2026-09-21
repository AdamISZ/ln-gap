//! Tic-tac-toe on the fact chain: G1–G6 (docs/design-notes/GAME_PROTOCOL.md).
//!
//! The reference game (user X, hub O): 4, 1, 0, 8, 6, 3, 2 → X wins at
//! move 7 (XOX/OX./X.O).

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

/// Contract transactions by kind: (commitments, moves, splits, disproofs, other).
pub fn summary(w: &GameWorld) -> (usize, Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let txs = w.contract_txs();
    let c = txs.iter().filter(|r| r.starts_with("commitment_")).count();
    let strip = |r: &String| r.rsplit('/').next().unwrap().to_string();
    let m: Vec<String> = txs.iter().filter(|r| strip(r).starts_with("move_")).cloned().collect();
    let s: Vec<String> = txs.iter().filter(|r| strip(r).starts_with("split_")).cloned().collect();
    let d: Vec<String> = txs.iter().filter(|r| r.starts_with("disprove_")).cloned().collect();
    let o: Vec<String> = txs.iter().filter(|r| !r.starts_with("commitment_") && !strip(r).starts_with("move_") && !strip(r).starts_with("split_") && !r.starts_with("disprove_")).cloned().collect();
    (c, m, s, d, o)
}

fn report(w: &GameWorld, sc: &Scenario) -> Report {
    let mut r = Report::from_harness(&w.h, sc.id, sc.title, sc.expected);
    r.narrative = w.narrative();
    let (c, m, s, d, o) = summary(w);
    println!("=== {}: commitments {c}, moves {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}", sc.id);
    println!("=== {}: on-chain balances user {} / hub {}", sc.id, w.h.balance(Role::User), w.h.balance(Role::Hub));
    println!("\n{}", r.narrative);
    r
}

pub const G1: Scenario = Scenario {
    id: "G1",
    title: "Cooperative game on the venue, folded off-chain",
    expected: "seven moves on the fact chain, no Bitcoin transaction; the winner gets both stakes and its reserve back",
    run: || {
        let mut w = GameWorld::new("G1", honest())?;
        w.step_until(30, |w| w.contracts() == 0)?;
        ensure!(w.depth == 7 && w.board.render() == "XOX/OX./X.O");
        ensure!(w.party_txs().is_empty(), "nothing on Bitcoin: {:?}", w.party_txs());
        ensure!(w.balances() == [sat(100_000) - STAKE - RESERVE + STAKE + STAKE + RESERVE, sat(100_000) - STAKE - RESERVE + RESERVE]);
        Ok(report(&w, &G1))
    },
};

fn stall(sc: &Scenario, stall_at: u32, expect_depth: u32) -> Result<Report> {
    let mut b = honest();
    b[Role::Hub.idx()].stall_at = Some(stall_at);
    let mut w = GameWorld::new(sc.id, b)?;
    w.step_until(60, |w| w.contract_txs().iter().any(|r| r.starts_with("split_")))?;
    w.steps(2)?;
    let (c, m, s, d, o) = summary(&w);
    ensure!(c == 1, "one force-close");
    ensure!(m == vec![format!("move_{expect_depth}")], "one timeout claim at the user's last move: {m:?}");
    ensure!(s == vec![format!("split_{expect_depth}_UserWins")], "one split: {s:?}");
    ensure!(d.is_empty() && o.is_empty(), "nothing else: {d:?} {o:?}");
    ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "the user takes the stakes and the reserve");
    Ok(report(&w, sc))
}

pub const G2A: Scenario = Scenario {
    id: "G2A",
    title: "The hub stalls at move 2",
    expected: "commitment, move_1 (the user's timeout claim), split_1_UserWins: three transactions",
    run: || stall(&G2A, 2, 1),
};

pub const G2B: Scenario = Scenario {
    id: "G2B",
    title: "The hub stalls at move 6",
    expected: "commitment, move_5 (the user's timeout claim), split_5_UserWins: the same three transactions",
    run: || stall(&G2B, 6, 5),
};

pub const G3: Scenario = Scenario {
    id: "G3",
    title: "The loser refuses the cooperative fold",
    expected: "commitment, move_7 (the winner claims the terminal position), split_7_UserWins",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].refuse_fold = true;
        let mut w = GameWorld::new("G3", b)?;
        w.step_until(60, |w| w.contract_txs().iter().any(|r| r.starts_with("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(w.depth == 7 && c == 1);
        ensure!(m == vec!["move_7".to_string()] && s == vec!["split_7_UserWins".to_string()], "{m:?} {s:?}");
        ensure!(d.is_empty() && o.is_empty());
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE);
        Ok(report(&w, &G3))
    },
};

pub const G4: Scenario = Scenario {
    id: "G4",
    title: "A spurious timeout claim is refuted by an inclusion proof",
    expected: "the hub claims the user missed move 3; the user answers with move_3 and its slot-3 inclusion claim; r2/split_3_UserWins: the claimant forfeits",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].ignore_at = Some(3);
        let mut w = GameWorld::new("G4", b)?;
        w.step_until(80, |w| w.contract_txs().iter().any(|r| r.contains("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["move_2".to_string(), "move_3".to_string()], "the claim and the refutation: {m:?}");
        ensure!(s == vec!["r2/split_3_UserWins".to_string()], "{s:?}");
        ensure!(d.is_empty() && o.is_empty(), "no dispute: the refutation's inclusion claim is honest");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE);
        Ok(report(&w, &G4))
    },
};

pub const G5: Scenario = Scenario {
    id: "G5",
    title: "An invalid move is claimed and disproved",
    expected: "the hub publishes an occupied cell and claims it as a timeout of the user; disprove_cell_occupied_0",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].invalid_at = Some(4);
        b[Role::User.idx()].passive = true;
        let mut w = GameWorld::new("G5", b)?;
        w.step_until(80, |w| w.contract_txs().iter().any(|r| r.starts_with("disprove_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1 && m == vec!["move_4".to_string()]);
        ensure!(d.iter().any(|r| r.starts_with("disprove_cell_occupied_")), "{d:?}");
        ensure!(s.is_empty() && o.is_empty());
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE - sat(5_000));
        Ok(report(&w, &G5))
    },
};

pub const G6: Scenario = Scenario {
    id: "G6",
    title: "A fabricated inclusion claim is disproved by bisection",
    expected: "the hub claims a move it never published; the user disputes; the bisection isolates the root_ok step and disproves it",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].fabricate_at = Some(4);
        b[Role::User.idx()].passive = true;
        let mut w = GameWorld::new("G6", b)?;
        w.step_until(120, |w| w.contract_txs().iter().any(|r| r.starts_with("simple_") || r.starts_with("cpred_") || r.starts_with("ccopy_") || r.starts_with("flat_") || r.starts_with("re_") || r.starts_with("block_") || r.starts_with("ckeep_")))?;
        w.steps(2)?;
        let (_, m, s, _, o) = summary(&w);
        ensure!(m == vec!["move_4".to_string()]);
        ensure!(o.iter().any(|r| r == "d4/dispute"), "{o:?}");
        ensure!(o.iter().any(|r| r.starts_with("simple_") || r.starts_with("cpred_")), "a predicate disproof: {o:?}");
        ensure!(s.is_empty());
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE - sat(20_000));
        ensure!(w.h.balance(Role::Hub) < sat(100_000) - STAKE);
        Ok(report(&w, &G6))
    },
};

pub const G7: Scenario = Scenario {
    id: "G7",
    title: "A garbage-signed move is a stall",
    expected: "the hub publishes move 4 with garbage in place of its signature and stalls; the user's timeout claim at depth 3 cannot be answered: commitment, move_3, split_3_UserWins",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].garbage_at = Some(4);
        b[Role::Hub.idx()].passive = true;
        let mut w = GameWorld::new("G7", b)?;
        w.step_until(60, |w| w.contract_txs().iter().any(|r| r.starts_with("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1 && m == vec!["move_3".to_string()] && s == vec!["split_3_UserWins".to_string()], "{m:?} {s:?}");
        ensure!(d.is_empty() && o.is_empty(), "nothing else: {d:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE);
        Ok(report(&w, &G7))
    },
};

pub const G7B: Scenario = Scenario {
    id: "G7B",
    title: "A garbage-signed move cannot refute a timeout claim",
    expected: "the hub answers the user's timeout claim with its garbage-signed move 4; the user disputes the inclusion claim and the bisection isolates the signature predicate (cpred)",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].garbage_at = Some(4);
        b[Role::Hub.idx()].refute_with_garbage = true;
        let mut w = GameWorld::new("G7B", b)?;
        w.step_until(120, |w| w.contract_txs().iter().any(|r| r.starts_with("cpred_") || r.starts_with("simple_") || r.starts_with("ccopy_") || r.starts_with("flat_") || r.starts_with("re_") || r.starts_with("block_") || r.starts_with("ckeep_")))?;
        w.steps(2)?;
        let (_, m, s, _, o) = summary(&w);
        ensure!(m == vec!["move_3".to_string(), "move_4".to_string()], "the claim and the garbage refutation: {m:?}");
        ensure!(o.iter().any(|r| r == "r3/d4/dispute"), "the user disputes the refutation's claim: {o:?}");
        ensure!(o.iter().any(|r| r.starts_with("cpred_")), "the signature predicate fails: {o:?}");
        ensure!(s.is_empty());
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE - sat(25_000));
        ensure!(w.h.balance(Role::Hub) < sat(100_000) - STAKE);
        Ok(report(&w, &G7B))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![G1, G2A, G2B, G3, G4, G5, G6, G7, G7B]
}
