//! Tic-tac-toe on the fact chain: G1–G6 (docs/planning/VENUE.md).
//!
//! The reference game (user X, hub O): 4, 1, 0, 8, 6, 3, 2 → X wins at
//! move 7 (XOX/OX./X.O).

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::Role;
use lngap_harness::game_world::{Brain, GameWorld, RESERVE, STAKE};

const USER_MOVES: [u8; 4] = [4, 0, 6, 2];
const HUB_MOVES: [u8; 3] = [1, 8, 3];

fn honest() -> [Brain; 2] {
    [Brain { moves: USER_MOVES.to_vec(), ..Default::default() }, Brain { moves: HUB_MOVES.to_vec(), ..Default::default() }]
}

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

/// Contract transactions by kind: (commitments, moves, splits, disproofs, other).
fn summary(w: &GameWorld) -> (usize, Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let txs = w.contract_txs();
    let c = txs.iter().filter(|r| r.starts_with("commitment_")).count();
    let strip = |r: &String| r.rsplit('/').next().unwrap().to_string();
    let m: Vec<String> = txs.iter().filter(|r| strip(r).starts_with("move_")).cloned().collect();
    let s: Vec<String> = txs.iter().filter(|r| strip(r).starts_with("split_")).cloned().collect();
    let d: Vec<String> = txs.iter().filter(|r| r.starts_with("disprove_")).cloned().collect();
    let o: Vec<String> = txs.iter().filter(|r| !r.starts_with("commitment_") && !strip(r).starts_with("move_") && !strip(r).starts_with("split_") && !r.starts_with("disprove_")).cloned().collect();
    (c, m, s, d, o)
}

#[test]
fn g1_cooperative_game_folds_off_chain() -> Result<()> {
    let mut w = GameWorld::new("G1", honest())?;
    w.step_until(30, |w| w.contracts() == 0)?;
    println!("\n{}", w.narrative());
    assert_eq!(w.depth, 7, "seven moves on the venue");
    assert_eq!(w.board.render(), "XOX/OX./X.O");
    assert!(w.party_txs().is_empty(), "nothing on Bitcoin: {:?}", w.party_txs());
    // user wins: 2 × STAKE + own RESERVE; hub keeps its RESERVE
    assert_eq!(w.balances(), [sat(100_000) - STAKE - RESERVE + STAKE + STAKE + RESERVE, sat(100_000) - STAKE - RESERVE + RESERVE]);
    Ok(())
}

/// The loser stalls: three transactions settle the game whatever its depth.
fn stall_case(label: &str, stall_at: u32, expect_depth: u32) -> Result<()> {
    let mut b = honest();
    b[Role::Hub.idx()].stall_at = Some(stall_at);
    let mut w = GameWorld::new(label, b)?;
    w.step_until(60, |w| w.contract_txs().iter().any(|r| r.starts_with("split_")))?;
    w.steps(2)?;
    println!("\n{}", w.narrative());
    let (c, m, s, d, o) = summary(&w);
    println!("=== {label}: commitments {c}, moves {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}");
    assert_eq!(c, 1, "one force-close");
    assert_eq!(m, vec![format!("move_{expect_depth}")], "one timeout claim, at the user's last move");
    assert_eq!(s, vec![format!("split_{expect_depth}_UserWins")], "one split after the window");
    assert!(d.is_empty() && o.is_empty(), "nothing else: {d:?} {o:?}");
    assert!(w.h.balance(Role::User) > sat(100_000) + STAKE, "the user takes the stakes and the reserve: {}", w.h.balance(Role::User));
    Ok(())
}

#[test]
fn g2a_hub_stalls_early() -> Result<()> {
    stall_case("G2A", 2, 1)
}

#[test]
fn g2b_hub_stalls_late() -> Result<()> {
    stall_case("G2B", 6, 5)
}

#[test]
fn g3_loser_refuses_the_fold() -> Result<()> {
    let mut b = honest();
    b[Role::Hub.idx()].refuse_fold = true;
    let mut w = GameWorld::new("G3", b)?;
    w.step_until(60, |w| w.contract_txs().iter().any(|r| r.starts_with("split_")))?;
    w.steps(2)?;
    println!("\n{}", w.narrative());
    let (c, m, s, d, o) = summary(&w);
    println!("=== G3: commitments {c}, moves {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}");
    assert_eq!(w.depth, 7);
    assert_eq!(c, 1);
    assert_eq!(m, vec!["move_7".to_string()], "the winner claims the terminal position");
    assert_eq!(s, vec!["split_7_UserWins".to_string()]);
    assert!(d.is_empty() && o.is_empty());
    assert!(w.h.balance(Role::User) > sat(100_000) + STAKE);
    Ok(())
}

#[test]
fn g4_spurious_timeout_claim_is_refuted_by_inclusion() -> Result<()> {
    let mut b = honest();
    b[Role::Hub.idx()].ignore_at = Some(3);
    let mut w = GameWorld::new("G4", b)?;
    w.step_until(80, |w| w.contract_txs().iter().any(|r| r.contains("split_")))?;
    w.steps(2)?;
    println!("\n{}", w.narrative());
    let (c, m, s, d, o) = summary(&w);
    println!("=== G4: commitments {c}, moves {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}");
    assert_eq!(c, 1);
    assert_eq!(m, vec!["move_2".to_string(), "move_3".to_string()], "the hub's timeout claim and the user's refutation");
    assert_eq!(s, vec!["r2/split_3_UserWins".to_string()], "the refuted claimant forfeits");
    assert!(d.is_empty() && o.is_empty(), "no dispute: the refutation's inclusion claim is honest");
    assert!(w.h.balance(Role::User) > sat(100_000) + STAKE);
    Ok(())
}

#[test]
fn g5_invalid_move_is_disproved() -> Result<()> {
    let mut b = honest();
    b[Role::Hub.idx()].invalid_at = Some(4);
    b[Role::User.idx()].passive = true;
    let mut w = GameWorld::new("G5", b)?;
    w.step_until(80, |w| w.contract_txs().iter().any(|r| r.starts_with("disprove_")))?;
    w.steps(2)?;
    println!("\n{}", w.narrative());
    let (c, m, s, d, o) = summary(&w);
    println!("=== G5: commitments {c}, moves {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}");
    assert_eq!(c, 1);
    assert_eq!(m, vec!["move_4".to_string()], "the hub claims its invalid move");
    assert!(d.iter().any(|r| r.starts_with("disprove_cell_occupied_")), "disproved by the occupied-cell leaf: {d:?}");
    assert!(s.is_empty() && o.is_empty());
    println!("=== G5: on-chain balances user {} / hub {}", w.h.balance(Role::User), w.h.balance(Role::Hub));
    assert!(w.h.balance(Role::User) > sat(100_000) + STAKE - sat(5_000), "user: {}", w.h.balance(Role::User));
    Ok(())
}

#[test]
fn g6_fabricated_inclusion_is_disproved_by_bisection() -> Result<()> {
    let mut b = honest();
    b[Role::Hub.idx()].fabricate_at = Some(4);
    b[Role::User.idx()].passive = true;
    let mut w = GameWorld::new("G6", b)?;
    w.step_until(120, |w| {
        w.contract_txs().iter().any(|r| r.starts_with("simple_") || r.starts_with("cpred_") || r.starts_with("ccopy_") || r.starts_with("flat_") || r.starts_with("re_") || r.starts_with("block_") || r.starts_with("ckeep_"))
    })?;
    w.steps(2)?;
    println!("\n{}", w.narrative());
    let (c, m, s, d, o) = summary(&w);
    println!("=== G6: commitments {c}, moves {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}");
    assert_eq!(m, vec!["move_4".to_string()]);
    assert!(o.iter().any(|r| r == "d4/dispute"), "the user disputes the inclusion claim: {o:?}");
    let leaf = o.iter().find(|r| r.starts_with("simple_") || r.starts_with("cpred_")).expect("a predicate disproof");
    println!("=== G6: disproved at {leaf} after {} dispute transactions", o.len());
    assert!(s.is_empty());
    println!("=== G6: on-chain balances user {} / hub {}", w.h.balance(Role::User), w.h.balance(Role::Hub));
    // the user takes the contract output (minus the dispute chain's fees); the hub is left with its balance sweep
    assert!(w.h.balance(Role::User) > sat(100_000) + STAKE - sat(20_000), "user: {}", w.h.balance(Role::User));
    assert!(w.h.balance(Role::Hub) < sat(100_000) - STAKE, "hub: {}", w.h.balance(Role::Hub));
    Ok(())
}
