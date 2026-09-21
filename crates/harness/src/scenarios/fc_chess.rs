//! Chess on the fact chain with the stall graph: C1–C9. White (the user)
//! opens 1.e4 e5 2.Nf3 Nc6 3.Bc4 Nf6 and the hub resigns after move 6.

use anyhow::{ensure, Result};
use bitcoin::Amount;
use lngap_channel::Role;

use super::{Report, Scenario};
use crate::chess_world::{ChessBrain, ChessWorld, RESERVE, STAKE};

const USER: [&str; 3] = ["e2e4", "g1f3", "f1c4"];
const HUB: [&str; 3] = ["e7e5", "b8c6", "g8f6"];

fn honest() -> [ChessBrain; 2] {
    [ChessBrain { moves: USER.to_vec(), ..Default::default() }, ChessBrain { moves: HUB.to_vec(), ..Default::default() }]
}

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

pub fn summary(w: &ChessWorld) -> (usize, Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let txs = w.contract_txs();
    let c = txs.iter().filter(|r| r.starts_with("commitment_")).count();
    let last = |r: &String| r.rsplit('/').next().unwrap().to_string();
    let claims: Vec<String> = txs.iter().filter(|r| !r.contains('/') && (r.starts_with("stall_") || r.starts_with("lie_") || r.starts_with("sig_"))).cloned().collect();
    let s: Vec<String> = txs.iter().filter(|r| last(r).starts_with("split_")).cloned().collect();
    let d: Vec<String> = txs.iter().filter(|r| r.starts_with("disprove_")).cloned().collect();
    let o: Vec<String> = txs.iter().filter(|r| !r.starts_with("commitment_") && !claims.contains(r) && !last(r).starts_with("split_") && !r.starts_with("disprove_")).cloned().collect();
    (c, claims, s, d, o)
}

fn report(w: &ChessWorld, sc: &Scenario) -> Report {
    let mut r = Report::from_harness(&w.h, sc.id, sc.title, sc.expected);
    r.narrative = w.narrative();
    let (c, m, s, d, o) = summary(w);
    println!("=== {}: commitments {c}, claims {m:?}, splits {s:?}, disproofs {d:?}, other {o:?}", sc.id);
    println!("=== {}: on-chain balances user {} / hub {}", sc.id, w.h.balance(Role::User), w.h.balance(Role::Hub));
    println!("\n{}", r.narrative);
    r
}

fn until_settled(w: &mut ChessWorld) -> Result<()> {
    w.step_until(150, |w| w.contract_txs().iter().any(|r| r.rsplit('/').next().unwrap().starts_with("split_") || r.starts_with("disprove_")))?;
    w.steps(2)
}

pub const C1: Scenario = Scenario {
    id: "C1",
    title: "Chess: a cooperative game, the hub resigns, folded off-chain",
    expected: "six moves on the fact chain, no Bitcoin transaction; the user takes both stakes and its reserve",
    run: || {
        let mut w = ChessWorld::new("C1", honest(), 6)?;
        w.step_until(40, |w| w.contracts() == 0)?;
        ensure!(w.depth == 6, "depth {}", w.depth);
        ensure!(w.party_txs().is_empty(), "nothing on Bitcoin: {:?}", w.party_txs());
        ensure!(w.balances() == [sat(100_000) - STAKE - RESERVE + STAKE + STAKE + RESERVE, sat(100_000) - STAKE - RESERVE + RESERVE]);
        Ok(report(&w, &C1))
    },
};

pub const C2: Scenario = Scenario {
    id: "C2",
    title: "Chess: the hub stalls at move 2",
    expected: "commitment, stall_user binding the whole position after 1.e4 in its WOTS end state, stall_user/split_1_UserWins",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].stall_at = Some(2);
        let mut w = ChessWorld::new("C2", b, 6)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["stall_user".to_string()], "{m:?}");
        ensure!(s == vec!["stall_user/split_1_UserWins".to_string()], "{s:?}");
        ensure!(d.is_empty() && o.is_empty(), "{d:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "user balance {}", w.h.balance(Role::User));
        Ok(report(&w, &C2))
    },
};

pub const C3: Scenario = Scenario {
    id: "C3",
    title: "Chess: the loser refuses the fold",
    expected: "the hub, to move after 5, refuses the fold and does not move; the user proves it has no move after 5: stall_user, split_1_UserWins",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].refuse_fold = true;
        let mut w = ChessWorld::new("C3", b, 5)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(w.depth == 5 && c == 1);
        ensure!(m == vec!["stall_user".to_string()] && s == vec!["stall_user/split_1_UserWins".to_string()], "{m:?} {s:?}");
        ensure!(d.is_empty() && o.is_empty());
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "user balance {}", w.h.balance(Role::User));
        Ok(report(&w, &C3))
    },
};

pub const C4: Scenario = Scenario {
    id: "C4",
    title: "Chess: an illegal move claimed as a stall proof is disproved off the stall output",
    expected: "after 1.e4 the hub plays Qd8-h4 through its own pawn and proves a stall; the user spends disprove_chess_ray with exhibit j = 1 off stall_hub",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].illegal_at = Some((2, "d8h4"));
        b[Role::Hub.idx()].claim_own_illegal = true;
        b[Role::User.idx()].no_exhibit = true;
        let mut w = ChessWorld::new("C4", b, 6)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["stall_hub".to_string()], "{m:?}");
        ensure!(d == vec!["disprove_chess_ray".to_string()], "{d:?}");
        ensure!(s.is_empty() && o.is_empty(), "{s:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "user balance {}", w.h.balance(Role::User));
        Ok(report(&w, &C4))
    },
};

pub const C5: Scenario = Scenario {
    id: "C5",
    title: "Chess: an illegal move is exhibited by the victim",
    expected: "after 1.e4 the hub plays Qd8-h4 through its pawn and does nothing; the user exhibits it (lie_user) and, after the hub's window, spends disprove_chess_ray off its exhibit",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].illegal_at = Some((2, "d8h4"));
        let mut w = ChessWorld::new("C5", b, 6)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["lie_user".to_string()], "{m:?}");
        ensure!(d == vec!["disprove_chess_ray".to_string()], "{d:?}");
        ensure!(s.is_empty() && o.is_empty(), "{s:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "user balance {}", w.h.balance(Role::User));
        Ok(report(&w, &C5))
    },
};

pub const C6: Scenario = Scenario {
    id: "C6",
    title: "Chess: a baseless exhibit pays the framed party",
    expected: "the user exhibits the hub's legal 1...e5 as a lie; no challenge leaf fires; after the window the split pays the hub",
    run: || {
        let mut b = honest();
        b[Role::User.idx()].frame_at = Some(2);
        let mut w = ChessWorld::new("C6", b, 6)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["lie_user".to_string()], "{m:?}");
        ensure!(s == vec!["lie_user/split_3_HubWins".to_string()], "{s:?}");
        ensure!(d.is_empty() && o.is_empty(), "{d:?} {o:?}");
        ensure!(w.h.balance(Role::Hub) > sat(100_000) + STAKE, "hub balance {}", w.h.balance(Role::Hub));
        Ok(report(&w, &C6))
    },
};

pub const C7: Scenario = Scenario {
    id: "C7",
    title: "Chess: a fabricated stall proof is disputed",
    expected: "the hub's slot 2 is empty; it proves a stall with 1...e5 anyway; the head check at slot 2 fails; the user disputes and wins the ten-round bisection with cpred_h2_b5, taking the pot net of fees",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].fabricate_at = Some(2);
        b[Role::User.idx()].passive = true;
        let mut w = ChessWorld::new("C7", b, 6)?;
        w.step_until(200, |w| w.contract_txs().iter().any(|r| r.starts_with("cpred_") || r.starts_with("flat_") || r.starts_with("simple_") || r.contains("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["stall_hub".to_string()], "{m:?}");
        ensure!(s.is_empty() && d.is_empty(), "{s:?} {d:?}");
        ensure!(o.iter().any(|r| r == "stall_hub/d2/dispute"), "{o:?}");
        ensure!(o.iter().any(|r| r.starts_with("cpred_h2_b")), "the head check at slot 2 is the failing step: {o:?}");
        // The user takes the pot net of the bisection's fees (about 25k sat
        // for ten rounds and a 6.7 kvB disproof at regtest fee rates), so
        // it ends above its starting balance and the hub below its own.
        ensure!(w.h.balance(Role::User) > sat(100_000), "user balance {}", w.h.balance(Role::User));
        ensure!(w.h.balance(Role::Hub) < sat(100_000) - STAKE, "hub balance {}", w.h.balance(Role::Hub));
        Ok(report(&w, &C7))
    },
};

pub const C8: Scenario = Scenario {
    id: "C8",
    title: "Chess: a garbage-signed entry is exhibited",
    expected: "the hub publishes a legal 1...e5 with one garbage preimage; the stall claim would count the slot as held, so the user exhibits the signature (sig_user, D31); the hub cannot dispute; after delta the split pays the user",
    run: || {
        let mut b = honest();
        b[Role::Hub.idx()].garbage_sig_at = Some(2);
        let mut w = ChessWorld::new("C8", b, 6)?;
        until_settled(&mut w)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(w.depth == 1 && c == 1);
        ensure!(m == vec!["sig_user".to_string()], "{m:?}");
        ensure!(s == vec!["sig_user/split_5_UserWins".to_string()], "{s:?}");
        ensure!(d.is_empty() && o.is_empty(), "{d:?} {o:?}");
        ensure!(w.h.balance(Role::User) > sat(100_000) + STAKE, "user balance {}", w.h.balance(Role::User));
        Ok(report(&w, &C8))
    },
};

pub const C9: Scenario = Scenario {
    id: "C9",
    title: "Chess: a baseless signature exhibit is disputed",
    expected: "the user exhibits the hub's soundly signed 1...e5 as garbage-signed; the exhibited digest equals the commitment, so the claim's first check fails; the hub disputes and wins the bisection at simple_pre_chk",
    run: || {
        let mut b = honest();
        b[Role::User.idx()].fabricate_sig_at = Some(2);
        let mut w = ChessWorld::new("C9", b, 6)?;
        w.step_until(200, |w| w.contract_txs().iter().any(|r| r.starts_with("cpred_") || r.starts_with("flat_") || r.starts_with("simple_") || r.contains("split_")))?;
        w.steps(2)?;
        let (c, m, s, d, o) = summary(&w);
        ensure!(c == 1);
        ensure!(m == vec!["sig_user".to_string()], "{m:?}");
        ensure!(s.is_empty() && d.is_empty(), "{s:?} {d:?}");
        ensure!(o.iter().any(|r| r == "sig_user/d5/dispute"), "the hub disputed: {o:?}");
        ensure!(o.iter().any(|r| r.starts_with("simple_pre_chk")), "the preamble check is the failing step: {o:?}");
        ensure!(w.h.balance(Role::Hub) > sat(100_000), "hub balance {}", w.h.balance(Role::Hub));
        ensure!(w.h.balance(Role::User) < sat(100_000) - STAKE, "user balance {}", w.h.balance(Role::User));
        Ok(report(&w, &C9))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![C1, C2, C3, C4, C5, C6, C7, C8, C9]
}
