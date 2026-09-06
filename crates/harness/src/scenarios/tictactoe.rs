//! Plan §8.1: T1–T9 (with T6 split into a status fraud and a code fraud;
//! see DECISIONS.md D9).

use std::sync::Arc;

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::protocol::Closing;
use lngap_channel::Role;
use lngap_contract::{Claim, Contract, Program};
use lngap_tictactoe::{Board, TicTacToe, O_WON};

use super::{assert_cross_cutting, Report, Scenario};
use crate::Harness;

const STAKE: Amount = Amount::from_sat(10_000);
const K: u64 = 1_000;
fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

/// Fresh harness with the reference game queued: U:4 H:1 U:0 H:8 U:6 H:3 U:2.
fn setup(label: &str) -> Result<Harness> {
    let programs: Vec<Arc<dyn Program>> = vec![Arc::new(TicTacToe)];
    let mut h = Harness::new(label, programs)?;
    let mv = |c: u8| Contract::move_bits(&TicTacToe, &c);
    h.user.queue_moves(1, vec![mv(4), mv(0), mv(6), mv(2)]);
    h.hub.queue_moves(1, vec![mv(1), mv(8), mv(3)]);
    let msgs = h.user.open_contract(1, TicTacToe::NAME, [STAKE, STAKE])?;
    h.bus(msgs)?;
    assert_eq!(h.user.channel.current_seq(), 1);
    Ok(h)
}

fn board_of(bits: &[bool]) -> Board {
    Contract::state_from_bits(&TicTacToe, bits).unwrap()
}
fn bits_of(b: &Board) -> Vec<bool> {
    Contract::state_bits(&TicTacToe, b)
}

fn heights(h: &Harness, role: &str) -> Vec<u32> {
    h.seen.iter().filter(|s| s.role == role).map(|s| s.height).collect()
}
fn moves_seen(h: &Harness) -> Vec<String> {
    h.roles_seen().into_iter().filter(|r| r.starts_with("move_")).collect()
}
fn finish(h: &Harness, id: &str, title: &str, expected: &str) -> Report {
    assert_cross_cutting(h);
    let r = Report::from_harness(h, id, title, expected);
    println!("{}", r.narrative);
    r
}

pub const T1: Scenario = Scenario {
    id: "T1",
    title: "Full game cooperative; final update folds V to user; cooperative close",
    expected: "funding tx + 1 close tx only; user 110k, hub 90k",
    run: || {
        let mut h = setup("T1")?;
        h.settle_offchain()?;
        let st = h.user.channel.current_state().clone();
        assert!(st.contracts.is_empty());
        assert_eq!(st.seq, 9, "open + 7 moves + resolve");
        assert_eq!(st.balances, [sat(110_000), sat(90_000)]);
        let msgs = h.user.propose_close()?;
        h.bus(msgs)?;
        h.step()?;
        assert_eq!(h.roles_seen(), ["coop_close"]);
        assert_eq!(h.balance(Role::User), sat(110_000 - 500));
        assert_eq!(h.balance(Role::Hub), sat(90_000 - 500));
        Ok(finish(&h, T1.id, T1.title, T1.expected))
    },
};

pub const T2: Scenario = Scenario {
    id: "T2",
    title: "Hub stops signing after U's move 5; user force-closes and plays on-chain; hub plays Move_2 on-chain then goes silent",
    expected: "commitment, 3 Moves, Split_UserWins after Delta+Delta'; user gets 20k + to_user",
    run: || {
        let mut h = setup("T2")?;
        h.hub.faults.stop_from_seq = Some(5);
        h.step_until(120, |h| h.roles_seen().iter().any(|r| r.starts_with("split_")))?;
        h.steps(2)?;
        assert!(matches!(h.user.closing(), Some(Closing::Local { seq: 5, .. })));
        assert_eq!(moves_seen(&h), ["move_1", "move_2", "move_3"]);
        assert_eq!(heights(&h, "split_3_UserWins").len(), 1);
        let m3 = heights(&h, "move_3")[0];
        let sp = heights(&h, "split_3_UserWins")[0];
        assert_eq!(sp - m3, u32::from(h.params().delta + h.params().delta_prime), "user is the prover at depth 3 and UserWins favours it");
        assert_eq!(h.balance(Role::User), sat(90_000 - K - K + 20_000 - 4 * K));
        assert_eq!(h.balance(Role::Hub), sat(90_000 - K));
        Ok(finish(&h, T2.id, T2.title, T2.expected))
    },
};

pub const T3: Scenario = Scenario {
    id: "T3",
    title: "As T2 but hub silent after Move_1",
    expected: "commitment, Move_1, Split_UserWins after Delta+Delta'; user 20k",
    run: || {
        let mut h = setup("T3")?;
        h.hub.faults.stop_from_seq = Some(5);
        h.hub.faults.passive_onchain = true;
        h.step_until(120, |h| h.roles_seen().iter().any(|r| r.starts_with("split_")))?;
        h.steps(2)?;
        assert_eq!(moves_seen(&h), ["move_1"]);
        let m1 = heights(&h, "move_1")[0];
        let sp = heights(&h, "split_1_UserWins")[0];
        assert_eq!(sp - m1, u32::from(h.params().delta + h.params().delta_prime));
        assert_eq!(h.balance(Role::User), sat(90_000 - K - K + 20_000 - 2 * K));
        assert_eq!(h.balance(Role::Hub), sat(90_000 - K));
        Ok(finish(&h, T3.id, T3.title, T3.expected))
    },
};

/// Run a T4/T5/T6-style scenario: hub cheats in its on-chain Move_2 and the
/// user disproves with the named leaf.
fn cheat_scenario(id: &'static str, sc: &Scenario, cheat: Arc<dyn Fn(&Claim) -> Claim + Send + Sync>, leaf: &str) -> Result<Report> {
    let mut h = setup(id)?;
    h.hub.faults.stop_from_seq = Some(5);
    h.hub.faults.cheat_move = Some(cheat);
    h.step_until(120, |h| h.roles_seen().iter().any(|r| r.starts_with("disprove_")))?;
    h.steps(2)?;
    assert_eq!(moves_seen(&h), ["move_1", "move_2"]);
    let roles = h.roles_seen();
    let d = roles.iter().find(|r| r.starts_with("disprove_")).unwrap();
    assert_eq!(d, leaf, "{roles:?}");
    assert!(!roles.iter().any(|r| r.starts_with("split_")));
    // the disproof is not timelocked: it confirms in the block after Move_2
    assert_eq!(heights(&h, leaf)[0], heights(&h, "move_2")[0] + 1);
    assert_eq!(h.balance(Role::User), sat(90_000 - K - K + 20_000 - 3 * K), "user receives the contract value immediately");
    assert_eq!(h.balance(Role::Hub), sat(90_000 - K));
    Ok(finish(&h, sc.id, sc.title, sc.expected))
}

pub const T4: Scenario = Scenario {
    id: "T4",
    title: "As T2 but hub's Move_2 claims m = 6 (occupied by X), overwriting it with O",
    expected: "commitment, Move_1, Move_2, disprove_cell_occupied_6; user receives 20k immediately",
    run: || {
        cheat_scenario("T4", &T4, Arc::new(|c: &Claim| {
            let mut b = board_of(&c.prior);
            b.cells[6] = 2;
            b.turn = Role::User;
            Claim { mv: Contract::move_bits(&TicTacToe, &6), new: bits_of(&b), code: TicTacToe::HUB_WINS, ..c.clone() }
        }), "disprove_cell_occupied_6")
    },
};

pub const T5: Scenario = Scenario {
    id: "T5",
    title: "Hub's move is legal (m = 3) but the committed board shows an extra O on cell 5",
    expected: "disprove_board_mismatch_5",
    run: || {
        cheat_scenario("T5", &T5, Arc::new(|c: &Claim| {
            let mut b = board_of(&c.new);
            b.cells[5] = 2;
            Claim { new: bits_of(&b), ..c.clone() }
        }), "disprove_board_mismatch_5")
    },
};

pub const T6: Scenario = Scenario {
    id: "T6",
    title: "Hub commits a legal move and board but claims the game is won by O (status), code HubWins",
    expected: "disprove_status_mismatch (D9: the plan's 'code HubWins' is the honest code here, since the user is on turn and would forfeit)",
    run: || {
        cheat_scenario("T6", &T6, Arc::new(|c: &Claim| {
            let mut b = board_of(&c.new);
            b.status = O_WON;
            Claim { new: bits_of(&b), code: TicTacToe::HUB_WINS, ..c.clone() }
        }), "disprove_status_mismatch")
    },
};

pub const T6B: Scenario = Scenario {
    id: "T6b",
    title: "Hub commits a legal move and board but an outcome code (Draw) inconsistent with R(s')",
    expected: "disprove_code_mismatch",
    run: || {
        cheat_scenario("T6b", &T6B, Arc::new(|c: &Claim| Claim { code: TicTacToe::DRAW, ..c.clone() }), "disprove_code_mismatch")
    },
};

pub const T7: Scenario = Scenario {
    id: "T7",
    title: "Hub broadcasts the commitment for state 3 after the game is over and state 9 is signed",
    expected: "user sweeps to_hub and C_3 via revocation within 6 blocks; user ends with 200k − fees",
    run: || {
        let mut h = setup("T7")?;
        h.settle_offchain()?;
        assert_eq!(h.user.channel.current_seq(), 9);
        h.hub.channel.force_close_at(3)?;
        let h0 = h.step()?;
        assert!(matches!(h.user.closing(), Some(Closing::Remote { seq: 3, revoked: true, .. })));
        h.steps(8)?;
        let sweep = heights(&h, "revoke_sweep_3");
        assert_eq!(sweep.len(), 1);
        assert!(sweep[0] <= h0 + 6, "penalty within to_self_delay");
        assert_eq!(h.balance(Role::User), sat(200_000 - K - K));
        assert_eq!(h.balance(Role::Hub), Amount::ZERO);
        Ok(finish(&h, T7.id, T7.title, T7.expected))
    },
};

pub const T8: Scenario = Scenario {
    id: "T8",
    title: "User stalls after U:0 (mirror of T3): hub force-closes, plays Move_1(8); user silent on-chain",
    expected: "hub wins by forfeit via Split_HubWins off the hub's Move after Delta+Delta'",
    run: || {
        let mut h = setup("T8")?;
        h.user.faults.stop_from_seq = Some(4);
        h.user.faults.passive_onchain = true;
        h.step_until(120, |h| h.roles_seen().iter().any(|r| r.starts_with("split_")))?;
        h.steps(2)?;
        assert!(matches!(h.hub.closing(), Some(Closing::Local { seq: 4, .. })));
        assert_eq!(moves_seen(&h), ["move_1"]);
        let m1 = heights(&h, "move_1")[0];
        let sp = heights(&h, "split_1_HubWins")[0];
        assert_eq!(sp - m1, u32::from(h.params().delta + h.params().delta_prime));
        assert_eq!(h.balance(Role::Hub), sat(90_000 - K - K + 20_000 - 2 * K));
        assert_eq!(h.balance(Role::User), sat(90_000 - K));
        Ok(finish(&h, T8.id, T8.title, T8.expected))
    },
};

pub const T9: Scenario = Scenario {
    id: "T9",
    title: "Hub force-closes while it is the user's turn; user does nothing",
    expected: "Settle pays R(s) = hub wins (user forfeits) after the deadline (liveness rule; see DECISIONS.md TODO)",
    run: || {
        let mut h = setup("T9")?;
        h.user.faults.stop_from_seq = Some(5);
        h.user.faults.passive_onchain = true;
        h.settle_offchain()?;
        assert_eq!(h.user.channel.current_seq(), 5, "user on turn at state 5");
        let deadline = lngap_party::draft::downcast(&h.hub.channel.current_state().contracts[0]).deadline;
        h.hub.channel.force_close()?;
        h.step_until(120, |h| h.roles_seen().iter().any(|r| r == "settle"))?;
        h.steps(2)?;
        assert!(moves_seen(&h).is_empty());
        assert!(heights(&h, "settle")[0] > deadline);
        assert_eq!(h.balance(Role::Hub), sat(90_000 - K - K + 20_000 - K));
        assert_eq!(h.balance(Role::User), sat(90_000 - K));
        Ok(finish(&h, T9.id, T9.title, T9.expected))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![T1, T2, T3, T4, T5, T6, T6B, T7, T8, T9]
}
