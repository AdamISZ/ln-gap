//! Scenario definitions shared by the tests and the runner binary. Each
//! scenario drives a fresh harness, asserts the plan's expected outcome, and
//! returns a report for `docs/SCENARIOS.md`.

pub mod names;
pub mod fc_names;
pub mod fc_game;
pub mod fc_stall;
pub mod fc_chess;
pub mod tictactoe;

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::Role;

use crate::{Harness, FUNDING};

#[derive(Clone, Debug)]
pub struct Report {
    pub id: String,
    pub title: String,
    pub expected: String,
    /// (height, role, txid, broadcaster)
    pub txs: Vec<(u32, String, String, String)>,
    pub balances: [Amount; 2],
    pub narrative: String,
}

pub struct Scenario {
    pub id: &'static str,
    pub title: &'static str,
    pub expected: &'static str,
    pub run: fn() -> Result<Report>,
}

impl Report {
    pub fn from_harness(h: &Harness, id: &str, title: &str, expected: &str) -> Report {
        Report {
            id: id.into(),
            title: title.into(),
            expected: expected.into(),
            txs: h.seen.iter().map(|s| (s.height, s.role.clone(), s.txid.to_string(), s.by.map(|r| r.name().to_string()).unwrap_or_else(|| "harness".into()))).collect(),
            balances: [h.balance(Role::User), h.balance(Role::Hub)],
            narrative: h.narrative(),
        }
    }
}

/// Cross-cutting assertions (plan §8.3): every party transaction paid the
/// fixed fee, so final balances + fees == funding; single-signer
/// transactions are only disproofs and sweeps.
pub fn assert_cross_cutting(h: &Harness) {
    h.assert_signing_rule();
    let n = h.seen.iter().filter(|s| s.by.is_some()).count() as u64;
    let u = h.balance(Role::User);
    let b = h.balance(Role::Hub);
    assert_eq!(u + b + Amount::from_sat(1_000) * n, FUNDING, "balances {u} + {b} + {n} × 1000 sat fees != funding");
}

pub fn all() -> Vec<Scenario> {
    let mut v = tictactoe::scenarios();
    v.extend(names::scenarios());
    v.extend(fc_names::scenarios());
    v.extend(fc_game::scenarios());
    v.extend(fc_stall::scenarios());
    v.extend(fc_chess::scenarios());
    v
}
