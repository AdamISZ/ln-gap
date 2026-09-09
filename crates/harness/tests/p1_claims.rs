//! Phase 1 of the SPV dispute path: bisection over a 16-step hash chain on
//! regtest. Honest claim paid; false end state disproved at the last step;
//! false midstate disproved mid-chain; prover silent -> timeout; griefing
//! challenger silent -> prover timeout; griefing challenger plays it out ->
//! the step is correct and the prover times it out.

use std::sync::Arc;

use bitcoin::Amount;
use lngap_channel::Role;
use lngap_contract::toy::HashChain;
use lngap_contract::{Program, ProgramRegistry};
use lngap_harness::Harness;

const STAKE: Amount = Amount::from_sat(50_000);
const K: u64 = 1_000;
fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

fn setup(label: &str) -> Harness {
    let mut h = Harness::new(label, ProgramRegistry::new().with(Arc::new(HashChain::standard()) as Arc<dyn Program>)).unwrap();
    h.user.queue_moves(1, vec![vec![true]]);
    // hub non-cooperative from the start so the claim goes on-chain
    let msgs = h.user.open_contract(1, HashChain::NAME, [STAKE, STAKE]).unwrap();
    h.bus(msgs).unwrap();
    h.hub.faults.stop_from_seq = Some(1);
    h
}

fn roles(h: &Harness) -> Vec<String> {
    h.roles_seen()
}

/// Value the challenger's step transaction paid out (the contract minus fees).
fn step_output(h: &Harness) -> Amount {
    let s = h.seen.iter().find(|s| s.role.starts_with("step_")).unwrap();
    h.rt.get_tx(&s.txid).unwrap().output[0].value
}

#[test]
fn honest_claim_is_paid_without_dispute() {
    let mut h = setup("p1-honest");
    h.step_until(80, |h| roles(h).iter().any(|r| r.starts_with("split_"))).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.contains(&"move_1".to_string()) && r.contains(&"split_1_Paid".to_string()), "{r:?}");
    assert!(!r.iter().any(|x| x == "dispute"));
    assert_eq!(h.balance(Role::User), sat(50_000 - K - K + 100_000 - 2 * K));
    println!("{}", h.narrative());
}

#[test]
fn false_end_state_is_disproved_at_the_last_step() {
    let mut h = setup("p1-badend");
    h.user.faults.cheat_claim = Some(Arc::new(|s: &[u32; 8]| { let mut t = *s; t[0] ^= 1; t }));
    h.step_until(120, |h| roles(h).iter().any(|r| r.starts_with("step_"))).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert_eq!(r.iter().filter(|x| x.starts_with("p_round_")).count(), 2, "{r:?}");
    assert_eq!(r.iter().filter(|x| x.starts_with("q_round_")).count(), 2, "{r:?}");
    assert!(r.iter().any(|x| x.starts_with("step_")), "path 3,3 isolates step 15: {r:?}");
    assert!(h.hub.narrative().iter().any(|l| l.contains("step 15 is wrong")), "the hub isolated step 15");
    // hub takes the contract: 100k - move - dispute - 4 rounds, minus the size-based fee of the step tx
    let step_out = step_output(&h);
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K) + step_out);
    assert!(step_out > sat(100_000 - 6 * K - 12_000) && step_out < sat(100_000 - 6 * K), "step tx fee is ~10k sat: {step_out}");
    assert_eq!(h.balance(Role::User), sat(50_000 - K - K));
    println!("{}", h.narrative());
}

#[test]
fn false_midstate_is_disproved_mid_chain() {
    let mut h = setup("p1-badmid");
    // the prover's "computation" goes wrong from step 6 on, and it claims the end state of that computation
    let bad = |i: u32, s: &[u32; 8]| { let mut t = *s; if i >= 6 { t[3] ^= 0x40; } t };
    h.user.faults.cheat_midstates = Some(Arc::new(bad));
    h.user.faults.cheat_claim = Some(Arc::new(move |s: &[u32; 8]| bad(16, s)));
    h.step_until(120, |h| roles(h).iter().any(|r| r.starts_with("step_"))).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.iter().any(|x| x.starts_with("step_")), "{r:?}");
    assert!(h.hub.narrative().iter().any(|l| l.contains("step 5 is wrong")), "segment 1 of round 1 (steps 4..8), then segment 1 (step 5)");
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K) + step_output(&h));
    println!("{}", h.narrative());
}

#[test]
fn silent_prover_is_timed_out() {
    let mut h = setup("p1-silentp");
    h.user.faults.cheat_claim = Some(Arc::new(|s: &[u32; 8]| { let mut t = *s; t[7] ^= 2; t }));
    h.user.faults.silent_in_rounds = true;
    h.step_until(80, |h| roles(h).iter().any(|r| r == "dispute_timeout")).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.contains(&"d1/dispute".to_string()) && !r.iter().any(|x| x.starts_with("p_round_")), "{r:?}");
    let d = h.seen.iter().find(|s| s.role == "d1/dispute").unwrap().height;
    let t = h.seen.iter().find(|s| s.role == "dispute_timeout").unwrap().height;
    assert_eq!(t - d, u32::from(h.params().delta));
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K + 100_000 - 3 * K));
    println!("{}", h.narrative());
}

#[test]
fn griefing_challenger_silent_is_timed_out() {
    let mut h = setup("p1-griefsilent");
    h.hub.faults.dispute_anyway = true;
    h.hub.faults.silent_in_rounds = true;
    h.step_until(80, |h| roles(h).iter().any(|r| r == "dispute_timeout")).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.contains(&"p_round_1".to_string()) && !r.iter().any(|x| x.starts_with("q_round_")), "{r:?}");
    // user keeps the contract: 100k - move - dispute - p_round_1 - timeout
    assert_eq!(h.balance(Role::User), sat(50_000 - K - K + 100_000 - 4 * K));
    println!("{}", h.narrative());
}

#[test]
fn griefing_challenger_plays_out_and_loses_at_the_step() {
    let mut h = setup("p1-griefplay");
    h.hub.faults.dispute_anyway = true;
    h.step_until(120, |h| roles(h).iter().any(|r| r == "dispute_timeout")).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert_eq!(r.iter().filter(|x| x.starts_with("q_round_")).count(), 2, "{r:?}");
    assert!(!r.iter().any(|x| x.starts_with("step_")), "no step can be disproved: {r:?}");
    assert_eq!(h.balance(Role::User), sat(50_000 - K - K + 100_000 - 7 * K));
    println!("{}", h.narrative());
}
