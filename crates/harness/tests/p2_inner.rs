//! Phase 2 of the SPV dispute path: the two-level search. Level 1 bisects
//! the 16-step hash chain to one compression; the prover then publishes the
//! schedule words and the search continues over the 64 rounds (k = 8), ending
//! in a single-round disprove leaf of a few kvB instead of a 96 kvB
//! compression leaf.

use std::sync::Arc;

use bitcoin::Amount;
use lngap_channel::Role;
use lngap_contract::inner::{round_states, schedule};
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
    let msgs = h.user.open_contract(1, HashChain::NAME, [STAKE, STAKE]).unwrap();
    h.bus(msgs).unwrap();
    h.hub.faults.stop_from_seq = Some(1);
    h
}

fn roles(h: &Harness) -> Vec<String> {
    h.roles_seen()
}

/// Value the challenger's disproof transaction paid out.
fn disproof_output(h: &Harness) -> Amount {
    output_of(h, |r| r.starts_with("round_") || r.starts_with("sched_"))
}

/// Output value of the first seen transaction whose role matches.
fn output_of(h: &Harness, f: impl Fn(&str) -> bool) -> Amount {
    let s = h.seen.iter().find(|s| f(&s.role)).unwrap();
    h.rt.get_tx(&s.txid).unwrap().output[0].value
}

fn sizes(h: &Harness) -> String {
    h.seen.iter().map(|s| format!("{} {} vB", s.role, s.vsize)).collect::<Vec<_>>().join("; ")
}

const INNER_CHAIN: [&str; 7] = ["p_re_cur", "p_re_next", "p_sched", "p_inner_1", "q_inner_1", "p_inner_2", "q_inner_2"];

#[test]
fn honest_claim_is_paid_without_dispute() {
    let mut h = setup("p2-honest");
    h.step_until(80, |h| roles(h).iter().any(|r| r.starts_with("split_"))).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.contains(&"move_1".to_string()) && r.contains(&"split_1_Paid".to_string()), "{r:?}");
    assert!(!r.iter().any(|x| x == "dispute"));
    assert_eq!(h.balance(Role::User), sat(50_000 - K - K + 100_000 - 2 * K));
    println!("{}", h.narrative());
}

#[test]
fn false_end_state_is_disproved_at_round_63() {
    let mut h = setup("p2-badend");
    h.user.faults.cheat_claim = Some(Arc::new(|s: &[u32]| { let mut t = s.to_vec(); t[0] ^= 1; t }));
    h.step_until(160, |h| roles(h).iter().any(|r| r.starts_with("round_"))).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    for name in INNER_CHAIN {
        assert!(r.contains(&name.to_string()), "{name} missing: {r:?}");
    }
    assert!(!r.iter().any(|x| x.starts_with("step_")), "no compression-level leaf: {r:?}");
    assert!(h.hub.narrative().iter().any(|l| l.contains("round 63 is wrong")), "the hub isolated round 63 (feed-forward)");
    let out = disproof_output(&h);
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K) + out);
    // contract 100k minus move, dispute, 4 level-1 rounds, 5 inner-chain txs (three of them
    // paying ~2.4k by size), and the size-based fee of the round tx: well under 10k in all
    assert!(out > sat(100_000 - 25 * K) && out < sat(100_000 - 13 * K), "fees along the whole dispute are small: {out}");
    assert_eq!(h.balance(Role::User), sat(50_000 - K - K));
    println!("{}", h.narrative());
    println!("SIZES {}", sizes(&h));
}

#[test]
fn false_schedule_word_is_disproved() {
    let mut h = setup("p2-badsched");
    h.user.faults.cheat_claim = Some(Arc::new(|s: &[u32]| { let mut t = s.to_vec(); t[2] ^= 0x10; t }));
    h.user.faults.cheat_schedule = Some(Arc::new(|i: u32, w: u32| if i == 40 { w ^ 0x0100_0000 } else { w }));
    h.step_until(160, |h| roles(h).iter().any(|r| r.starts_with("sched_"))).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.contains(&"p_inner_1".to_string()) && !r.contains(&"q_inner_1".to_string()), "the schedule disproof replaces the first inner index: {r:?}");
    assert!(h.hub.narrative().iter().any(|l| l.contains("schedule word 40 is wrong")));
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K) + disproof_output(&h));
    println!("{}", h.narrative());
    println!("SIZES {}", sizes(&h));
}

#[test]
fn false_inner_state_is_disproved_mid_compression() {
    let mut h = setup("p2-badinner");
    // the prover's computation of step 15 goes wrong at round 30 and the error
    // propagates; it claims the resulting end state (so level 1 isolates step 15)
    let bad = |i: u32, s: &[u32; 8]| { let mut t = *s; if i == 30 { t[6] ^= 0x8000; } t };
    let prog = HashChain::standard();
    let states = prog.spec.states(&vec![]);
    let s15: [u32; 8] = states[15][..].try_into().unwrap();
    let cheated_end = round_states(&s15, &schedule(&prog.block()), Some(&bad))[64].to_vec();
    assert_ne!(cheated_end, states[16]);
    h.user.faults.cheat_claim = Some(Arc::new(move |_s: &[u32]| cheated_end.clone()));
    h.user.faults.cheat_inner = Some(Arc::new(bad));
    h.step_until(160, |h| roles(h).iter().any(|r| r.starts_with("round_"))).unwrap();
    h.steps(2).unwrap();
    let hub = h.hub.narrative();
    assert!(hub.iter().any(|l| l.contains("inner round 1: first bad segment is 3")), "s_32 is the first wrong boundary");
    assert!(hub.iter().any(|l| l.contains("inner round 2: first bad segment is 5")), "s_30 is the first wrong state in rounds 24..32");
    assert!(hub.iter().any(|l| l.contains("round 29 is wrong")), "round 29 maps s_29 to s_30");
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K) + disproof_output(&h));
    println!("{}", h.narrative());
}

#[test]
fn prover_silent_at_inner_level_is_timed_out() {
    let mut h = setup("p2-silentinner");
    h.user.faults.cheat_claim = Some(Arc::new(|s: &[u32]| { let mut t = s.to_vec(); t[7] ^= 2; t }));
    h.user.faults.silent_in_inner = true;
    h.step_until(160, |h| roles(h).iter().any(|r| r == "dispute_timeout")).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert_eq!(r.iter().filter(|x| x.starts_with("q_round_")).count(), 2, "{r:?}");
    assert!(!r.contains(&"p_re_cur".to_string()), "{r:?}");
    let q = h.seen.iter().find(|s| s.role == "q_round_2").unwrap().height;
    let t = h.seen.iter().find(|s| s.role == "dispute_timeout").unwrap().height;
    assert_eq!(t - q, u32::from(h.params().delta));
    // hub: 100k - move - dispute - 4 rounds - timeout
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K + 100_000 - 7 * K));
    println!("{}", h.narrative());
}

#[test]
fn griefing_challenger_plays_out_to_the_round_and_loses() {
    let mut h = setup("p2-griefplay");
    h.hub.faults.dispute_anyway = true;
    h.step_until(200, |h| roles(h).iter().any(|r| r == "dispute_timeout")).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    for name in INNER_CHAIN {
        assert!(r.contains(&name.to_string()), "{name} missing: {r:?}");
    }
    assert!(!r.iter().any(|x| x.starts_with("round_") || x.starts_with("sched_")), "nothing can be disproved: {r:?}");
    assert!(h.hub.narrative().iter().any(|l| l.contains("isolated round 63 is correct")));
    // user keeps the contract: 100k - move - dispute - 4 rounds - 7 inner txs (size-based fees) - timeout
    let out = output_of(&h, |r| r == "dispute_timeout");
    assert!(out > sat(100_000 - 25 * K) && out < sat(100_000 - 14 * K), "{out}");
    assert_eq!(h.balance(Role::User), sat(50_000 - K - K) + out);
    println!("SIZES {}", sizes(&h));
    println!("{}", h.narrative());
}
