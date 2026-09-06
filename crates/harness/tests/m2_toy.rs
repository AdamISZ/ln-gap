//! M2 scenarios on the coin-flip toy: cooperative play, and every dispute
//! path (settle by deadline, force-move chain, split after silence,
//! disproof of an invalid on-chain move, penalty with a contract output).

use std::sync::Arc;

use bitcoin::Amount;
use lngap_channel::protocol::Closing;
use lngap_channel::Role;
use lngap_contract::toy::CoinFlip;
use lngap_contract::{Claim, Program};
use lngap_harness::{Harness, FUNDING};

fn programs() -> Vec<Arc<dyn Program>> {
    vec![Arc::new(CoinFlip)]
}
const STAKE: Amount = Amount::from_sat(10_000);
const K: u64 = 1_000;

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

/// Open the contract and queue both parties' bits.
fn open(h: &mut Harness, user_bit: bool, hub_bit: bool) {
    h.user.queue_moves(1, vec![vec![user_bit]]);
    h.hub.queue_moves(1, vec![vec![hub_bit]]);
    let msgs = h.user.open_contract(1, CoinFlip::NAME, [STAKE, STAKE]).unwrap();
    h.bus(msgs).unwrap();
    assert_eq!(h.user.channel.current_seq(), 1);
    assert_eq!(h.user.channel.current_state().contracts.len(), 1);
}

#[test]
fn c1_cooperative_flip_then_close() {
    let mut h = Harness::new("c1", programs()).unwrap();
    open(&mut h, true, false); // xor = 1 → hub wins
    h.settle_offchain().unwrap(); // user reveals, hub reveals, contract resolved
    let st = h.user.channel.current_state().clone();
    assert!(st.contracts.is_empty(), "contract folded into balances");
    assert_eq!(st.balances, [sat(90_000), sat(110_000)]);
    assert_eq!(st.seq, 4, "open, user move, hub move, resolve");
    let msgs = h.user.propose_close().unwrap();
    h.bus(msgs).unwrap();
    h.step().unwrap();
    assert_eq!(h.roles_seen(), ["coop_close"]);
    assert_eq!(h.balance(Role::User), sat(90_000 - 500));
    assert_eq!(h.balance(Role::Hub), sat(110_000 - 500));
    h.assert_signing_rule();
    println!("{}", h.narrative());
}

#[test]
fn c2_hub_stalls_before_moving_user_settles_by_deadline() {
    // user reveals off-chain (seq 2); hub's turn; hub goes dark and never
    // moves on-chain either. User force-closes; after the deadline Settle
    // pays R(s) = UserWins (hub forfeits).
    let mut h = Harness::new("c2", programs()).unwrap();
    open(&mut h, true, false);
    h.hub.faults.stop_from_seq = Some(2);
    h.hub.faults.passive_onchain = true;
    h.settle_offchain().unwrap();
    assert_eq!(h.user.channel.current_seq(), 2, "user's reveal signed; hub then silent");
    let deadline = lngap_party::draft::downcast(&h.user.channel.current_state().contracts[0]).deadline;
    // the user proposes nothing more (hub's turn); hub misses the deadline off-chain → user force-closes
    h.step_until(60, |h| matches!(h.user.closing(), Some(Closing::Local { confirmed_at: Some(_), .. }))).unwrap();
    h.step_until(60, |h| h.roles_seen().iter().any(|r| r == "settle")).unwrap();
    h.steps(2).unwrap();
    let roles = h.roles_seen();
    assert!(roles.iter().any(|r| r.starts_with("commitment_2")), "{roles:?}");
    assert!(roles.iter().any(|r| r == "settle"), "{roles:?}");
    let settle = h.seen.iter().find(|s| s.role == "settle").unwrap();
    assert!(settle.height > deadline, "settle confirmed after the deadline");
    // user: 90k balance − commit fee − sweep fee, plus 20k − 1k from settle
    assert_eq!(h.balance(Role::User), sat(90_000 - K - K + 20_000 - K));
    assert_eq!(h.balance(Role::Hub), sat(90_000 - K));
    h.assert_signing_rule();
    println!("{}", h.narrative());
}

#[test]
fn c3_force_move_chain_on_chain() {
    // hub stops cooperating right after the contract opens (seq 1, user on
    // turn). User force-closes and reveals on-chain (Move_1); hub reveals
    // on-chain (Move_2); nobody can move further; Split pays the winner.
    let mut h = Harness::new("c3", programs()).unwrap();
    open(&mut h, true, true); // xor 0 → user wins
    h.hub.faults.stop_from_seq = Some(1);
    h.step_until(80, |h| h.roles_seen().iter().any(|r| r.starts_with("split_"))).unwrap();
    h.steps(2).unwrap();
    let roles = h.roles_seen();
    assert_eq!(roles.iter().filter(|r| r.starts_with("move_")).count(), 2, "{roles:?}");
    assert!(roles.iter().any(|r| r == "split_2_UserWins"), "{roles:?}");
    // window: depth-2 prover is the hub, UserWins does not favour it → Delta only
    let m2 = h.seen.iter().find(|s| s.role == "move_2").unwrap().height;
    let sp = h.seen.iter().find(|s| s.role == "split_2_UserWins").unwrap().height;
    assert_eq!(sp - m2, u32::from(h.params().delta));
    assert_eq!(h.balance(Role::User), sat(90_000 - K - K + 20_000 - 3 * K));
    assert_eq!(h.balance(Role::Hub), sat(90_000 - K));
    h.assert_signing_rule();
    println!("{}", h.narrative());
}

#[test]
fn c4_hub_silent_after_move_1() {
    let mut h = Harness::new("c4", programs()).unwrap();
    open(&mut h, false, true);
    h.hub.faults.stop_from_seq = Some(1);
    h.hub.faults.passive_onchain = true;
    h.step_until(80, |h| h.roles_seen().iter().any(|r| r.starts_with("split_"))).unwrap();
    h.steps(2).unwrap();
    let roles = h.roles_seen();
    assert_eq!(roles.iter().filter(|r| r.starts_with("move_")).count(), 1, "{roles:?}");
    // after the user's reveal R(s) = UserWins (hub on turn forfeits): prover-favourable → Delta + Delta'
    assert!(roles.iter().any(|r| r == "split_1_UserWins"), "{roles:?}");
    let m1 = h.seen.iter().find(|s| s.role == "move_1").unwrap().height;
    let sp = h.seen.iter().find(|s| s.role == "split_1_UserWins").unwrap().height;
    assert_eq!(sp - m1, u32::from(h.params().delta + h.params().delta_prime));
    assert_eq!(h.balance(Role::User), sat(90_000 - K - K + 20_000 - 2 * K));
    h.assert_signing_rule();
    println!("{}", h.narrative());
}

#[test]
fn c5_hub_cheats_on_chain_and_is_disproved() {
    for (label, cheat) in [
        ("code", Arc::new(|c: &Claim| Claim { code: CoinFlip::HUB_WINS, ..c.clone() }) as Arc<dyn Fn(&Claim) -> Claim + Send + Sync>),
        ("state", Arc::new(|c: &Claim| Claim { new: vec![true, false, true, false], ..c.clone() })),
    ] {
        let mut h = Harness::new(&format!("c5-{label}"), programs()).unwrap();
        open(&mut h, true, true); // honest outcome: xor 0 → user wins
        h.hub.faults.stop_from_seq = Some(1);
        h.hub.faults.cheat_move = Some(cheat);
        h.step_until(80, |h| h.roles_seen().iter().any(|r| r.starts_with("disprove_"))).unwrap();
        h.steps(2).unwrap();
        let roles = h.roles_seen();
        let d = roles.iter().find(|r| r.starts_with("disprove_")).unwrap();
        assert_eq!(d, &format!("disprove_{label}_mismatch"), "{roles:?}");
        assert!(!roles.iter().any(|r| r.starts_with("split_")));
        // user takes the whole contract value: 20k − move_1 fee − move_2 fee − disprove fee
        assert_eq!(h.balance(Role::User), sat(90_000 - K - K + 20_000 - 3 * K));
        assert_eq!(h.balance(Role::Hub), sat(90_000 - K));
        h.assert_signing_rule();
        println!("{}", h.narrative());
    }
}

#[test]
fn c6_revoked_state_with_contract_output_is_swept() {
    let mut h = Harness::new("c6", programs()).unwrap();
    open(&mut h, true, false);
    h.settle_offchain().unwrap(); // through to seq 4, contract resolved: user 90k, hub 110k
    assert_eq!(h.user.channel.current_seq(), 4);
    // hub broadcasts seq 2 (user revealed, contract output live, hub on turn)
    h.hub.channel.force_close_at(2).unwrap();
    h.step().unwrap();
    assert!(matches!(h.user.closing(), Some(Closing::Remote { revoked: true, .. })));
    h.steps(2).unwrap();
    assert!(h.roles_seen().iter().any(|r| r.starts_with("revoke_sweep")));
    assert_eq!(h.balance(Role::User), sat(FUNDING.to_sat() - K - K));
    assert_eq!(h.balance(Role::Hub), Amount::ZERO);
    h.assert_signing_rule();
    println!("{}", h.narrative());
}
