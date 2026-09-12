//! Fact-chain names scenarios: N1 (cooperative registration), N2 (hub doesn't submit),
//! N4 (cooperative sale). Stage 1: no on-chain bisection; proofs verified natively.

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::Role;
use lngap_harness::factchain_world::{FcWorld, GRACE};

const K: u64 = 1_000;
fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

fn party_txs(h: &lngap_harness::Harness) -> Vec<String> {
    h.seen
        .iter()
        .filter(|s| s.by.is_some())
        .map(|s| s.role.clone())
        .collect()
}

fn contracts(h: &lngap_harness::Harness) -> usize {
    h.user.channel.current_state().contracts.len()
}

fn balances(h: &lngap_harness::Harness) -> [Amount; 2] {
    h.user.channel.current_state().balances
}

/// Register `alice` cooperatively through to both folded bonds.
fn register_cooperatively(w: &mut FcWorld) -> Result<()> {
    w.register()?;
    w.step_until(60, |w| contracts(&w.alice) == 0 && w.resolve("alice") == Some(w.alice_key()))?;
    Ok(())
}

#[test]
fn n1_cooperative_registration() -> Result<()> {
    let mut w = FcWorld::new("FCN1")?;
    register_cooperatively(&mut w)?;

    // No channel transactions on-chain (all folded off-chain)
    assert!(party_txs(&w.alice).is_empty(), "no channel transaction on-chain");
    assert_eq!(balances(&w.alice), [sat(100_000), sat(100_000)]);

    // Registry shows alice -> K_A
    assert_eq!(w.resolve("alice"), Some(w.alice_key()));

    // Fact chain has blocks (at least commit + reveal)
    assert!(w.fc_height() >= 2, "fact chain has {} blocks", w.fc_height());

    println!("\n{}", w.narrative());
    Ok(())
}

#[test]
fn n2_hub_does_not_submit() -> Result<()> {
    let mut w = FcWorld::new("FCN2")?;
    w.hub.lock().unwrap().faults.no_submit = true;
    let r = w.register()?;

    // Hub stops signing after the bond opens
    w.alice.hub.faults.stop_from_seq = Some(1);

    // Step until Alice's claim is on-chain (after h_max + GRACE)
    w.step_until(200, |w| {
        party_txs(&w.alice).iter().any(|r| r.starts_with("split_"))
    })?;
    w.steps(2)?;

    let roles = party_txs(&w.alice);
    assert!(
        roles.iter().any(|r| r == "move_1"),
        "Alice claims: {roles:?}"
    );
    assert!(
        roles.iter().any(|r| r == "split_1_BondToUser"),
        "bond to user: {roles:?}"
    );

    // The claim happened after h_max + GRACE (CLTV)
    let m1 = w.alice.seen.iter().find(|s| s.role == "move_1").unwrap().height;
    assert!(m1 >= r.h_max + GRACE, "claim only after h_max + GRACE: m1={m1}, h_max+GRACE={}", r.h_max + GRACE);

    // Alice gets her bond
    assert!(w.alice.balance(Role::User) > sat(100_000), "Alice should gain the bond");

    println!("\n{}", w.narrative());
    Ok(())
}

#[test]
fn n4_cooperative_sale() -> Result<()> {
    let mut w = FcWorld::new("FCN4")?;
    register_cooperatively(&mut w)?;

    let h_sale = w.height() + 40;
    w.bob_offers(h_sale)?;
    w.alice_sells(h_sale)?;

    w.step_until(80, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;

    // Registry shows alice -> K_B
    assert_eq!(w.resolve("alice"), Some(w.bob_key()));

    // Balances: Bob -40k, Alice +40k, hub flat
    assert_eq!(balances(&w.alice), [sat(140_000), sat(60_000)]);
    assert_eq!(balances(&w.bob), [sat(60_000), sat(140_000)]);

    // No channel transactions
    assert!(party_txs(&w.alice).is_empty() && party_txs(&w.bob).is_empty());

    println!("\n{}", w.narrative());
    Ok(())
}
