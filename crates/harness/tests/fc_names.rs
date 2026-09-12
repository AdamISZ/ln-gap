//! Fact-chain names scenarios: N1–N7 (N8/N9 deferred to stage 2).
//! Stage 1: no on-chain bisection; proofs verified natively.

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::Role;
use lngap_harness::factchain_world::{
    FcWorld, GRACE, ID_BOND, ID_LEG2, ID_RBOND, ID_TBOND, PRICE, BOND, Who,
};
use lngap_party::MoveCtx;

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

#[test]
fn n3_false_claim_hub_proves_inclusion() -> Result<()> {
    let mut w = FcWorld::new("FCN3")?;
    let r = w.register()?;
    w.registering = false; // no reveal: just one bond

    // Alice's cheating policy: claim from claim_from no matter what, never fold
    let claim_from = r.h_max + GRACE;
    w.alice.user.set_move_policy(
        ID_BOND,
        Box::new(move |ctx: &MoveCtx| {
            (ctx.height >= claim_from && lngap_lamport::bits_to_uint(ctx.state) == 0)
                .then(|| vec![true])
        }),
    );
    w.alice.user.set_cancel_policy(ID_BOND, Box::new(|_| false));

    // Alice goes dark after proposing the claim so the hub must answer on-chain
    w.alice.user.faults.stop_from_seq = Some(2);

    // Step until the bond resolves on-chain
    w.step_until(200, |w| {
        party_txs(&w.alice).iter().any(|r| r.starts_with("split_"))
    })?;
    w.steps(2)?;

    let roles = party_txs(&w.alice);
    // Alice claims (move_1), hub answers by broadcasting its commitment,
    // bond resolves to hub
    assert!(
        roles.iter().any(|r| r == "move_1"),
        "Alice claims: {roles:?}"
    );
    assert!(
        roles.iter().any(|r| r.starts_with("commitment_") || r.starts_with("move_")),
        "hub answers on-chain: {roles:?}"
    );
    assert!(
        roles.iter().any(|r| r == "split_1_BondToHub"),
        "bond to hub: {roles:?}"
    );

    // Bond resolved to hub. The exact balance depends on fee accounting
    // for the force-close transactions. Just verify the bond went to hub
    // (not to user) and Alice didn't gain anything.
    let user_bal = w.alice.balance(Role::User).to_sat();
    assert!(
        user_bal < 100_000,
        "Alice should not gain the bond: {user_bal}"
    );

    println!("\n{}", w.narrative());
    Ok(())
}

#[test]
fn n5_alice_never_signs_transfer() -> Result<()> {
    let mut w = FcWorld::new("FCN5")?;
    register_cooperatively(&mut w)?;

    let h_sale = w.height() + 15;
    w.bob_offers(h_sale)?;

    w.step_until(30, |w| w.height() >= h_sale)?;

    assert_eq!(contracts(&w.bob), 0, "no contracts opened");
    assert_eq!(balances(&w.bob), [sat(100_000), sat(100_000)]);
    assert_eq!(w.resolve("alice"), Some(w.alice_key()));
    assert!(party_txs(&w.bob).is_empty());

    println!("\n{}", w.narrative());
    Ok(())
}

#[test]
fn n6_hub_refuses_to_submit_transfer() -> Result<()> {
    let mut w = FcWorld::new("FCN6")?;
    register_cooperatively(&mut w)?;

    let h_sale = w.height() + 30;
    w.bob_offers(h_sale)?;
    // Set no_submit BEFORE alice_sells so the transfer entry is never queued
    w.hub.lock().unwrap().faults.no_submit = true;
    w.alice_sells(h_sale)?;
    // Clear any entry that was queued before the fault was set
    w.pending_entry = None;

    w.step_until(200, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;

    // Bob refunded (leg 1 folds, no proof of inclusion)
    assert_eq!(balances(&w.bob), [sat(100_000), sat(100_000)]);
    // Alice keeps the name (transfer never anchored)
    assert_eq!(w.resolve("alice"), Some(w.alice_key()));
    // The legs and transfer bond all folded cooperatively (no on-chain dispute)
    assert!(party_txs(&w.alice).is_empty() && party_txs(&w.bob).is_empty());

    println!("\n{}", w.narrative());
    Ok(())
}

#[test]
fn n7_hub_proves_onchain_refuses_alice() -> Result<()> {
    let mut w = FcWorld::new("FCN7")?;
    register_cooperatively(&mut w)?;

    let h_sale = w.height() + 70;
    w.bob_offers(h_sale)?;
    w.alice_sells(h_sale)?;

    w.bob.user.faults.stop_from_seq = Some(1);
    w.bob.user.faults.passive_onchain = true;

    w.set_hub_policy(Who::Alice, Some(Box::new(|ctx: &lngap_party::ChangeCtx| {
        if let lngap_party::draft::Change::Move { id, .. } = ctx.change {
            if *id == ID_LEG2 {
                anyhow::bail!("hub refuses to pay Alice");
            }
        }
        Ok(())
    })));

    // Step until Bob's leg resolves (hub proves inclusion on-chain)
    w.step_until(200, |w| {
        party_txs(&w.bob).iter().any(|r| r == "split_1_Paid")
    })?;
    // Give time for the rest to settle
    w.steps(20)?;

    let bob_roles = party_txs(&w.bob);
    assert!(
        bob_roles.iter().any(|r| r == "move_1") || bob_roles.iter().any(|r| r == "split_1_Paid"),
        "Bob's channel: {bob_roles:?}"
    );

    assert_eq!(w.resolve("alice"), Some(w.bob_key()));

    println!("\n{}", w.narrative());
    Ok(())
}
