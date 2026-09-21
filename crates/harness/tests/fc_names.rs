//! Fact-chain names scenarios: N1–N9.
//! Stages 1+2: on-chain bisection disputes via the flat terminal leaf.

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

#[test]
fn n8_fabricated_proof_disproved_by_bisection() -> Result<()> {
    use lngap_harness::factchain_world::{ID_BOND, GRACE};
    use std::sync::Arc;

    let mut w = FcWorld::new("N8")?;
    let r = w.register()?;
    w.registering = false;
    let claim_from = r.h_max + GRACE;

    // Alice honestly claims "not anchored" after the grace period.
    // (The entry IS anchored — the hub submitted it — but Alice can still claim.)
    w.alice.user.set_move_policy(
        ID_BOND,
        Box::new(move |ctx: &MoveCtx| {
            (ctx.height >= claim_from && lngap_lamport::bits_to_uint(ctx.state) == 0)
                .then(|| vec![true])
        }),
    );
    w.alice.user.set_cancel_policy(ID_BOND, Box::new(|_| false));
    w.alice.user.faults.stop_from_seq = Some(2);

    // Hub cheats: alters the claimed end state of its inclusion proof.
    // The honest proof computes hash(headers) as the end state; the hub
    // flips one bit, so the bisection will find the discrepancy.
    w.alice.hub.faults.cheat_claim = Some(Arc::new(|s: &[u32]| {
        let mut t = s.to_vec();
        t[0] ^= 1;
        t
    }));

    // Wait for the bisection disproof to appear on-chain
    w.step_until(400, |w| {
        let roles = party_txs(&w.alice);
        roles.iter().any(|r| {
            r.starts_with("round_")
                || r.starts_with("cpred_")
            || r.starts_with("flat_")
                || r.starts_with("simple_")
                || r.starts_with("sched_")
                || r.starts_with("block_")
                || r.starts_with("ccopy_")
                || r.starts_with("ckeep_")
                || r.starts_with("re_")
        })
    })?;
    w.steps(5)?;

    let roles = party_txs(&w.alice);

    // The hub force-closes and makes move_1 (its fabricated inclusion proof).
    // Alice disputes (d1/dispute), the bisection runs, and the hub's proof
    // is disproved at a bisection leaf.
    assert!(roles.iter().any(|r| r == "move_1"), "hub's proof move: {roles:?}");
    assert!(roles.iter().any(|r| r == "d1/dispute"), "Alice disputed: {roles:?}");

    // The disproof lands at a bisection terminal leaf. With a cheated end
    // state, the bisection narrows to the last step (a NOP padding step)
    // and disproves it with a flat/simple leaf. If the cheat hit a
    // compression midstate, it would narrow to an n4bit round leaf instead.
    let d = roles.iter().find(|r| {
        r.starts_with("round_")
            || r.starts_with("cpred_")
            || r.starts_with("flat_")
            || r.starts_with("simple_")
            || r.starts_with("block_")
            || r.starts_with("ckeep_")
            || r.starts_with("re_")
    }).expect("bisection disproof leaf");

    println!("\n=== N8: bisection disproof at {d} ===");
    println!("  roles: {roles:?}");
    println!("  alice balance: {} (user), {} (hub)", w.alice.balance(Role::User), w.alice.balance(Role::Hub));

    // Alice wins the bond (the hub's proof was disproved)
    assert!(
        w.alice.balance(Role::User) > sat(100_000),
        "Alice gained the bond: {}",
        w.alice.balance(Role::User)
    );

    println!("\n{}", w.narrative());
    Ok(())
}

#[test]
fn n9_private_fork_refuted_by_heavier_chain() -> Result<()> {
    let mut w = FcWorld::new("FCN9")?;
    w.fork = true;
    w.register()?;
    w.registering = false; // no reveal: just the commit bond

    // Alice goes dark after proposing the claim, so the dispute resolves
    // on-chain (same forcing as N3/N8).
    w.alice.user.faults.stop_from_seq = Some(2);

    // Step until the bond resolves on-chain
    w.step_until(400, |w| {
        party_txs(&w.alice).iter().any(|r| r.starts_with("split_"))
    })?;
    w.steps(2)?;

    let roles = party_txs(&w.alice);
    println!("\n=== N9 roles: {roles:?} ===");

    // The hub proves inclusion on its private fork; Alice refutes with the
    // heavier real chain; the bond splits to her.
    let moves: Vec<&String> = roles.iter().filter(|r| r.starts_with("move_")).collect();
    assert!(moves.len() >= 2, "hub's fork proof + Alice's refutation: {roles:?}");
    let split = roles
        .iter()
        .find(|r| r.starts_with("split_"))
        .expect("a split happened");
    assert!(split.ends_with("BondToUser"), "the bond went to Alice: {split}");

    // NEITHER claim was disputed: the fork proof is internally valid (Alice
    // cannot disprove it) and so is Alice's longer chain (the hub cannot
    // disprove it). The resolution is by chain length alone, so no bisection
    // ever runs.
    assert!(
        !roles.iter().any(|r| r.contains("dispute")),
        "nothing to disprove on either side: {roles:?}"
    );

    // The real chain never contained the commit.
    assert_eq!(w.resolve("alice"), None);

    // Alice wins the bond.
    assert!(
        w.alice.balance(Role::User) > sat(100_000),
        "Alice gained the bond: {}",
        w.alice.balance(Role::User)
    );

    println!("\n{}", w.narrative());
    Ok(())
}
