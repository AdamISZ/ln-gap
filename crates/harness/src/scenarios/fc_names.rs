//! Fact-chain scenario wrappers for the scenario runner.
//! These use FcWorld and delegate to the same logic as the cargo tests,
//! but return Report structs so the scenario runner can --keep them
//! for the explorer.

use std::sync::Arc;

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::Role;
use crate::factchain_world::{FcWorld, Who, BOND, GRACE, ID_BOND, ID_LEG2};
use lngap_party::MoveCtx;

use super::{Report, Scenario};

fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}
fn party_txs(h: &crate::Harness) -> Vec<String> {
    h.seen
        .iter()
        .filter(|s| s.by.is_some())
        .map(|s| s.role.clone())
        .collect()
}
fn contracts(h: &crate::Harness) -> usize {
    h.user.channel.current_state().contracts.len()
}
fn balances(h: &crate::Harness) -> [Amount; 2] {
    h.user.channel.current_state().balances
}

fn register_cooperatively(w: &mut FcWorld) -> Result<()> {
    w.register()?;
    w.step_until(60, |w| {
        contracts(&w.alice) == 0 && w.resolve("alice") == Some(w.alice_key())
    })?;
    Ok(())
}

fn fc_report(w: &FcWorld, id: &str, title: &str, expected: &str) -> Report {
    let mut txs: Vec<(u32, String, String, String)> = Vec::new();
    for (tag, h) in [("alice", &w.alice), ("bob", &w.bob)] {
        for s in &h.seen {
            txs.push((
                s.height,
                format!("{tag}:{}", s.role),
                s.txid.to_string(),
                s.by
                    .map(|r| r.name().to_string())
                    .unwrap_or_else(|| "hub-registry".into()),
            ));
        }
    }
    txs.sort_by_key(|t| t.0);
    txs.dedup_by(|a, b| a.2 == b.2);
    Report {
        id: id.into(),
        title: title.into(),
        expected: expected.into(),
        txs,
        balances: [w.alice.balance(Role::User), w.alice.balance(Role::Hub)],
        narrative: w.narrative(),
    }
}

pub const FC_N1: Scenario = Scenario {
    id: "FCN1",
    title: "Cooperative registration on the fact chain",
    expected: "no channel tx on-chain; both bonds folded; registry shows alice -> K_A",
    run: || {
        let mut w = FcWorld::new("FCN1")?;
        register_cooperatively(&mut w)?;
        assert!(party_txs(&w.alice).is_empty());
        assert_eq!(balances(&w.alice), [sat(100_000), sat(100_000)]);
        assert_eq!(w.resolve("alice"), Some(w.alice_key()));
        assert!(w.fc_height() >= 2);
        let r = fc_report(&w, FC_N1.id, FC_N1.title, FC_N1.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub const FC_N2: Scenario = Scenario {
    id: "FCN2",
    title: "Hub doesn't submit to the fact chain; Alice claims the bond",
    expected: "move_1 (CLTV at h_max+GRACE), split_1_BondToUser; Alice +40k",
    run: || {
        let mut w = FcWorld::new("FCN2")?;
        w.hub.lock().unwrap().faults.no_submit = true;
        let r = w.register()?;
        w.alice.hub.faults.stop_from_seq = Some(1);
        w.step_until(200, |w| {
            party_txs(&w.alice).iter().any(|r| r.starts_with("split_"))
        })?;
        w.steps(2)?;
        let roles = party_txs(&w.alice);
        assert!(roles.iter().any(|r| r == "move_1"));
        assert!(roles.iter().any(|r| r == "split_1_BondToUser"));
        let m1 = w.alice.seen.iter().find(|s| s.role == "move_1").unwrap().height;
        assert!(m1 >= r.h_max + GRACE);
        assert!(w.alice.balance(Role::User) > sat(100_000));
        let r = fc_report(&w, FC_N2.id, FC_N2.title, FC_N2.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub const FC_N3: Scenario = Scenario {
    id: "FCN3",
    title: "Alice falsely claims not anchored; hub proves inclusion on-chain",
    expected: "move_1 (Alice claims), hub answers, split_1_BondToHub",
    run: || {
        let mut w = FcWorld::new("FCN3")?;
        let r = w.register()?;
        w.registering = false;
        let claim_from = r.h_max + GRACE;
        w.alice.user.set_move_policy(
            ID_BOND,
            Box::new(move |ctx: &MoveCtx| {
                (ctx.height >= claim_from && lngap_lamport::bits_to_uint(ctx.state) == 0)
                    .then(|| vec![true])
            }),
        );
        w.alice.user.set_cancel_policy(ID_BOND, Box::new(|_| false));
        w.alice.user.faults.stop_from_seq = Some(2);
        w.step_until(200, |w| {
            party_txs(&w.alice).iter().any(|r| r.starts_with("split_"))
        })?;
        w.steps(2)?;
        let roles = party_txs(&w.alice);
        assert!(roles.iter().any(|r| r == "move_1"));
        assert!(roles.iter().any(|r| r == "split_1_BondToHub"));
        let r = fc_report(&w, FC_N3.id, FC_N3.title, FC_N3.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub const FC_N4: Scenario = Scenario {
    id: "FCN4",
    title: "Cooperative sale of alice to Bob on the fact chain",
    expected: "no channel tx; Bob -40k, Alice +40k; registry shows alice -> K_B",
    run: || {
        let mut w = FcWorld::new("FCN4")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 40;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        w.step_until(80, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;
        assert_eq!(w.resolve("alice"), Some(w.bob_key()));
        assert_eq!(balances(&w.alice), [sat(140_000), sat(60_000)]);
        assert_eq!(balances(&w.bob), [sat(60_000), sat(140_000)]);
        assert!(party_txs(&w.alice).is_empty() && party_txs(&w.bob).is_empty());
        let r = fc_report(&w, FC_N4.id, FC_N4.title, FC_N4.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub const FC_N5: Scenario = Scenario {
    id: "FCN5",
    title: "Sale; Alice never signs the transfer",
    expected: "nothing opens; balances unchanged; registry shows alice -> K_A",
    run: || {
        let mut w = FcWorld::new("FCN5")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 15;
        w.bob_offers(h_sale)?;
        w.step_until(30, |w| w.height() >= h_sale)?;
        assert_eq!(contracts(&w.bob), 0);
        assert_eq!(balances(&w.bob), [sat(100_000), sat(100_000)]);
        assert_eq!(w.resolve("alice"), Some(w.alice_key()));
        let r = fc_report(&w, FC_N5.id, FC_N5.title, FC_N5.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub const FC_N6: Scenario = Scenario {
    id: "FCN6",
    title: "Sale; hub promises transfer but refuses to submit to fact chain",
    expected: "Bob refunded; Alice keeps the name; no on-chain dispute",
    run: || {
        let mut w = FcWorld::new("FCN6")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 30;
        w.bob_offers(h_sale)?;
        w.hub.lock().unwrap().faults.no_submit = true;
        w.alice_sells(h_sale)?;
        w.pending_entry = None;
        w.step_until(200, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;
        assert_eq!(balances(&w.bob), [sat(100_000), sat(100_000)]);
        assert_eq!(w.resolve("alice"), Some(w.alice_key()));
        assert!(party_txs(&w.alice).is_empty() && party_txs(&w.bob).is_empty());
        let r = fc_report(&w, FC_N6.id, FC_N6.title, FC_N6.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub const FC_N7: Scenario = Scenario {
    id: "FCN7",
    title: "Sale; hub proves inclusion on-chain in leg 1, refuses to pay Alice",
    expected: "Bob's leg resolves (hub proves); registry shows alice -> K_B",
    run: || {
        let mut w = FcWorld::new("FCN7")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 70;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        w.bob.user.faults.stop_from_seq = Some(1);
        w.bob.user.faults.passive_onchain = true;
        w.set_hub_policy(
            Who::Alice,
            Some(Box::new(|ctx: &lngap_party::ChangeCtx| {
                if let lngap_party::draft::Change::Move { id, .. } = ctx.change {
                    if *id == ID_LEG2 {
                        anyhow::bail!("hub refuses to pay Alice");
                    }
                }
                Ok(())
            })),
        );
        w.step_until(200, |w| {
            party_txs(&w.bob).iter().any(|r| r == "split_1_Paid")
        })?;
        w.steps(20)?;
        assert_eq!(w.resolve("alice"), Some(w.bob_key()));
        let r = fc_report(&w, FC_N7.id, FC_N7.title, FC_N7.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

fn disproof(roles: &[String]) -> Option<String> {
    roles.iter().find(|r| {
        r.starts_with("cpred_")
            || r.starts_with("simple_")
            || r.starts_with("round_")
            || r.starts_with("sched_")
            || r.starts_with("block_")
            || r.starts_with("ccopy_")
            || r.starts_with("ckeep_")
            || r.starts_with("re_")
    }).cloned()
}

pub const FC_N8: Scenario = Scenario {
    id: "FCN8",
    title: "Hub fabricates inclusion proof; Alice disproves by n4bit bisection",
    expected: "move_1 (Alice claims), move_2 (hub's fabricated proof), bisection disproves at n4bit round leaf, bond to Alice",
    run: || {
        let mut w = FcWorld::new("FCN8")?;
        let r = w.register()?;
        w.registering = false;
        let claim_from = r.h_max + GRACE;

        // Alice honestly claims "not anchored" after the grace period
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
            disproof(&roles).is_some()
        })?;
        w.steps(5)?;

        let roles = party_txs(&w.alice);
        // as in tests/fc_names.rs: the hub force-closes and makes move_1 (its
        // fabricated proof), Alice disputes, and the bisection lands on a
        // terminal leaf (a simple step with a cheated end state, or a
        // compression leaf if the cheat hit a midstate)
        assert!(roles.iter().any(|r| r == "move_1"), "hub's proof move: {roles:?}");
        assert!(roles.iter().any(|r| r == "d1/dispute"), "Alice disputed: {roles:?}");
        let d = disproof(&roles).expect("bisection disproof");
        assert!(
            d.starts_with("round_") || d.starts_with("cpred_") || d.starts_with("block_") || d.starts_with("ckeep_") || d.starts_with("re_") || d.starts_with("simple_") || d.starts_with("flat_"),
            "disproof at a bisection leaf: {d} (roles: {roles:?})"
        );
        // Alice wins the bond (the hub's proof was disproved)
        assert!(w.alice.balance(Role::User) > sat(100_000), "Alice gained the bond: {}", w.alice.balance(Role::User));
        let r = fc_report(&w, FC_N8.id, FC_N8.title, FC_N8.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub const FC_N9: Scenario = Scenario {
    id: "FCN9",
    title: "Hub proves inclusion on a private fork; Alice refutes with the heavier chain",
    expected: "both claims are internally valid, so no dispute runs; the longer chain wins: split BondToUser; the commit is not on the real chain",
    run: || {
        let mut w = FcWorld::new("FCN9")?;
        w.fork = true;
        w.register()?;
        w.registering = false; // no reveal: just the commit bond

        // Alice goes dark after proposing the claim, so the dispute resolves on-chain
        w.alice.user.faults.stop_from_seq = Some(2);

        w.step_until(400, |w| {
            party_txs(&w.alice).iter().any(|r| r.starts_with("split_"))
        })?;
        w.steps(2)?;

        let roles = party_txs(&w.alice);
        let moves = roles.iter().filter(|r| r.starts_with("move_")).count();
        assert!(moves >= 2, "hub's fork proof + Alice's refutation: {roles:?}");
        let split = roles
            .iter()
            .find(|r| r.starts_with("split_"))
            .expect("a split happened");
        assert!(split.ends_with("BondToUser"), "the bond went to Alice: {split}");
        // Neither claim was disputed: the fork proof is internally valid and
        // so is the heavier chain — the resolution is by chain length alone.
        assert!(
            !roles.iter().any(|r| r.contains("dispute")),
            "nothing to disprove on either side: {roles:?}"
        );
        assert_eq!(w.resolve("alice"), None, "the commit is not on the real chain");
        assert!(w.alice.balance(Role::User) > sat(100_000), "Alice gained the bond: {}", w.alice.balance(Role::User));
        let r = fc_report(&w, FC_N9.id, FC_N9.title, FC_N9.expected);
        println!("\n{}", r.narrative);
        Ok(r)
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![FC_N1, FC_N2, FC_N3, FC_N4, FC_N5, FC_N6, FC_N7, FC_N8, FC_N9]
}
