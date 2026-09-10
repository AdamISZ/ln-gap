//! Plan §8.2 N1–N8 on the bonded name registry, under the SPV model
//! (SPV_DISPUTE.md phases 3–4): no attestations or receipts; the hub
//! promises an anchor height and a proof shape, the bond is written against
//! them, every fact about the registry is an inclusion proof verified by
//! bisection, and a hub proving on a private fork is refuted by the heavier
//! chain.

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::protocol::Closing;
use lngap_channel::Role;
use lngap_party::draft::Change;
use lngap_party::{ChangeCtx, MoveCtx};

use super::{assert_cross_cutting, Report, Scenario};
use crate::names_world::{NamesWorld, Who, BOND, GRACE, ID_BOND, ID_LEG2, ID_RBOND, PRICE};
use crate::Harness;

const K: u64 = 1_000;
fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}
fn party_txs(h: &Harness) -> Vec<String> {
    h.seen.iter().filter(|s| s.by.is_some()).map(|s| s.role.clone()).collect()
}
fn balances(h: &Harness) -> [Amount; 2] {
    h.user.channel.current_state().balances
}
fn contracts(h: &Harness) -> usize {
    h.user.channel.current_state().contracts.len()
}
fn disproof(h: &Harness) -> Option<String> {
    party_txs(h).into_iter().find(|r| r.starts_with("cpred_") || r.starts_with("simple_") || r.starts_with("round_") || r.starts_with("sched_") || r.starts_with("block_") || r.starts_with("ccopy_") || r.starts_with("ckeep_") || r.starts_with("re_"))
}
fn output_of(h: &Harness, role: &str) -> Amount {
    let s = h.seen.iter().find(|s| s.role == role).unwrap();
    h.rt.get_tx(&s.txid).unwrap().output[0].value
}
fn report(w: &NamesWorld, sc: &Scenario) -> Report {
    let mut txs: Vec<(u32, String, String, String)> = Vec::new();
    for (tag, h) in [("alice", &w.alice), ("bob", &w.bob)] {
        for s in &h.seen {
            txs.push((s.height, format!("{tag}:{}", s.role), s.txid.to_string(), s.by.map(|r| r.name().to_string()).unwrap_or_else(|| "hub-registry".into())));
        }
    }
    txs.sort_by_key(|t| t.0);
    txs.dedup_by(|a, b| a.2 == b.2);
    let r = Report {
        id: sc.id.into(),
        title: sc.title.into(),
        expected: sc.expected.into(),
        txs,
        balances: if party_txs(&w.alice).is_empty() { balances(&w.alice) } else { [w.alice.balance(Role::User), w.alice.balance(Role::Hub)] },
        narrative: w.narrative(),
    };
    println!("{}", r.narrative);
    r
}

/// Register `alice` cooperatively through to both folded bonds.
fn register_cooperatively(w: &mut NamesWorld) -> Result<()> {
    w.register()?;
    w.step_until(60, |w| contracts(&w.alice) == 0 && w.resolve("alice") == Some(w.alice_key()))?;
    Ok(())
}

pub const N1: Scenario = Scenario {
    id: "N1",
    title: "Alice registers `alice` through the hub; hub promises, anchors commit and reveal; cooperative",
    expected: "1 anchor tx per request batch; no contract tx on-chain; both bonds folded back once the public ledger shows the entries; registry shows alice -> K_A",
    run: || {
        let mut w = NamesWorld::new("N1")?;
        register_cooperatively(&mut w)?;
        assert!(party_txs(&w.alice).is_empty(), "no channel transaction on-chain");
        assert_eq!(balances(&w.alice), [sat(100_000), sat(100_000)]);
        let anchors = w.anchor_txs()?;
        assert!(anchors.len() >= 2, "commit anchor + reveal anchor: {}", anchors.len());
        assert!(w.audit()?.is_empty(), "{:?}", w.audit()?);
        Ok(report(&w, &N1))
    },
};

pub const N2: Scenario = Scenario {
    id: "N2",
    title: "Hub promises but never anchors, and stops signing; Alice claims on-chain after the promised height",
    expected: "N-REG: commitment, move_1 (the claim, CLTV at the promised height + grace), no answer from the hub, split_1_BondToUser; Alice +40k",
    run: || {
        let mut w = NamesWorld::new("N2")?;
        w.hub.lock().unwrap().faults.no_anchor = true;
        let r = w.register()?;
        w.alice.hub.faults.stop_from_seq = Some(1);
        w.step_until(80, |w| party_txs(&w.alice).iter().any(|r| r.starts_with("split_")))?;
        w.steps(2)?;
        let roles = party_txs(&w.alice);
        assert!(roles.iter().any(|r| r == "move_1"), "{roles:?}");
        assert!(roles.iter().any(|r| r == "split_1_BondToUser"), "{roles:?}");
        let m1 = w.alice.seen.iter().find(|s| s.role == "move_1").unwrap().height;
        assert!(m1 > r.height + GRACE, "claim only after the promised height (CLTV)");
        assert_eq!(w.alice.balance(Role::User), sat(100_000 - K - K + BOND.to_sat() - 2 * K));
        assert_eq!(w.alice.balance(Role::Hub), sat(60_000 - K));
        assert!(!w.audit()?.is_empty(), "auditor reports the broken promise");
        assert_cross_cutting(&w.alice);
        Ok(report(&w, &N2))
    },
};

pub const N3: Scenario = Scenario {
    id: "N3",
    title: "Hub promises and anchors, but Alice falsely claims `not anchored` on-chain",
    expected: "hub refuses the claim off-chain, Alice force-closes and claims (move_1), the hub answers with its inclusion proof (move_2), Alice finds nothing to dispute, split_2_BondToHub; the hub keeps the bond",
    run: || {
        let mut w = NamesWorld::new("N3")?;
        let r = w.register()?;
        w.registering = false; // no reveal in this scenario: one bond
        let d = r.height + GRACE;
        // Alice's cheating policy: claim from the promised height no matter what, never fold the bond
        w.alice.user.set_move_policy(ID_BOND, Box::new(move |ctx: &MoveCtx| (ctx.height >= d && lngap_lamport::bits_to_uint(ctx.state) == 0).then(|| vec![true])));
        w.alice.user.set_cancel_policy(ID_BOND, Box::new(|_| false));
        w.step_until(120, |w| party_txs(&w.alice).iter().any(|r| r.starts_with("split_")))?;
        w.steps(2)?;
        let roles = party_txs(&w.alice);
        assert!(roles.iter().any(|r| r == "move_1") && roles.iter().any(|r| r == "move_2") && roles.iter().any(|r| r == "split_2_BondToHub"), "{roles:?}");
        assert!(!roles.iter().any(|r| r == "dispute"), "the proof was valid: no dispute");
        assert!(matches!(w.alice.user.closing(), Some(Closing::Local { .. })), "Alice force-closed after her claim was refused");
        assert!(w.alice.user.narrative().iter().any(|l| l.contains("claimed end state") && l.contains("correct")), "Alice checked the hub's proof");
        assert_eq!(w.alice.balance(Role::Hub), sat(60_000 - K + BOND.to_sat() - 3 * K));
        assert_eq!(w.alice.balance(Role::User), sat(100_000 - K - K));
        assert_cross_cutting(&w.alice);
        Ok(report(&w, &N3))
    },
};

pub const N4: Scenario = Scenario {
    id: "N4",
    title: "Sale of `alice` to Bob for 40k, all cooperative",
    expected: "no contract tx; Bob -40k, Alice +40k, hub flat; registry shows alice -> K_B in the next anchor; both legs paid on the same public inclusion proof",
    run: || {
        let mut w = NamesWorld::new("N4")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 40;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        w.step_until(80, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;
        assert_eq!(w.resolve("alice"), Some(w.bob_key()));
        assert_eq!(balances(&w.alice), [sat(140_000), sat(60_000)]);
        assert_eq!(balances(&w.bob), [sat(60_000), sat(140_000)]);
        assert!(party_txs(&w.alice).is_empty() && party_txs(&w.bob).is_empty());
        let findings = w.audit()?;
        assert!(findings.is_empty(), "{findings:?}");
        Ok(report(&w, &N4))
    },
};

pub const N5: Scenario = Scenario {
    id: "N5",
    title: "Sale; Alice never signs the transfer",
    expected: "nothing opens: the legs name the transfer entry, which exists only once Alice signs; balances unchanged",
    run: || {
        let mut w = NamesWorld::new("N5")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 15;
        w.bob_offers(h_sale)?;
        w.step_until(20, |w| w.height() >= h_sale)?;
        assert_eq!(contracts(&w.bob), 0);
        assert_eq!(balances(&w.bob), [sat(100_000), sat(100_000)]);
        assert_eq!(w.resolve("alice"), Some(w.alice_key()));
        assert!(party_txs(&w.bob).is_empty());
        Ok(report(&w, &N5))
    },
};

pub const N6: Scenario = Scenario {
    id: "N6",
    title: "Sale; Alice signs, hub promises the transfer, then refuses to anchor",
    expected: "Bob refunded at h_sale; the hub's leg-2 payment refunded; Alice claims the transfer bond off-chain (the hub cannot answer) and takes it at the deadline; Alice keeps the name",
    run: || {
        let mut w = NamesWorld::new("N6")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 30;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        w.hub.lock().unwrap().faults.no_anchor = true;
        w.step_until(120, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;
        assert_eq!(balances(&w.bob), [sat(100_000), sat(100_000)]);
        assert_eq!(balances(&w.alice), [sat(100_000 + BOND.to_sat()), sat(100_000 - BOND.to_sat())]);
        assert_eq!(w.resolve("alice"), Some(w.alice_key()));
        assert!(party_txs(&w.alice).is_empty() && party_txs(&w.bob).is_empty());
        let findings = w.audit()?;
        assert!(findings.iter().any(|f| f.contains("transfer")), "{findings:?}");
        Ok(report(&w, &N6))
    },
};

pub const N7: Scenario = Scenario {
    id: "N7",
    title: "Sale; hub anchors, proves inclusion on-chain in leg 1 to get paid by Bob, but refuses to pay Alice",
    expected: "the proof data is public: Alice proves the same inclusion herself in leg 2 on-chain; hub pays; no attestation needed",
    run: || {
        let mut w = NamesWorld::new("N7")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 70;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        // Bob goes dark so the hub has to prove on-chain; the hub refuses Alice's leg-2 claim
        w.bob.user.faults.stop_from_seq = Some(1);
        w.bob.user.faults.passive_onchain = true;
        w.set_hub_policy(Who::Alice, Some(Box::new(|ctx: &ChangeCtx| match ctx.change {
            Change::Move { id: ID_LEG2, .. } => anyhow::bail!("hub refuses to pay Alice"),
            _ => Ok(()),
        })));
        w.step_until(160, |w| party_txs(&w.alice).iter().any(|r| r == "split_1_Paid") && party_txs(&w.bob).iter().any(|r| r == "split_1_Paid"))?;
        // the transfer bond on-chain resolves by settle at its deadline (anchored: nothing to claim)
        w.step_until(120, |w| party_txs(&w.alice).iter().any(|r| r == "settle"))?;
        w.steps(2)?;
        let bob_roles = party_txs(&w.bob);
        assert!(bob_roles.iter().any(|r| r == "move_1") && bob_roles.iter().any(|r| r == "split_1_Paid"), "{bob_roles:?}");
        let alice_roles = party_txs(&w.alice);
        assert!(alice_roles.iter().any(|r| r == "move_1") && alice_roles.iter().any(|r| r == "split_1_Paid"), "{alice_roles:?}");
        assert!(!alice_roles.iter().any(|r| r == "dispute") && !bob_roles.iter().any(|r| r == "dispute"));
        assert_eq!(w.resolve("alice"), Some(w.bob_key()));
        // Bob's channel: hub gets 10k - move - split fees; Bob 90k - claim fee
        assert_eq!(w.bob.balance(Role::Hub), sat(100_000 - K - K + PRICE.to_sat() - 2 * K));
        assert_eq!(w.bob.balance(Role::User), sat(60_000 - K));
        // Alice's channel: Alice gets 10k - 2 fees
        assert!(w.alice.balance(Role::User) >= sat(100_000 - K - K + PRICE.to_sat() - 2 * K), "{}", w.alice.balance(Role::User));
        assert_cross_cutting(&w.alice);
        assert_cross_cutting(&w.bob);
        Ok(report(&w, &N7))
    },
};

pub const N8: Scenario = Scenario {
    id: "N8",
    title: "Omission: the hub promises the reveal, leaves it out of the anchor, and tries a fabricated inclusion proof",
    expected: "Alice claims the reveal bond; the hub's proof is rejected off-chain, goes on-chain (move_2) and is disproved by bisection at the ledger-root check; bond to Alice; the auditor reports the omission too",
    run: || {
        let mut w = NamesWorld::new("N8")?;
        w.hub.lock().unwrap().faults.omit_req = Some(2);
        w.register()?;
        w.step_until(200, |w| disproof(&w.alice).is_some())?;
        w.steps(2)?;
        let roles = party_txs(&w.alice);
        let d = disproof(&w.alice).unwrap();
        assert!(d.starts_with("simple_ledger_root"), "{d}: {roles:?}");
        assert!(roles.iter().any(|r| r == "move_2") && roles.iter().any(|r| r == "d2/dispute"), "{roles:?}");
        assert_eq!(w.resolve("alice"), None, "no reveal anchored, no owner");
        let findings = w.audit()?;
        assert!(findings.iter().any(|f| f.contains("promise 2")), "{findings:?}");
        // Alice's channel closed: the reveal bond's disproof paid her; the commit bond was folded earlier
        let out = output_of(&w.alice, &d);
        assert!(out > sat(BOND.to_sat() - 30 * K) && out < BOND, "the bond minus the dispute's fees: {out}");
        // a bisection dispute pays some of its transactions by size (D18), so the
        // flat-fee balance equation of `assert_cross_cutting` does not apply here
        w.alice.assert_signing_rule();
        assert_eq!(w.alice.balance(Role::User), sat(100_000 - K - K) + out, "the disproof paid Alice the bond");
        let mut rep = report(&w, &N8);
        rep.narrative.push_str("\n=== auditor ===\n");
        rep.narrative.push_str(&findings.join("\n"));
        Ok(rep)
    },
};

pub const N9: Scenario = Scenario {
    id: "N9",
    title: "Fake chain: the hub anchors on a private fork and proves inclusion there; Alice refutes with the heavier chain",
    expected: "Alice's node does not see the anchor; she claims, the hub proves inclusion on its fork (move_2, internally valid), Alice refutes with one more real header (move_3), split_3_BondToUser",
    run: || {
        let mut w = NamesWorld::new("N9")?;
        w.fork = true;
        w.register()?;
        w.step_until(200, |w| party_txs(&w.alice).iter().any(|r| r.starts_with("split_")))?;
        w.steps(2)?;
        let roles = party_txs(&w.alice);
        assert!(roles.iter().any(|r| r == "move_2") && roles.iter().any(|r| r == "move_3") && roles.iter().any(|r| r == "split_3_BondToUser"), "{roles:?}");
        assert!(w.alice.user.narrative().iter().any(|l| l.contains("claimed end state") && l.contains("correct")), "the fork proof is internally valid");
        assert_eq!(w.alice.balance(Role::User), sat(100_000 - K - K + BOND.to_sat() - 4 * K));
        assert_cross_cutting(&w.alice);
        Ok(report(&w, &N9))
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![N1, N2, N3, N4, N5, N6, N7, N8, N9]
}

pub const _IDS: [u32; 2] = [ID_RBOND, ID_LEG2];
