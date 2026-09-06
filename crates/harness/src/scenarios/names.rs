//! Plan §8.2: N1–N8 on the bonded name registry.

use anyhow::Result;
use bitcoin::Amount;
use lngap_channel::protocol::Closing;
use lngap_channel::Role;
use lngap_names::statements::{attest_label, attest_value};
use lngap_party::draft::Change;
use lngap_party::{ChangeCtx, MoveCtx};

use super::{assert_cross_cutting, Report, Scenario};
use crate::names_world::{NamesWorld, Who, BOND, ID_BOND, ID_LEG2, PRICE};
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
        // on-chain payouts if the channel closed, else the channel's off-chain balances
        balances: if party_txs(&w.alice).is_empty() { balances(&w.alice) } else { [w.alice.balance(Role::User), w.alice.balance(Role::Hub)] },
        narrative: w.narrative(),
    };
    println!("{}", r.narrative);
    r
}

/// Register `alice` cooperatively through to the folded bond.
fn register_cooperatively(w: &mut NamesWorld) -> Result<()> {
    w.register()?;
    w.step_until(40, |w| contracts(&w.alice) == 0 && w.resolve("alice") == Some(w.alice_key()))?;
    Ok(())
}

pub const N1: Scenario = Scenario {
    id: "N1",
    title: "Alice registers `alice` through the hub; hub receipts, anchors commit and reveal, attests; cooperative",
    expected: "1 anchor tx per interval; no contract tx on-chain; bond folded back; registry shows alice -> K_A",
    run: || {
        let mut w = NamesWorld::new("N1")?;
        register_cooperatively(&mut w)?;
        assert!(party_txs(&w.alice).is_empty(), "no channel transaction on-chain");
        assert_eq!(balances(&w.alice), [sat(100_000), sat(100_000)]);
        let anchors = w.anchor_txs()?;
        assert!(anchors.len() >= 3, "genesis + commit anchor + reveal anchor: {}", anchors.len());
        assert!(w.alice.user.has_reveal(&attest_label("alice", &w.alice_key())));
        assert!(w.audit()?.is_empty(), "{:?}", w.audit()?);
        Ok(report(&w, &N1))
    },
};

pub const N2: Scenario = Scenario {
    id: "N2",
    title: "Hub receipts but never anchors or attests, and stops signing; Alice claims on-chain after d_receipt",
    expected: "N-REG: commitment, move_1 (claim revealing the receipt), split_1_BondToUser; Alice +20k",
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
        assert!(m1 > r.deadline, "claim only after d_receipt (CLTV)");
        assert_eq!(w.alice.balance(Role::User), sat(100_000 - K - K + BOND.to_sat() - 2 * K));
        assert_eq!(w.alice.balance(Role::Hub), sat(80_000 - K));
        assert!(!w.audit()?.is_empty(), "auditor reports the broken receipt promise");
        assert_cross_cutting(&w.alice);
        Ok(report(&w, &N2))
    },
};

pub const N3: Scenario = Scenario {
    id: "N3",
    title: "Hub receipts and attests off-chain, but Alice falsely claims `unattested` on-chain",
    expected: "hub refuses the claim off-chain, Alice force-closes and claims, hub broadcasts disprove_attested and keeps the bond; the attestation preimages are now on-chain",
    run: || {
        let mut w = NamesWorld::new("N3")?;
        let r = w.register()?;
        let d = r.deadline;
        // Alice's cheating policy: claim from d_receipt no matter what, never fold the bond
        w.alice.user.set_move_policy(ID_BOND, Box::new(move |ctx: &MoveCtx| (ctx.height >= d).then(|| vec![true])));
        w.alice.user.set_cancel_policy(ID_BOND, Box::new(|_| false));
        w.step_until(80, |w| party_txs(&w.alice).iter().any(|r| r.starts_with("disprove_")))?;
        w.steps(2)?;
        let roles = party_txs(&w.alice);
        assert!(roles.iter().any(|r| r == "disprove_attested"), "{roles:?}");
        assert!(matches!(w.alice.user.closing(), Some(Closing::Local { .. })), "Alice force-closed after her claim was refused");
        assert_eq!(w.alice.balance(Role::Hub), sat(80_000 - K + BOND.to_sat() - 2 * K));
        assert_eq!(w.alice.balance(Role::User), sat(100_000 - K - K));
        // the attestation is now public: reconstruct it from the disproof's witness alone
        let txid = w.alice.seen.iter().find(|s| s.role == "disprove_attested").unwrap().txid;
        let tx = w.rt.get_tx(&txid)?;
        let pk = w.hub.lock().unwrap().statement_pk(&attest_label("alice", &w.alice_key())).unwrap();
        let elems: Vec<Vec<u8>> = tx.input[0].witness.iter().map(|e| e.to_vec()).collect();
        let mut value = 0u32;
        for (i, bit) in pk.bits.iter().enumerate() {
            let one = elems.iter().any(|e| e.len() == 20 && lngap_btc::hash160(e) == bit.h1);
            let zero = elems.iter().any(|e| e.len() == 20 && lngap_btc::hash160(e) == bit.h0);
            assert!(one ^ zero, "bit {i} revealed exactly once");
            value |= u32::from(one) << i;
        }
        assert_eq!(value, attest_value("alice", &w.alice_key()), "on-chain preimages say attest(alice, K_A)");
        assert_cross_cutting(&w.alice);
        Ok(report(&w, &N3))
    },
};

pub const N4: Scenario = Scenario {
    id: "N4",
    title: "Sale of `alice` to Bob for 10k, all cooperative",
    expected: "no contract tx; Bob -10k, Alice +10k, hub flat; registry shows alice -> K_B in the next anchor",
    run: || {
        let mut w = NamesWorld::new("N4")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 40;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        w.step_until(60, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;
        assert_eq!(w.resolve("alice"), Some(w.bob_key()));
        assert_eq!(balances(&w.alice), [sat(110_000), sat(90_000)]);
        assert_eq!(balances(&w.bob), [sat(90_000), sat(110_000)]);
        assert!(party_txs(&w.alice).is_empty() && party_txs(&w.bob).is_empty());
        let findings = w.audit()?;
        assert!(findings.is_empty(), "{findings:?}");
        Ok(report(&w, &N4))
    },
};

pub const N5: Scenario = Scenario {
    id: "N5",
    title: "Sale; Alice never signs the transfer",
    expected: "Bob refunded at h_sale (cooperative cancel of leg 1); nothing else",
    run: || {
        let mut w = NamesWorld::new("N5")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 15;
        w.bob_offers(h_sale)?;
        w.step_until(40, |w| contracts(&w.bob) == 0)?;
        assert!(w.height() >= h_sale);
        assert_eq!(balances(&w.bob), [sat(100_000), sat(100_000)]);
        assert_eq!(w.resolve("alice"), Some(w.alice_key()));
        assert!(party_txs(&w.bob).is_empty());
        Ok(report(&w, &N5))
    },
};

pub const N6: Scenario = Scenario {
    id: "N6",
    title: "Sale; Alice signs, hub receipts the transfer, then refuses to anchor or attest",
    expected: "Bob refunded; hub's leg-2 payment refunded; Alice takes the hub's transfer bond off-chain; Alice keeps the name",
    run: || {
        let mut w = NamesWorld::new("N6")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 30;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        w.hub.lock().unwrap().faults.no_anchor = true;
        w.step_until(60, |w| contracts(&w.alice) == 0 && contracts(&w.bob) == 0)?;
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
    title: "Sale; hub anchors and attests, reveals the attestation on-chain in leg 1 to get paid by Bob, but refuses to pay Alice",
    expected: "Alice copies the attestation from leg 1's on-chain witness and exercises leg 2 on-chain; hub pays",
    run: || {
        let mut w = NamesWorld::new("N7")?;
        register_cooperatively(&mut w)?;
        let h_sale = w.height() + 70;
        w.bob_offers(h_sale)?;
        w.alice_sells(h_sale)?;
        // Bob goes dark so the hub has to reveal on-chain; the hub withholds
        // the statement from Alice and refuses her leg-2 claim
        w.bob.user.faults.stop_from_seq = Some(1);
        w.bob.user.faults.passive_onchain = true;
        w.withhold_from.insert(Who::Alice);
        w.set_hub_policy(Who::Alice, Some(Box::new(|ctx: &ChangeCtx| match ctx.change {
            Change::Move { id: ID_LEG2, .. } => anyhow::bail!("hub refuses to pay Alice"),
            _ => Ok(()),
        })));
        w.step_until(120, |w| party_txs(&w.alice).iter().any(|r| r.starts_with("split_")) && party_txs(&w.bob).iter().any(|r| r.starts_with("split_")))?;
        w.step_until(60, |w| party_txs(&w.alice).iter().any(|r| r == "settle" || r == "disprove_attested"))?;
        w.steps(2)?;
        let bob_roles = party_txs(&w.bob);
        assert!(bob_roles.iter().any(|r| r == "move_1") && bob_roles.iter().any(|r| r == "split_1_Paid"), "{bob_roles:?}");
        let alice_roles = party_txs(&w.alice);
        assert!(alice_roles.iter().any(|r| r == "move_1") && alice_roles.iter().any(|r| r == "split_1_Paid"), "{alice_roles:?}");
        let learned = w.alice.user.narrative().iter().any(|l| l.contains("from an on-chain witness"));
        assert!(learned, "Alice learned the attestation from the chain");
        assert_eq!(w.resolve("alice"), Some(w.bob_key()));
        // Bob's channel: hub gets 10k - move - split fees; Bob 90k - claim fee
        assert_eq!(w.bob.balance(Role::Hub), sat(100_000 - K - K + PRICE.to_sat() - 2 * K));
        assert_eq!(w.bob.balance(Role::User), sat(90_000 - K));
        // Alice's channel: Alice gets 10k - 2 fees; the transfer bond goes back to the hub either by
        // settle (Alice learned the attestation before d_receipt and never claimed) or by
        // disprove_attested (she claimed first, and the hub's disproof published the attestation)
        assert_eq!(w.alice.balance(Role::User), sat(100_000 - K - K + PRICE.to_sat() - 2 * K));
        let bond_fees = if alice_roles.iter().any(|r| r == "disprove_attested") { 2 * K } else { K };
        assert_eq!(w.alice.balance(Role::Hub), sat(70_000 - K + BOND.to_sat() - bond_fees));
        assert_cross_cutting(&w.alice);
        assert_cross_cutting(&w.bob);
        Ok(report(&w, &N7))
    },
};

pub const N8: Scenario = Scenario {
    id: "N8",
    title: "Harness audit: an anchored root omits a receipted request; two anchors carry conflicting roots",
    expected: "reported by the off-chain auditor; not enforced on-chain in the PoC (documented gap)",
    run: || {
        // (a) the hub receipts the reveal (request 2) but leaves it out of every anchor
        let mut w = NamesWorld::new("N8a")?;
        w.hub.lock().unwrap().faults.omit_req = Some(2);
        w.register()?;
        w.step_until(60, |w| contracts(&w.alice) == 0)?;
        assert_eq!(w.resolve("alice"), None, "no reveal anchored, no owner");
        assert_eq!(balances(&w.alice), [sat(120_000), sat(80_000)], "the commit's bond paid Alice off-chain since nothing could be attested");
        let findings = w.audit()?;
        assert!(findings.iter().any(|f| f.contains("receipt 2")), "{findings:?}");
        let mut rep = report(&w, &N8);
        // (b) the hub anchors a root that is not its published ledger
        let mut w2 = NamesWorld::new("N8b")?;
        w2.hub.lock().unwrap().faults.corrupt_root = true;
        w2.register()?;
        w2.steps(8)?;
        let findings2 = w2.audit()?;
        assert!(findings2.iter().any(|f| f.contains("not the published ledger")), "{findings2:?}");
        rep.narrative.push_str("\n=== auditor (a) ===\n");
        rep.narrative.push_str(&findings.join("\n"));
        rep.narrative.push_str("\n=== auditor (b) ===\n");
        rep.narrative.push_str(&findings2.join("\n"));
        println!("auditor findings (a): {findings:?}\nauditor findings (b): {findings2:?}");
        Ok(rep)
    },
};

pub fn scenarios() -> Vec<Scenario> {
    vec![N1, N2, N3, N4, N5, N6, N7, N8]
}
