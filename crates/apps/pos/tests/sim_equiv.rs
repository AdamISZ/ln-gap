//! The player-equivocation gadget through the script32 simulator (D39; the
//! D29 discipline). The leaf's 2-of-2 prefix is not simulable (the
//! simulator does not stub CHECKSIGADD, sim_ttt.rs's note), so this pins
//! the leaf's own logic: the 46-byte `LamportExt::equivocation` gadget,
//! which is the whole evidence check — it admits exactly the pair of BOTH
//! preimages of one bit commitment.

use bitcoin::script::Builder;
use lngap_lamport::gadgets::LamportExt;
use lngap_lamport::BitSecret;

fn bit() -> (BitSecret, lngap_lamport::BitCommit) {
    let sk = BitSecret { p0: [0xA0; 20], p1: [0xA1; 20] };
    (sk, sk.commit())
}

#[test]
fn equivocation_gadget_is_46_bytes() {
    // the figure POS_FACTCHAIN_PLAN.md step 6 quotes
    let (_sk, c) = bit();
    let b = Builder::new().equivocation(&c).into_script();
    assert_eq!(b.len(), 46, "hash160_verify(h1) + hash160_verify(h0)");
}

#[test]
fn equivocation_admits_exactly_both_preimages() {
    let (sk, c) = bit();
    let leaf = Builder::new().equivocation(&c).push_int(1).into_script();
    // witness `p0 p1`, p1 on top (the gadget consumes h1's preimage first)
    let good = vec![sk.p0.to_vec(), sk.p1.to_vec()];
    assert!(lngap_script32::sim::run(leaf.as_script(), good).is_ok(), "both preimages must open the leaf");
    // the same preimage twice is not evidence of anything
    let same = vec![sk.p0.to_vec(), sk.p0.to_vec()];
    assert!(lngap_script32::sim::run(leaf.as_script(), same).is_err(), "p0 twice must fail h1's check");
    let same1 = vec![sk.p1.to_vec(), sk.p1.to_vec()];
    assert!(lngap_script32::sim::run(leaf.as_script(), same1).is_err(), "p1 twice must fail h0's check");
    // a wrong value is not a preimage at all
    let wrong = vec![[0x42; 20].to_vec(), sk.p1.to_vec()];
    assert!(lngap_script32::sim::run(leaf.as_script(), wrong).is_err(), "a wrong value must fail h0's check");
    // swapped order fails (p1 does not open h0's position... the wire order is fixed)
    let swapped = vec![sk.p1.to_vec(), sk.p0.to_vec()];
    assert!(
        lngap_script32::sim::run(leaf.as_script(), swapped).is_err(),
        "the wire order is pinned: p1 on top, checked against h1 first"
    );
}
