//! Smoke tests for the regtest wrapper and the taproot/sighash helpers:
//! fund a NUMS-keyed taproot output and spend it through leaves with a
//! signature, a CLTV, and a CSV.

use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, TxOut};
use lngap_btc::keys::{xonly, Seed};
use lngap_btc::regtest::Regtest;
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, check_timelock, Timelock, FIXED_FEE};
use lngap_btc::witness::WitnessStack;

fn sink() -> ScriptBuf {
    // anyone-can-spend-ish sink: p2tr to a NUMS key, we never need to spend it
    TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)])
        .unwrap()
        .script_pubkey()
}

#[test]
fn spend_through_sig_cltv_and_csv_leaves() {
    let rt = Regtest::start().unwrap();
    let alice = Seed::from_label("alice").keypair("t");
    let bob = Seed::from_label("bob").keypair("t");
    let (a, b) = (xonly(&alice), xonly(&bob));
    let h0 = rt.height().unwrap();
    let cltv_h = h0 + 10;

    let tree = TapTree::new(vec![
        Leaf::new("two_of_two", Builder::new().two_of_two(&a, &b).into_script(), Timelock::NONE),
        Leaf::new("a_after_cltv", Builder::new().cltv(cltv_h).checksig(&a).into_script(), Timelock::cltv(cltv_h)),
        Leaf::new("b_after_csv", Builder::new().csv(5).checksig(&b).into_script(), Timelock::csv(5)),
    ])
    .unwrap();
    let value = Amount::from_sat(50_000);
    let out = vec![TxOut { value: value - FIXED_FEE, script_pubkey: sink() }];

    // --- 2-of-2, immediate
    let (op, prevout) = rt.fund(&tree.script_pubkey(), value).unwrap();
    let leaf = tree.leaf("two_of_two").unwrap();
    let mut tx = build_spend(op, &leaf.timelock, out.clone());
    check_timelock(&tx, 0, &leaf.timelock).unwrap();
    let sa = sign_tapscript(&alice, &tx, 0, std::slice::from_ref(&prevout), &leaf.script).unwrap();
    let sb = sign_tapscript(&bob, &tx, 0, std::slice::from_ref(&prevout), &leaf.script).unwrap();
    // script: <A> CHECKSIG <B> CHECKSIGADD — A's sig is consumed first (top).
    let mut w = WitnessStack::new();
    w.push(sa.as_ref().to_vec()).push(sb.as_ref().to_vec());
    tx.input[0].witness = w.build(&leaf.script, &tree.control_block("two_of_two").unwrap());
    // negative: only one signature
    let mut bad = tx.clone();
    let mut w1 = WitnessStack::new();
    w1.push(sa.as_ref().to_vec()).push(Vec::new());
    bad.input[0].witness = w1.build(&leaf.script, &tree.control_block("two_of_two").unwrap());
    assert!(rt.test_accept(&bad).is_err());
    rt.send_and_confirm(&tx).unwrap();

    // --- CLTV leaf: rejected before height, accepted after
    let (op, prevout) = rt.fund(&tree.script_pubkey(), value).unwrap();
    let leaf = tree.leaf("a_after_cltv").unwrap();
    let mut tx = build_spend(op, &leaf.timelock, out.clone());
    let sa = sign_tapscript(&alice, &tx, 0, std::slice::from_ref(&prevout), &leaf.script).unwrap();
    tx.input[0].witness = WitnessStack::new()
        .push(sa.as_ref().to_vec())
        .build(&leaf.script, &tree.control_block("a_after_cltv").unwrap());
    // A tx with nLockTime = h is valid in a block of height h+1, i.e. once the chain tip is ≥ h.
    assert!(rt.height().unwrap() < cltv_h);
    assert!(rt.test_accept(&tx).is_err(), "CLTV spend must fail before the height");
    rt.mine_to_height(cltv_h).unwrap();
    rt.send_and_confirm(&tx).unwrap();

    // --- CSV leaf: rejected until 5 blocks after funding confirms
    let (op, prevout) = rt.fund(&tree.script_pubkey(), value).unwrap();
    let leaf = tree.leaf("b_after_csv").unwrap();
    let mut tx = build_spend(op, &leaf.timelock, out.clone());
    let sb = sign_tapscript(&bob, &tx, 0, std::slice::from_ref(&prevout), &leaf.script).unwrap();
    tx.input[0].witness = WitnessStack::new()
        .push(sb.as_ref().to_vec())
        .build(&leaf.script, &tree.control_block("b_after_csv").unwrap());
    assert!(rt.test_accept(&tx).is_err(), "CSV spend must fail right after confirmation");
    rt.mine(3).unwrap();
    assert!(rt.test_accept(&tx).is_err(), "CSV 5: still too early after 4 confirmations");
    rt.mine(1).unwrap();
    assert!(rt.test_accept(&tx).is_ok(), "CSV 5: spendable at 5 confirmations");
    rt.send_and_confirm(&tx).unwrap();

    for (name, s, cb) in tree.sizes() {
        eprintln!("leaf {name}: script {s} bytes, control block {cb} bytes");
    }
}
