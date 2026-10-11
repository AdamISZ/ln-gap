//! Shared regtest fixtures for the seal tests.
#![allow(dead_code)]

use bitcoin::{Amount, ScriptBuf, Transaction, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_seal::{ceremony, first_tree, Member, PresignedChain, SealSpec};

pub const CEREMONY: [u8; 32] = [0xCE; 32];

pub fn spec_at(start: u32) -> SealSpec {
    SealSpec {
        value: Amount::from_sat(200_000),
        start,
        period: 4,
        periods: 3,
        grace: 2,
        release_delay: 5,
        fanout_depth: 3,
        leaf_value: Amount::from_sat(330),
        split_fee: Amount::from_sat(400),
        anchor_value: Amount::from_sat(240),
        closing_fee: Amount::from_sat(3_000),
    }
}

/// Fund `S_1` and run the toy ceremony over the funding outpoint.
pub fn setup(rt: &Regtest, seed: u8) -> (SealSpec, Member, PresignedChain) {
    let spec = spec_at(rt.height().unwrap() + 6);
    let member = Member::new([seed; 32], &spec);
    let tree = first_tree(&spec, &member.public(), &CEREMONY).unwrap();
    let (op, out) = rt.fund(&tree.script_pubkey(), spec.value).unwrap();
    assert_eq!(out.value, spec.value);
    let chain = ceremony(&spec, &member.public(), op, &CEREMONY).unwrap();
    (spec, member, chain)
}

/// A plain output returning most of `value`.
pub fn refund(value: Amount) -> Vec<TxOut> {
    vec![TxOut { value: value - Amount::from_sat(2_000), script_pubkey: ScriptBuf::new_op_return(b"lngap-seal-refund") }]
}

/// Close period k at exactly `H_k`: rejected one block earlier, mined at `H_k`.
pub fn close_at(rt: &Regtest, spec: &SealSpec, tx: &Transaction, k: u32, what: &str) {
    let h = spec.height(k);
    rt.mine_to_height(h - 2).unwrap();
    assert!(rt.test_accept(tx).is_err(), "closing {k} must not be valid before H_{k}");
    rt.mine_to_height(h - 1).unwrap();
    let at = rt.mine_with(std::slice::from_ref(tx)).unwrap_or_else(|e| panic!("closing {k} must mine at H_{k}: {e:#}"));
    assert_eq!(at, h);
    println!("SEAL closing {k} ({what}): {} vB", tx.vsize());
}

/// Broadcast every not-yet-confirmed transaction of `txs` in order, in one
/// block.
pub fn mine_missing(rt: &Regtest, txs: &[Transaction]) -> usize {
    let missing: Vec<Transaction> = txs
        .iter()
        .filter(|t| rt.confirmations(&t.compute_txid()).ok().flatten().is_none())
        .cloned()
        .collect();
    if !missing.is_empty() {
        rt.mine_with(&missing).unwrap_or_else(|e| panic!("unfolding the connector path must mine: {e:#}"));
    }
    missing.len()
}
