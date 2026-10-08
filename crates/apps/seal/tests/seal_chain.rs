//! V25_POC_PLAN.md Phase 1 on regtest: a member's seal chain.
//!
//! - closings with a root and empty closings confirm from `H_k`, not before;
//! - a skipped period: the burn opens at `H_k + grace`, and the full-fee
//!   burn takes the bond; the late closing is still valid at that height
//!   (the race against the burn: only a member that mines wins it);
//! - two different roots for one period: the slash leaf takes the bond,
//!   not before `race_from`; the same root twice is not evidence;
//! - an honest term: the member reclaims the final output after `release`.
//!
//! Run with `--test-threads=1` or 2: each test starts its own node.

use bitcoin::{Amount, ScriptBuf, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_seal::{ceremony, first_tree, Member, PresignedChain, SealSpec};

const CEREMONY: [u8; 32] = [0xCE; 32];

fn spec_at(start: u32) -> SealSpec {
    SealSpec {
        value: Amount::from_sat(200_000),
        start,
        period: 4,
        periods: 3,
        grace: 2,
        release_delay: 5,
        connector_value: Amount::from_sat(330),
        anchor_value: Amount::from_sat(330),
        closing_fee: Amount::from_sat(3_000),
    }
}

/// Fund `S_1` and run the toy ceremony over the funding outpoint.
fn setup(rt: &Regtest, seed: u8) -> (SealSpec, Member, PresignedChain) {
    let spec = spec_at(rt.height().unwrap() + 6);
    let member = Member::new([seed; 32], spec.periods);
    let tree = first_tree(&spec, &member.public(), &CEREMONY).unwrap();
    let (op, out) = rt.fund(&tree.script_pubkey(), spec.value).unwrap();
    assert_eq!(out.value, spec.value);
    let chain = ceremony(&spec, &member.public(), op, &CEREMONY).unwrap();
    (spec, member, chain)
}

/// One zero-value OP_RETURN output: the whole input goes to fee (the
/// OP_RETURN carries a few bytes so the tx is not `tx-size-small`).
fn burn_outputs() -> Vec<TxOut> {
    vec![TxOut { value: Amount::ZERO, script_pubkey: ScriptBuf::new_op_return(b"lngap-seal-burn") }]
}

/// A plain output returning most of `value` (for negatives that must not
/// trip the RPC's max-fee guard).
fn refund(value: Amount) -> Vec<TxOut> {
    vec![TxOut { value: value - Amount::from_sat(2_000), script_pubkey: ScriptBuf::new_op_return(b"lngap-seal-refund") }]
}

/// Close period k at exactly `H_k`: rejected one block earlier, mined at `H_k`.
fn close_at(rt: &Regtest, spec: &SealSpec, tx: &bitcoin::Transaction, k: u32, what: &str) {
    let h = spec.height(k);
    rt.mine_to_height(h - 2).unwrap();
    assert!(rt.test_accept(tx).is_err(), "closing {k} must not be valid before H_{k}");
    rt.mine_to_height(h - 1).unwrap();
    let at = rt.mine_with(std::slice::from_ref(tx)).unwrap_or_else(|e| panic!("closing {k} must mine at H_{k}: {e:#}"));
    assert_eq!(at, h);
    println!("PHASE1 closing {k} ({what}): {} vB", tx.vsize());
}

#[test]
fn closings_and_the_burn_of_a_skipped_period() {
    let rt = Regtest::start().unwrap();
    let (spec, member, chain) = setup(&rt, 1);

    // period 1: a root
    let tx1 = chain.close(&member, 1, &[0xA1; 20]).unwrap();
    close_at(&rt, &spec, &tx1, 1, "root");
    assert!(rt.is_unspent(&chain.connector_outpoint(1).unwrap()).unwrap(), "closing 1 created its connector");
    assert!(rt.is_unspent(&chain.seal_outpoint(2).unwrap()).unwrap(), "the bond moved to S_2");

    // period 2: idle, the empty preimage
    let tx2 = chain.close_empty(&member, 2).unwrap();
    close_at(&rt, &spec, &tx2, 2, "empty");

    // period 3: skipped. The burn opens at H_3 + grace.
    let b = spec.burn_from(3);
    rt.mine_to_height(b - 2).unwrap();
    let early = chain.burn(3, refund(spec.output_value(3))).unwrap();
    assert!(rt.test_accept(&early).is_err(), "the burn must wait for H_3 + grace");
    rt.mine_to_height(b - 1).unwrap();
    // the race: the pre-signed closing is still valid now, as is the burn
    let late = chain.close(&member, 3, &[0xA3; 20]).unwrap();
    assert!(rt.test_accept(&late).is_ok(), "a late closing is still valid: it races the burn");
    let burn = chain.burn(3, burn_outputs()).unwrap();
    let txid = rt.send_raw_any_fee(&burn).unwrap();
    rt.mine(1).unwrap();
    assert!(rt.confirmations(&txid).unwrap().is_some(), "the burn confirmed");
    assert!(!rt.is_unspent(&chain.seal_outpoint(3).unwrap()).unwrap(), "S_3 is spent");
    println!("PHASE1 burn: {} vB, {} sat to the miner", burn.vsize(), spec.output_value(3).to_sat());
}

#[test]
fn two_roots_for_one_period_are_slashed() {
    let rt = Regtest::start().unwrap();
    let (spec, member, chain) = setup(&rt, 2);

    let root_a = [0x0A; 20];
    let root_b = [0x0B; 20];
    close_at(&rt, &spec, &chain.close(&member, 1, &root_a).unwrap(), 1, "root");
    // the equivocation: a second root for period 1, given out off chain
    let sig_a = member.sign_root(1, &root_a).unwrap();
    let sig_b = member.sign_root(1, &root_b).unwrap();
    close_at(&rt, &spec, &chain.close_empty(&member, 2).unwrap(), 2, "empty");
    close_at(&rt, &spec, &chain.close(&member, 3, &[0x33; 20]).unwrap(), 3, "root");
    let k = spec.periods + 1; // the bond now sits in the final output

    // no head start: the evidence is not spendable before race_from
    let r = spec.race_from();
    rt.mine_to_height(r - 2).unwrap();
    let early = chain.slash(k, 1, &sig_a, &sig_b, refund(spec.output_value(k))).unwrap();
    assert!(rt.test_accept(&early).is_err(), "the slash must wait for race_from");
    rt.mine_to_height(r - 1).unwrap();
    // the same root twice is not evidence
    let same = chain.slash(k, 1, &sig_a, &sig_a, refund(spec.output_value(k))).unwrap();
    assert!(rt.test_accept(&same).is_err(), "one root presented twice must not slash");
    // a pair for a different period's key fails
    let wrong = chain.slash(k, 2, &sig_a, &sig_b, refund(spec.output_value(k))).unwrap();
    assert!(rt.test_accept(&wrong).is_err(), "period-1 signatures are not evidence under period 2's key");
    // the watcher's full-fee slash
    let slash = chain.slash(k, 1, &sig_a, &sig_b, burn_outputs()).unwrap();
    let txid = rt.send_raw_any_fee(&slash).unwrap();
    rt.mine(1).unwrap();
    assert!(rt.confirmations(&txid).unwrap().is_some(), "the slash confirmed");
    println!("PHASE1 slash: {} vB, {} sat to the miner", slash.vsize(), spec.output_value(k).to_sat());
}

#[test]
fn an_honest_term_is_reclaimed_after_release() {
    let rt = Regtest::start().unwrap();
    let (spec, member, chain) = setup(&rt, 3);
    for k in 1..=spec.periods {
        close_at(&rt, &spec, &chain.close(&member, k, &[k as u8; 20]).unwrap(), k, "root");
    }
    let k = spec.periods + 1;
    let out = refund(spec.output_value(k));
    rt.mine_to_height(spec.release() - 2).unwrap();
    assert!(rt.test_accept(&chain.reclaim(&member, out.clone()).unwrap()).is_err(), "no reclaim before release");
    rt.mine_to_height(spec.release() - 1).unwrap();
    let tx = chain.reclaim(&member, out).unwrap();
    rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("the reclaim must mine at release: {e:#}"));
    println!("PHASE1 reclaim: {} vB", tx.vsize());
}
