//! V25_POC_PLAN.md Phase 1 on regtest: a member's seal chain.
//!
//! - closings with a root and empty closings confirm from `H_k`, not before;
//! - a skipped period: the pinned burn opens at `H_k + grace` and takes the
//!   bond to fees; nobody can redirect the burn leaf; the late closing is
//!   still valid at that height (the race: only a member that mines wins);
//! - two different roots for one period: the pinned slash takes the bond,
//!   not before `race_from`; the same root twice is not evidence;
//! - an honest term: the member reclaims the final output after `release`.
//!
//! Run with `--test-threads=1` or 2: each test starts its own node.

mod common;

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, ScriptBuf, TxOut};
use common::{close_at, refund, setup};
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;

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
    close_at(&rt, &spec, &chain.close_empty(&member, 2).unwrap(), 2, "empty");

    // period 3: skipped. The pinned burn opens at H_3 + grace.
    let b = spec.burn_from(3);
    let burn = chain.burn(3).unwrap();
    rt.mine_to_height(b - 2).unwrap();
    assert!(rt.mine_with(std::slice::from_ref(&burn)).is_err(), "the burn must wait for H_3 + grace");
    rt.mine_to_height(b - 1).unwrap();
    // nobody can redirect the burn leaf: a self-payment without the
    // ceremony's signature fails
    {
        let tree = chain.seal_tree(3).unwrap();
        let leaf = tree.leaf("burn").unwrap();
        let mut steal = build_spend(chain.seal_outpoint(3).unwrap(), &leaf.timelock, refund(spec.output_value(3)));
        let thief = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[0x77; 32]).unwrap());
        let prev = chain.seal_txout(3).unwrap();
        let sig = sign_tapscript(&thief, &steal, 0, std::slice::from_ref(&prev), &leaf.script).unwrap();
        steal.input[0].witness = tapscript_witness(&[sig.as_ref().to_vec()], &leaf.script, &tree.control_block("burn").unwrap());
        assert!(rt.test_accept(&steal).is_err(), "the burn leaf pays only the pinned burn");
    }
    // the race: the pre-signed closing is still valid now, as is the burn
    let late = chain.close(&member, 3, &[0xA3; 20]).unwrap();
    assert!(rt.test_accept(&late).is_ok(), "a late closing is still valid: it races the burn");
    let txid = rt.send_raw_any_fee(&burn).unwrap();
    rt.mine(1).unwrap();
    assert!(rt.confirmations(&txid).unwrap().is_some(), "the burn confirmed");
    assert!(!rt.is_unspent(&chain.seal_outpoint(3).unwrap()).unwrap(), "S_3 is spent");
    assert!(rt.test_accept(&late).is_err(), "after the burn the closing is gone");
    println!("SEAL burn (pinned): {} vB, {} sat to the miner", burn.vsize(), spec.output_value(3).to_sat());
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

    // no head start: the evidence is not spendable before race_from
    let r = spec.race_from();
    rt.mine_to_height(r - 2).unwrap();
    let slash = chain.slash(1, &sig_a, &sig_b).unwrap();
    assert!(rt.mine_with(std::slice::from_ref(&slash)).is_err(), "the slash must wait for race_from");
    rt.mine_to_height(r - 1).unwrap();
    // the same root twice is not evidence
    let same = chain.slash(1, &sig_a, &sig_a).unwrap();
    assert!(rt.mine_with(std::slice::from_ref(&same)).is_err(), "one root presented twice must not slash");
    // a pair for a different period's key fails
    let wrong = chain.slash(2, &sig_a, &sig_b).unwrap();
    assert!(rt.mine_with(std::slice::from_ref(&wrong)).is_err(), "period-1 signatures are not evidence under period 2's key");
    // the pinned slash: everything to fees
    let txid = rt.send_raw_any_fee(&slash).unwrap();
    rt.mine(1).unwrap();
    assert!(rt.confirmations(&txid).unwrap().is_some(), "the slash confirmed");
    println!("SEAL slash (pinned): {} vB, {} sat to the miner", slash.vsize(), spec.output_value(4).to_sat());
}

#[test]
fn an_honest_term_is_reclaimed_after_release() {
    let rt = Regtest::start().unwrap();
    let (spec, member, chain) = setup(&rt, 3);
    for k in 1..=spec.periods {
        close_at(&rt, &spec, &chain.close(&member, k, &[k as u8; 20]).unwrap(), k, "root");
    }
    let k = spec.periods + 1;
    let out = vec![TxOut {
        value: spec.output_value(k) - Amount::from_sat(2_000),
        script_pubkey: ScriptBuf::new_p2tr(SECP256K1, member.keypair().x_only_public_key().0, None),
    }];
    rt.mine_to_height(spec.release() - 2).unwrap();
    assert!(rt.test_accept(&chain.reclaim(&member, out.clone()).unwrap()).is_err(), "no reclaim before release");
    rt.mine_to_height(spec.release() - 1).unwrap();
    let tx = chain.reclaim(&member, out).unwrap();
    rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("the reclaim must mine at release: {e:#}"));
    println!("SEAL reclaim: {} vB", tx.vsize());
}
