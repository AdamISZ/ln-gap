//! V25_POC_PLAN.md Phase 2 on regtest: connectors and the connector tree.
//!
//! A GATED transaction stands in for a contract's rebuttal through a
//! member: pre-signed before anything happens, it spends a contract output
//! AND one leaf connector of the member's closing (with the mover's
//! preimage). The contract's signature commits to both inputs, so the
//! gated transaction is valid only if that leaf exists, which needs the
//! member's closing confirmed and the leaf's path unfolded.
//!
//! - the gated transaction is rejected before the closing and before its
//!   path is unfolded, and mines after;
//! - a second leaf of the same closing serves a second contract: its path
//!   reuses the splits already on chain;
//! - a burned period has no connector: the path cannot start;
//! - third parties cannot spend the tree's internal outputs, nor a leaf
//!   without its preimage.
//!
//! Run with `--test-threads=1` or 2: each test starts its own node.

mod common;

use bitcoin::key::Keypair;
use bitcoin::script::Builder;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{absolute, Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxOut};
use common::{close_at, mine_missing, refund, setup};
use lngap_btc::regtest::Regtest;
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, build_tx, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_seal::{node_tree, Member, PresignedChain};

/// A stand-in contract output: one leaf, `<alice> CHECKSIG`.
struct Contract {
    alice: Keypair,
    tree: TapTree,
    op: OutPoint,
    out: TxOut,
}

fn contract(rt: &Regtest, seed: u8) -> Contract {
    let alice = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[seed; 32]).unwrap());
    let tree = TapTree::new(vec![Leaf::new(
        "pay",
        Builder::new().checksig(&alice.x_only_public_key().0).into_script(),
        Timelock::NONE,
    )])
    .unwrap();
    let (op, out) = rt.fund(&tree.script_pubkey(), Amount::from_sat(50_000)).unwrap();
    Contract { alice, tree, op, out }
}

/// The gated transaction, pre-signed by the contract's key BEFORE the leaf
/// exists: inputs (contract output, leaf connector (k, s)).
fn gated(c: &Contract, chain: &PresignedChain, member: &Member, k: u32, s: u32) -> Transaction {
    let (leaf_op, leaf_out) = chain.leaf_connector(k, s).unwrap();
    let pay = TxOut {
        value: c.out.value + leaf_out.value - Amount::from_sat(1_500),
        script_pubkey: ScriptBuf::new_p2tr(SECP256K1, c.alice.x_only_public_key().0, None),
    };
    let mut tx = build_tx(
        &[(c.op, Sequence::ENABLE_RBF_NO_LOCKTIME), (leaf_op, Sequence::ENABLE_RBF_NO_LOCKTIME)],
        vec![pay],
        absolute::LockTime::ZERO,
    );
    let leaf = c.tree.leaf("pay").unwrap();
    let sig = sign_tapscript(&c.alice, &tx, 0, &[c.out.clone(), leaf_out], &leaf.script).unwrap();
    tx.input[0].witness = tapscript_witness(&[sig.as_ref().to_vec()], &leaf.script, &c.tree.control_block("pay").unwrap());
    // the mover's preimage, handed out by the member at registration
    tx.input[1].witness = chain.leaf_witness(k, s, &member.leaf_preimage(k, s)).unwrap();
    tx
}

#[test]
fn a_leaf_connector_proves_the_closing() {
    let rt = Regtest::start().unwrap();
    let (spec, member, chain) = setup(&rt, 11);
    let c1 = contract(&rt, 0x21);
    let c2 = contract(&rt, 0x22);
    let g1 = gated(&c1, &chain, &member, 1, 2);
    let g2 = gated(&c2, &chain, &member, 1, 5);

    // before the closing: no connector, so neither the path nor the gated tx
    let path1 = chain.connector_path(1, 2).unwrap();
    assert!(rt.test_accept(&path1[0]).is_err(), "the root split needs the closing's connector");
    assert!(rt.test_accept(&g1).is_err(), "the gated tx needs its leaf");

    close_at(&rt, &spec, &chain.close(&member, 1, &[0x5A; 20]).unwrap(), 1, "root");
    assert!(rt.test_accept(&g1).is_err(), "the closing alone does not create the leaf");

    // unfold leaf 2's path, then the gated tx mines
    let n = mine_missing(&rt, &path1);
    assert_eq!(n, spec.fanout_depth as usize);
    let split_vb: Vec<usize> = path1.iter().map(|t| t.vsize()).collect();
    rt.mine_with(std::slice::from_ref(&g1)).unwrap_or_else(|e| panic!("the gated tx must mine once its leaf exists: {e:#}"));
    println!(
        "SEAL connector path to leaf 2: {} splits, {:?} vB (total {} vB); gated tx {} vB",
        n,
        split_vb,
        split_vb.iter().sum::<usize>(),
        g1.vsize()
    );

    // a second contract uses leaf 5: its path shares the root split
    let path2 = chain.connector_path(1, 5).unwrap();
    assert_eq!(path2[0].compute_txid(), path1[0].compute_txid(), "leaves 2 and 5 share the root split");
    let n2 = mine_missing(&rt, &path2);
    assert_eq!(n2, spec.fanout_depth as usize - 1, "only the splits below the shared root are new");
    rt.mine_with(std::slice::from_ref(&g2)).unwrap_or_else(|e| panic!("the second gated tx must mine: {e:#}"));
    println!("SEAL second leaf of the same closing: {n2} new splits");
}

#[test]
fn a_burned_period_has_no_connector() {
    let rt = Regtest::start().unwrap();
    let (spec, member, chain) = setup(&rt, 12);
    let c = contract(&rt, 0x23);
    let g = gated(&c, &chain, &member, 1, 0);
    // period 1 is skipped and burned
    rt.mine_to_height(spec.burn_from(1) - 1).unwrap();
    rt.send_raw_any_fee(&chain.burn(1).unwrap()).unwrap();
    rt.mine(1).unwrap();
    let path = chain.connector_path(1, 0).unwrap();
    assert!(rt.mine_with(std::slice::from_ref(&path[0])).is_err(), "no closing, no connector: the path cannot start");
    assert!(rt.test_accept(&g).is_err(), "the gated tx can never become valid");
}

#[test]
fn the_tree_resists_third_parties() {
    let rt = Regtest::start().unwrap();
    let (spec, member, chain) = setup(&rt, 13);
    close_at(&rt, &spec, &chain.close(&member, 1, &[0x5B; 20]).unwrap(), 1, "root");
    let thief = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[0x66; 32]).unwrap());
    // the connector κ_1: only its pinned split
    {
        let node = node_tree(&chain.closings[0].split_key).unwrap();
        let leaf = node.leaf("split").unwrap();
        let prev = TxOut { value: spec.connector_value(), script_pubkey: node.script_pubkey() };
        let mut steal = build_spend(chain.connector_outpoint(1).unwrap(), &Timelock::NONE, refund(spec.connector_value()));
        let sig = sign_tapscript(&thief, &steal, 0, std::slice::from_ref(&prev), &leaf.script).unwrap();
        steal.input[0].witness = tapscript_witness(&[sig.as_ref().to_vec()], &leaf.script, &node.control_block("split").unwrap());
        assert!(rt.test_accept(&steal).is_err(), "a connector node is spendable only by its pinned split");
    }
    // a leaf without its preimage
    mine_missing(&rt, &chain.connector_path(1, 3).unwrap());
    let (op, out) = chain.leaf_connector(1, 3).unwrap();
    let mut steal = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::ZERO, script_pubkey: ScriptBuf::new_op_return(b"x-steal-leaf-xx") }]);
    steal.input[0].witness = chain.leaf_witness(1, 3, &[0u8; 32]).unwrap();
    assert!(rt.test_accept(&steal).is_err(), "a leaf needs its preimage");
    assert_eq!(out.value, spec.leaf_value);
}
