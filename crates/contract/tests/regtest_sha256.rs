//! The embedded BitVM SHA-256 runs in a leaf on regtest: hash a 32-byte
//! message and require the digest to equal a constant.

use bitcoin::script::Builder;
use bitcoin::{Amount, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_contract::script_hash::{compress_witness, message_witness, message_witness_u4, sha256_compress_equals, sha256_compress_script, sha256_equals, sha256_script, sha256_u4_equals, sha256_u4_script};
use sha2::{Digest, Sha256};

#[test]
fn sha256_leaf_on_regtest() {
    let rt = Regtest::start().unwrap();
    for n in [32usize, 64, 80] {
        let msg: Vec<u8> = (0..n as u32).map(|i| (i * 37 + 11) as u8 ^ 0x80u8.wrapping_mul((i % 3) as u8)).collect();
        let digest: [u8; 32] = Sha256::digest(&msg).into();
        let leaf = sha256_equals(Builder::new(), n, &digest).into_script();
        eprintln!("SIZE sha256({n}) leaf: {} bytes (raw script {} bytes)", leaf.len(), sha256_script(n).len());
        let tree = TapTree::new(vec![Leaf::new("h", leaf.clone(), Timelock::NONE)]).unwrap();
        let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
        let spend = |m: &[u8]| {
            // a megabyte of witness at ≥ 1 sat/vB: fund with 2 mBTC and pay ~0.5 mBTC
            let (op, _prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(2_000_000)).unwrap();
            let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(1_500_000), script_pubkey: sink.clone() }]);
            let mut w = WitnessStack::new();
            w.extend(message_witness(m));
            tx.input[0].witness = w.build(&leaf, &tree.control_block("h").unwrap());
            tx
        };
        // too big for the mempool (cluster size limit), so go straight into a block
        let mut wrong = msg.clone();
        wrong[n / 2] ^= 1;
        let bad = spend(&wrong);
        let r = rt.mine_with_check(&bad);
        assert!(r.is_err(), "wrong message must fail consensus, got {r:?}");
        eprintln!("sha256({n}) wrong message: rejected ({})", r.unwrap_err().lines().next().unwrap_or(""));
        let tx = spend(&msg);
        let h = rt.mine_with_check(&tx).unwrap_or_else(|e| panic!("sha256({n}) valid spend rejected: {e}"));
        eprintln!("sha256({n}) mined at {h}: weight {} WU, vsize {}", tx.weight(), tx.vsize());
    }
}

/// The nibble-wise variant: does one compression fit a standard transaction?
#[test]
fn sha256_u4_leaf_on_regtest() {
    let rt = Regtest::start().unwrap();
    for n in [32usize, 80] {
        let msg: Vec<u8> = (0..n as u32).map(|i| (i * 53 + 7) as u8).collect();
        let digest: [u8; 32] = Sha256::digest(&msg).into();
        let leaf = sha256_u4_equals(Builder::new(), n, &digest).into_script();
        eprintln!("SIZE sha256_u4({n}) leaf: {} bytes (raw {} bytes)", leaf.len(), sha256_u4_script(n).len());
        let tree = TapTree::new(vec![Leaf::new("h", leaf.clone(), Timelock::NONE)]).unwrap();
        let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
        let spend = |m: &[u8]| {
            let (op, _prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(2_000_000)).unwrap();
            let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(1_500_000), script_pubkey: sink.clone() }]);
            let mut w = WitnessStack::new();
            w.extend(message_witness_u4(m));
            tx.input[0].witness = w.build(&leaf, &tree.control_block("h").unwrap());
            tx
        };
        let tx = spend(&msg);
        let standard = tx.weight().to_wu() <= 400_000;
        match rt.test_accept(&tx) {
            Ok(vs) => eprintln!("sha256_u4({n}) MEMPOOL-ACCEPTED: vsize {vs}, weight {} WU, within 400 kWU standard limit: {standard}", tx.weight()),
            Err(e) => eprintln!("sha256_u4({n}) mempool rejected: {e}; weight {} WU, standard-size: {standard}", tx.weight()),
        }
        let mut wrong = msg.clone();
        wrong[1] ^= 0x10;
        let r = rt.mine_with_check(&spend(&wrong));
        assert!(r.is_err(), "wrong message must fail");
        let h = rt.mine_with_check(&tx).unwrap_or_else(|e| panic!("sha256_u4({n}) valid spend rejected: {e}"));
        eprintln!("sha256_u4({n}) mined at {h}");
    }
}

/// The bisection terminal step: one compression with an input midstate.
#[test]
fn sha256_compress_leaf_on_regtest() {
    let rt = Regtest::start().unwrap();
    let mut state = [0x6a09e667u32, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    let block0: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(31).wrapping_add(5));
    sha2::compress256(&mut state, &[block0.into()]);
    let block: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(97).wrapping_add(13));
    let mut expected = state;
    sha2::compress256(&mut expected, &[block.into()]);

    let leaf = sha256_compress_equals(Builder::new(), &expected).into_script();
    eprintln!("SIZE compress leaf: {} bytes (raw {} bytes)", leaf.len(), sha256_compress_script().len());
    let tree = TapTree::new(vec![Leaf::new("c", leaf.clone(), Timelock::NONE)]).unwrap();
    let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
    let spend = |st: &[u32; 8], bl: &[u8; 64]| {
        let (op, _prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(2_000_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(1_500_000), script_pubkey: sink.clone() }]);
        let mut w = WitnessStack::new();
        w.extend(compress_witness(st, bl));
        tx.input[0].witness = w.build(&leaf, &tree.control_block("c").unwrap());
        tx
    };
    let tx = spend(&state, &block);
    let standard = tx.weight().to_wu() <= 400_000;
    match rt.test_accept(&tx) {
        Ok(vs) => eprintln!("compress MEMPOOL-ACCEPTED: vsize {vs}, weight {} WU, standard-size: {standard}", tx.weight()),
        Err(e) => panic!("compress mempool rejected: {e}; weight {} WU", tx.weight()),
    }
    let mut wrong_state = state;
    wrong_state[3] ^= 1;
    assert!(rt.mine_with_check(&spend(&wrong_state, &block)).is_err(), "wrong midstate must fail");
    let mut wrong_block = block;
    wrong_block[40] ^= 0x80;
    assert!(rt.mine_with_check(&spend(&state, &wrong_block)).is_err(), "wrong block must fail");
    let h = rt.mine_with_check(&tx).unwrap();
    eprintln!("compress mined at {h}");
}
