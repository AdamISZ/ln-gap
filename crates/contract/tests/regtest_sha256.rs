//! The embedded BitVM SHA-256 runs in a leaf on regtest: hash a 32-byte
//! message and require the digest to equal a constant.

use bitcoin::script::Builder;
use bitcoin::{Amount, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_contract::script_hash::{message_witness, sha256_equals, sha256_script};
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
