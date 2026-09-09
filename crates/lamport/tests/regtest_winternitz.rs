//! The Winternitz verify gadget through the interpreter.
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{Amount, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_btc::hash160;
use lngap_lamport::winternitz::{message_digits, WotsExt, WotsParams, WotsSecret};

#[test]
fn winternitz_leaf_on_regtest() {
    let rt = Regtest::start().unwrap();
    let ps = WotsParams::for_bytes(32);
    let sk = WotsSecret::from_entropy(ps, [3u8; 32]);
    let pk = sk.public();
    let msg: Vec<u8> = (0..32u8).map(|i| i.wrapping_mul(59).wrapping_add(1)).collect();
    // leaf: verify, then require the 64 digits equal the message's nibbles (last nibble on top)
    let mut b = Builder::new().wots_verify(&pk);
    for n in message_digits(&msg).iter().rev() {
        b = if *n == 0 { b.push_opcode(OP_PUSHBYTES_0) } else { b.push_int(i64::from(*n)) };
        b = b.push_opcode(OP_EQUALVERIFY);
    }
    let leaf = b.push_opcode(OP_PUSHNUM_1).into_script();
    eprintln!("SIZE wots verify leaf: {} bytes", leaf.len());
    let tree = TapTree::new(vec![Leaf::new("w", leaf.clone(), Timelock::NONE)]).unwrap();
    let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
    let spend = |items: Vec<Vec<u8>>| {
        let (op, _p) = rt.fund(&tree.script_pubkey(), Amount::from_sat(50_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(40_000), script_pubkey: sink.clone() }]);
        let mut w = WitnessStack::new();
        w.extend(items);
        tx.input[0].witness = w.build(&leaf, &tree.control_block("w").unwrap());
        tx
    };
    let sig = sk.sign(&msg).unwrap();
    let tx = spend(sig.consumption_order());
    let vs = rt.test_accept(&tx).unwrap();
    eprintln!("wots accepted: vsize {vs}, witness {} bytes", tx.input[0].witness.size());
    // wrong message
    let mut other = msg.clone();
    other[7] ^= 0x30;
    assert!(rt.test_accept(&spend(sk.sign(&other).unwrap().consumption_order())).is_err());
    // forgery: bump one digit by hashing its signature once more, checksum untouched
    let mut forged = sig.clone();
    forged.digits[10] += 1;
    forged.hashes[10] = hash160(&forged.hashes[10]);
    assert!(rt.test_accept(&spend(forged.consumption_order())).is_err(), "forged digit must fail the checksum");
    rt.send_and_confirm(&tx).unwrap();
}
