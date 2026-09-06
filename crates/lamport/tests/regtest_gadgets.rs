//! Every gadget executed by the real interpreter (regtest `testmempoolaccept`),
//! positive and negative. Also the M0 deliverable: a spend through a leaf that
//! decodes an 8-bit Lamport value and enforces `value > 100`.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, Transaction, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock, FIXED_FEE};
use lngap_btc::witness::WitnessStack;
use lngap_lamport::gadgets::LamportExt;
use lngap_lamport::{Reveal, SecretKey};

struct Fixture {
    rt: Regtest,
    tree: TapTree,
    sink: ScriptBuf,
}

impl Fixture {
    fn new(leaves: Vec<Leaf>) -> Fixture {
        let rt = Regtest::start().unwrap();
        let tree = TapTree::new(leaves).unwrap();
        let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)])
            .unwrap()
            .script_pubkey();
        Fixture { rt, tree, sink }
    }
    /// Fund the tree and build a spend through `leaf` with the given witness
    /// (consumption order). Returns the tx, ready for test_accept.
    fn spend(&self, leaf: &str, args: &[Vec<u8>]) -> Transaction {
        let value = Amount::from_sat(20_000);
        let (op, _prev) = self.rt.fund(&self.tree.script_pubkey(), value).unwrap();
        let l = self.tree.leaf(leaf).unwrap();
        let mut tx = build_spend(op, &l.timelock, vec![TxOut { value: value - FIXED_FEE, script_pubkey: self.sink.clone() }]);
        let mut w = WitnessStack::new();
        w.extend(args.iter().cloned());
        tx.input[0].witness = w.build(&l.script, &self.tree.control_block(leaf).unwrap());
        tx
    }
    fn accepts(&self, leaf: &str, args: &[Vec<u8>]) -> Result<u64, String> {
        self.rt.test_accept(&self.spend(leaf, args))
    }
}

#[test]
fn m0_decode_uint_greater_than_100() {
    let sk = SecretKey::from_entropy(8, [9u8; 32]);
    let pk = sk.public();
    let leaf = Builder::new().decode_uint(&pk).push_int(100).push_opcode(OP_GREATERTHAN).into_script();
    let f = Fixture::new(vec![Leaf::new("gt100", leaf.clone(), Timelock::NONE)]);
    eprintln!("gt100 leaf: {} bytes script", leaf.len());

    // positive: 150 > 100, confirmed on-chain for real
    let r = sk.reveal_uint(150).unwrap();
    let tx = f.spend("gt100", &r.consumption_order());
    let (txid, h) = f.rt.send_and_confirm(&tx).unwrap();
    eprintln!("M0 deliverable: {txid} confirmed at height {h}, witness {} bytes", tx.input[0].witness.size());
    // boundary
    assert!(f.accepts("gt100", &sk.reveal_uint(101).unwrap().consumption_order()).is_ok());
    assert!(f.accepts("gt100", &sk.reveal_uint(255).unwrap().consumption_order()).is_ok());
    // negative: value not > 100
    assert!(f.accepts("gt100", &sk.reveal_uint(100).unwrap().consumption_order()).is_err());
    assert!(f.accepts("gt100", &sk.reveal_uint(0).unwrap().consumption_order()).is_err());
    // negative: a wrong preimage for one bit
    let mut r = sk.reveal_uint(200).unwrap();
    r.preimages[3][0] ^= 1;
    assert!(f.accepts("gt100", &r.consumption_order()).is_err());
    // negative: missing element
    let r = sk.reveal_uint(200).unwrap();
    let mut args = r.consumption_order();
    args.pop();
    assert!(f.accepts("gt100", &args).is_err());
    // negative: reversed order (lsb on top) decodes to a different number for asymmetric values
    let r = sk.reveal_uint(0b1000_0000).unwrap(); // 128 msb-first; reversed = 1
    let mut args = r.consumption_order();
    args.reverse();
    assert!(f.accepts("gt100", &args).is_err());
    // negative: a different key's preimages
    let other = SecretKey::from_entropy(8, [10u8; 32]);
    assert!(f.accepts("gt100", &other.reveal_uint(200).unwrap().consumption_order()).is_err());
}

#[test]
fn expect_uint_and_equivocation() {
    let sk = SecretKey::from_entropy(5, [3u8; 32]);
    let pk = sk.public();
    let leaves = vec![
        Leaf::new("expect_21", Builder::new().expect_uint(&pk, 21).push_int(1).into_script(), Timelock::NONE),
        Leaf::new("equiv_bit2", Builder::new().equivocation(&pk.bits[2]).push_int(1).into_script(), Timelock::NONE),
        Leaf::new("bit2", Builder::new().bit_decode(&pk.bits[2]).into_script(), Timelock::NONE),
    ];
    let f = Fixture::new(leaves);

    // expect_uint: exact value passes, any other fails
    assert!(f.accepts("expect_21", &sk.reveal_uint(21).unwrap().consumption_order()).is_ok());
    assert!(f.accepts("expect_21", &sk.reveal_uint(20).unwrap().consumption_order()).is_err());
    assert!(f.accepts("expect_21", &sk.reveal_uint(5).unwrap().consumption_order()).is_err());
    let short = Reveal { preimages: sk.reveal_uint(21).unwrap().preimages[1..].to_vec() };
    assert!(f.accepts("expect_21", &short.consumption_order()).is_err());

    // bit_decode: leaves the bit; a leaf ending in the bit is satisfiable only for bit = 1
    assert!(f.accepts("bit2", &[sk.bits[2].p1.to_vec()]).is_ok());
    assert!(f.accepts("bit2", &[sk.bits[2].p0.to_vec()]).is_err(), "bit 0 leaves a false top element");
    assert!(f.accepts("bit2", &[sk.bits[3].p1.to_vec()]).is_err(), "other bit's preimage");

    // equivocation: needs both preimages; witness p0 then p1 with p1 consumed first
    assert!(f.accepts("equiv_bit2", &[sk.bits[2].p1.to_vec(), sk.bits[2].p0.to_vec()]).is_ok());
    assert!(f.accepts("equiv_bit2", &[sk.bits[2].p0.to_vec(), sk.bits[2].p1.to_vec()]).is_err(), "order matters");
    assert!(f.accepts("equiv_bit2", &[sk.bits[2].p1.to_vec(), sk.bits[2].p1.to_vec()]).is_err(), "same preimage twice");
}
