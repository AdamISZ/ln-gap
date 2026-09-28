//! A commitment to a small number that Script can open without `OP_CAT`
//! (for the blackjack design in the paper): the value is the LENGTH of a
//! random string. Commit `C = SHA256(s)` with `|s| = BASE + v`; to open,
//! reveal `s`; the script checks the hash and reads `v` back with
//! `OP_SIZE`. Hiding: `s` is random and the hash hides its length. Binding:
//! a second opening of a different length would be a SHA256 collision
//! (HASH160's 2^80 collision bound is too low for a committer with time to
//! grind, hence SHA256).
//!
//! The leaf here is the dealing check: two parties' shares `v`, `w` in
//! 0..=12 were committed at open; the card is `(v + w) mod 13`. The
//! positive form (`card_is`) spends iff both reveals open their
//! commitments, both shares are in range, and the card equals the claimed
//! rank; the disprove form (`card_is_not`) spends iff the claimed rank is
//! WRONG. On regtest: correct spends mine; a wrong preimage, a string one
//! byte longer (the "other value"), an out-of-range share and a wrong
//! claimed card are each rejected.

use bitcoin::hashes::{sha256, Hash};
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, TxOut};
use lngap_btc::keys::{xonly, Seed};
use lngap_btc::regtest::Regtest;
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock, FIXED_FEE};
use lngap_btc::witness::WitnessStack;

/// Bytes of randomness a share of 0 still carries.
const BASE: i64 = 32;
const RANKS: i64 = 13;

/// A share's opening: `BASE + v` bytes, deterministic here (hiding is not
/// what the test is about).
fn opening(tag: u8, v: i64) -> Vec<u8> {
    (0..(BASE + v) as usize).map(|i| tag.wrapping_mul(31).wrapping_add(i as u8)).collect()
}

fn commit(s: &[u8]) -> [u8; 32] {
    sha256::Hash::hash(s).to_byte_array()
}

/// `<s> -> v`: check `SHA256(s) == c`, then `v = |s| - BASE` in `0..RANKS`.
fn open_share(b: Builder, c: &[u8; 32]) -> Builder {
    b.push_opcode(OP_DUP)
        .push_opcode(OP_SHA256)
        .push_bytes(c)
        .push_opcode(OP_EQUALVERIFY)
        .push_opcode(OP_SIZE)
        .push_opcode(OP_NIP)
        .push_int(BASE)
        .push_opcode(OP_SUB)
        .push_opcode(OP_DUP)
        .push_int(0)
        .push_int(RANKS)
        .push_opcode(OP_WITHIN)
        .push_opcode(OP_VERIFY)
}

/// Witness `[sig, s_b, s_a]` bottom to top (s_a on top; `WitnessStack`'s
/// first push is the top) -> the card `(v_a + v_b) mod 13`
/// on the stack above `sig`.
fn card(c_a: &[u8; 32], c_b: &[u8; 32]) -> Builder {
    let b = open_share(Builder::new(), c_a).push_opcode(OP_SWAP);
    open_share(b, c_b)
        .push_opcode(OP_ADD)
        .push_opcode(OP_DUP)
        .push_int(RANKS)
        .push_opcode(OP_GREATERTHANOREQUAL)
        .push_opcode(OP_IF)
        .push_int(RANKS)
        .push_opcode(OP_SUB)
        .push_opcode(OP_ENDIF)
}

fn sink() -> ScriptBuf {
    TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey()
}

#[test]
fn size_commitment_card_leaf() {
    let rt = Regtest::start().unwrap();
    let key = Seed::from_label("dealer-check").keypair("t");
    let x = xonly(&key);
    // the shares committed at open: v = 9 (Alice), w = 7 (Bob): card (9 + 7) mod 13 = 3
    let (v, w) = (9i64, 7i64);
    let (s_a, s_b) = (opening(0xA1, v), opening(0xB2, w));
    let (c_a, c_b) = (commit(&s_a), commit(&s_b));
    let rank = (v + w) % RANKS;
    assert_eq!(rank, 3);

    let card_is = card(&c_a, &c_b).push_int(rank).push_opcode(OP_EQUALVERIFY).checksig(&x).into_script();
    let card_is_not = card(&c_a, &c_b).push_int(rank + 1).push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_VERIFY).checksig(&x).into_script();
    let claims_wrong = card(&c_a, &c_b).push_int(rank + 1).push_opcode(OP_EQUALVERIFY).checksig(&x).into_script();
    let tree = TapTree::new(vec![
        Leaf::new("card_is", card_is, Timelock::NONE),
        Leaf::new("card_is_not", card_is_not, Timelock::NONE),
        Leaf::new("claims_wrong", claims_wrong, Timelock::NONE),
    ])
    .unwrap();
    let value = Amount::from_sat(50_000);
    let out = vec![TxOut { value: value - FIXED_FEE, script_pubkey: sink() }];

    let spend = |leaf: &str, s_a: &[u8], s_b: &[u8]| {
        let (op, prevout) = rt.fund(&tree.script_pubkey(), value).unwrap();
        let l = tree.leaf(leaf).unwrap();
        let mut tx = build_spend(op, &l.timelock, out.clone());
        let sig = sign_tapscript(&key, &tx, 0, std::slice::from_ref(&prevout), &l.script).unwrap();
        tx.input[0].witness = WitnessStack::new().push(s_a.to_vec()).push(s_b.to_vec()).push(sig.as_ref().to_vec()).build(&l.script, &tree.control_block(leaf).unwrap());
        tx
    };

    // the correct openings and the correct card: mines
    let tx = spend("card_is", &s_a, &s_b);
    rt.send_and_confirm(&tx).unwrap();
    eprintln!("card_is spend: {} vB, leaf {} bytes", tx.vsize(), tree.leaf("card_is").unwrap().script.len());

    // a wrong preimage (same length: the value "unchanged", the hash not)
    let mut bad = s_a.clone();
    bad[0] ^= 1;
    assert!(rt.test_accept(&spend("card_is", &bad, &s_b)).is_err(), "a wrong preimage must not open the commitment");

    // the other value: a string one byte longer does not hash to the commitment
    let mut longer = s_a.clone();
    longer.push(0);
    assert!(rt.test_accept(&spend("card_is", &longer, &s_b)).is_err(), "a different length (another value) must not open the commitment");

    // a wrong claimed card: the positive form rejects it...
    assert!(rt.test_accept(&spend("claims_wrong", &s_a, &s_b)).is_err(), "a wrong claimed card must be rejected");
    // ...and the disprove form fires on it
    let tx = spend("card_is_not", &s_a, &s_b);
    rt.send_and_confirm(&tx).unwrap();
    eprintln!("card_is_not (disprove) spend: {} vB", tx.vsize());

    // an out-of-range share: committed honestly, but v = 13 fails the range check
    let s_big = opening(0xC3, 13);
    let c_big = commit(&s_big);
    let over = card(&c_big, &c_b).push_opcode(OP_DROP).checksig(&x).into_script();
    let t2 = TapTree::new(vec![Leaf::new("over", over, Timelock::NONE)]).unwrap();
    let (op, prevout) = rt.fund(&t2.script_pubkey(), value).unwrap();
    let l = t2.leaf("over").unwrap();
    let mut tx = build_spend(op, &l.timelock, out.clone());
    let sig = sign_tapscript(&key, &tx, 0, std::slice::from_ref(&prevout), &l.script).unwrap();
    tx.input[0].witness = WitnessStack::new().push(s_big).push(s_b.clone()).push(sig.as_ref().to_vec()).build(&l.script, &t2.control_block("over").unwrap());
    assert!(rt.test_accept(&tx).is_err(), "a share outside 0..=12 must fail the range check");
}
