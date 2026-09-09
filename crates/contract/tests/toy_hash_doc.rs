//! The toy hash from docs/planning/research/HASH_IN_SCRIPT.md (private planning
//! area), built opcode for opcode and run
//! on regtest. If this test passes, the listing in the doc is correct.
//!
//! ToyHash over 2-bit digits ("crumbs"): state (a, b), block (m0, m1),
//! two rounds of  t = a XOR m_i;  a' = (b + t) mod 4;  b' = t.

use bitcoin::opcodes::all::*;
use bitcoin::script::{Builder, ScriptBuf};
use bitcoin::{Amount, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;

fn toy_hash(a: u8, b: u8, m: [u8; 2]) -> (u8, u8) {
    let (mut a, mut b) = (a, b);
    for mi in m {
        let t = a ^ mi;
        a = (b + t) % 4;
        b = t;
    }
    (a, b)
}

fn num(b: Builder, v: u8) -> Builder {
    if v == 0 { b.push_opcode(OP_PUSHBYTES_0) } else { b.push_int(i64::from(v)) }
}

/// One round: stack (top right) [T, ..., m_i at depth 2, b, a] -> [T, ..., m_i, b', a'].
/// `above` = items between the table top and m_i (0 in round 0 when m1 is below m0... see doc).
fn round(mut s: Builder, above_table_after_pop: u8) -> Builder {
    s = s.push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_DUP).push_opcode(OP_ADD); // 4a
    s = s.push_int(2).push_opcode(OP_PICK).push_opcode(OP_ADD); // + m_i = index k
    s = num(s, above_table_after_pop).push_opcode(OP_ADD).push_opcode(OP_PICK); // t = T[k]
    s = s.push_opcode(OP_TUCK).push_opcode(OP_ADD); // [.., t, b + t]
    s = s.push_opcode(OP_DUP).push_int(4).push_opcode(OP_GREATERTHANOREQUAL).push_opcode(OP_IF).push_int(4).push_opcode(OP_SUB).push_opcode(OP_ENDIF); // mod 4
    s.push_int(2).push_opcode(OP_ROLL).push_opcode(OP_DROP) // drop the used m_i
}

/// The whole script for "ToyHash(a, b, m0, m1) == expected", witness = [m1, m0, b, a] (a on top).
fn toy_hash_script(expected: (u8, u8)) -> ScriptBuf {
    let mut s = Builder::new();
    // 1. the XOR table for crumbs, index k = 4x + y, pushed so that T[0] ends on top
    for k in (0..16u8).rev() {
        s = num(s, (k >> 2) ^ (k & 3));
    }
    // 2. bring the four inputs above the table (they were pushed before it)
    for _ in 0..4 {
        s = s.push_int(19).push_opcode(OP_ROLL);
    }
    // 3. two unrolled rounds
    s = round(s, 3); // above the table after popping k: m1, m0, b
    s = round(s, 2); // above the table after popping k: m1, b'
    // 4. park the output, drop the table, restore
    s = s.push_opcode(OP_TOALTSTACK).push_opcode(OP_TOALTSTACK);
    for _ in 0..8 {
        s = s.push_opcode(OP_2DROP);
    }
    s = s.push_opcode(OP_FROMALTSTACK).push_opcode(OP_FROMALTSTACK);
    // 5. compare with the expected (a on top)
    s = num(s, expected.0).push_opcode(OP_EQUALVERIFY);
    s = num(s, expected.1).push_opcode(OP_EQUALVERIFY);
    s.push_opcode(OP_PUSHNUM_1).into_script()
}

#[test]
fn toy_hash_script_matches_the_doc() {
    let rt = Regtest::start().unwrap();
    let (a, b, m) = (2u8, 1u8, [3u8, 0u8]);
    let expected = toy_hash(a, b, m);
    assert_eq!(expected, (3, 2), "hand-traced value in the doc");
    let leaf = toy_hash_script(expected);
    println!("ASM:\n{}", leaf.to_asm_string());
    println!("SIZE: {} bytes", leaf.len());
    let tree = TapTree::new(vec![Leaf::new("toy", leaf.clone(), Timelock::NONE)]).unwrap();
    let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
    let spend = |inputs: [u8; 4]| {
        let (op, _p) = rt.fund(&tree.script_pubkey(), Amount::from_sat(20_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(19_000), script_pubkey: sink.clone() }]);
        let mut w = WitnessStack::new();
        // consumption order: a, b, m0, m1
        for v in inputs {
            w.push(if v == 0 { vec![] } else { vec![v] });
        }
        tx.input[0].witness = w.build(&leaf, &tree.control_block("toy").unwrap());
        tx
    };
    let good = spend([a, b, m[0], m[1]]);
    rt.test_accept(&good).expect("correct inputs hash to the expected value");
    assert!(rt.test_accept(&spend([a, b, m[0], 1])).is_err(), "different block");
    assert!(rt.test_accept(&spend([a, 2, m[0], m[1]])).is_err(), "different state");
    // exhaustive: the script agrees with the native function on every input
    for x in 0..4u8 {
        for y in 0..4u8 {
            for m0 in 0..4u8 {
                for m1 in 0..4u8 {
                    let ok = toy_hash(x, y, [m0, m1]) == expected;
                    assert_eq!(rt.test_accept(&spend([x, y, m0, m1])).is_ok(), ok, "inputs {x} {y} {m0} {m1}");
                }
            }
        }
    }
    rt.send_and_confirm(&good).unwrap();
}
