//! Fast stack-choreography checks of the readout leaf through the script32
//! simulator (its CHECKSIG stub pops both elements and continues). Regtest
//! remains the source of truth for the crypto; this catches stack bugs.

use lngap_ec_wots::{readout_leaf, snum, Attester};

const DUMMY_SIG: [u8; 64] = [0x30; 64];

fn sim_stack(table_chunks: usize, attested: &[u8], claimed: &[u8]) -> Vec<Vec<u8>> {
    let args = readout_witness_args_raw(table_chunks, attested, claimed);
    args
}

fn readout_witness_args_raw(chunks: usize, attested: &[u8], claimed: &[u8]) -> Vec<Vec<u8>> {
    // wire order (bottom first), mirroring readout_witness_args with dummies
    let mut out = Vec::with_capacity(3 * chunks);
    for j in (0..chunks).rev() {
        out.push(snum(lngap_ec_wots::chunk_value(claimed, j)));
        out.push(DUMMY_SIG.to_vec());
        out.push(snum(lngap_ec_wots::chunk_value(attested, j)));
    }
    out
}

#[test]
fn readout_stack_choreography() {
    let att = Attester::new([7u8; 32]);
    let table = att.epoch_table(3, 8);
    let msg = [0xde, 0xad, 0xbe, 0xef];
    let leaf = readout_leaf(&table);
    let stack = sim_stack(8, &msg, &msg);
    let final_stack =
        lngap_script32::sim::run(leaf.as_script(), stack).expect("correct claim must run");
    assert_eq!(final_stack, vec![vec![1]], "the leaf ends with OP_1");
}

#[test]
fn readout_rejects_wrong_claim() {
    let att = Attester::new([7u8; 32]);
    let table = att.epoch_table(3, 8);
    let msg = [0xde, 0xad, 0xbe, 0xef];
    let mut wrong = msg;
    wrong[3] ^= 1;
    let leaf = readout_leaf(&table);
    let stack = sim_stack(8, &msg, &wrong);
    assert!(
        lngap_script32::sim::run(leaf.as_script(), stack).is_err(),
        "v != c must fail at EQUALVERIFY"
    );
}

#[test]
fn readout_rejects_out_of_range_value() {
    let att = Attester::new([7u8; 32]);
    let table = att.epoch_table(3, 8);
    let msg = [0xde, 0xad, 0xbe, 0xef];
    let leaf = readout_leaf(&table);
    let mut stack = sim_stack(8, &msg, &msg);
    // corrupt one v (the top element of the stack is chunk 0's v): 16 is out of range
    let n = stack.len();
    stack[n - 1] = vec![16];
    assert!(
        lngap_script32::sim::run(leaf.as_script(), stack).is_err(),
        "v = 16 must fail at OP_PICK"
    );
}

/// The TIED readout fragment (readout_tied_fragment): the chunk values come
/// off the altstack (the parked re-committed digits), the witness carries
/// only the per-chunk sigs. Choreography only — the sim's CHECKSIG stub pops
/// both elements; the crypto is the pos crate's regtest suites' job.
#[test]
fn tied_readout_stack_choreography() {
    use bitcoin::opcodes::all::*;
    use bitcoin::script::Builder;
    let att = Attester::new([7u8; 32]);
    let table = att.epoch_table(3, 8);
    let msg = [0xde, 0xad, 0xbe, 0xef];
    let digits: Vec<i64> = (0..8).map(|j| i64::from(lngap_ec_wots::chunk_value(&msg, j))).collect();
    let build = |digits: &[i64]| {
        let mut b = Builder::new();
        for &d in digits {
            b = b.push_int(d);
        }
        for _ in 0..8 {
            b = b.push_opcode(OP_TOALTSTACK);
        }
        for j in 0..8 {
            b = lngap_ec_wots::readout_tied_fragment(b, &table.points[j]);
        }
        b.push_int(1).into_script()
    };
    // witness, wire order (bottom first): the sigs, chunk 0's consumed first
    // (on top) — descending chunk order in the vec, dummy sigs
    let w: Vec<Vec<u8>> = (0..8).rev().map(|_| DUMMY_SIG.to_vec()).collect();
    let out = lngap_script32::sim::run(build(&digits).as_script(), w.clone()).expect("the tied readout must run clean");
    assert_eq!(out, vec![vec![1]], "each chunk consumes exactly its sig and digit");
    // a digit out of range fails the selection arithmetic
    let mut bad = digits.clone();
    bad[3] = 16;
    assert!(lngap_script32::sim::run(build(&bad).as_script(), w.clone()).is_err(), "16 is out of range");
    // a wrong digit runs the choreography to completion under the sim's stub
    // (the value-dependent sig check is the regtest suites' job)
    let mut wrong = digits.clone();
    wrong[3] ^= 1;
    assert!(lngap_script32::sim::run(build(&wrong).as_script(), w).is_ok());
}
