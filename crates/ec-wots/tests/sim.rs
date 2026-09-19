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
