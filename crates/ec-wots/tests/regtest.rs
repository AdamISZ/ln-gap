//! EC-WOTS as real tapscript spends on regtest: a readout leaf attesting a
//! 32-bit and a full 256-bit message, the negative paths (wrong claim, wrong
//! index, empty signature), and the equivocation slash leaf both ways.
//! Prints script/witness/vsize measurements against EC_WOTS.md's predictions.

use bitcoin::hashes::Hash;
use bitcoin::key::Keypair;
use bitcoin::script::Builder;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, ScriptBuf, Transaction, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_ec_wots::{
    readout_leaf, readout_witness_args, slash_leaf, slash_witness_args, Attestation, Attester,
    EpochTable,
};

struct Spend {
    tree: TapTree,
    tx: Transaction,
    prev: TxOut,
    leaf: ScriptBuf,
}

fn sink() -> ScriptBuf {
    TapTree::new(vec![Leaf::new(
        "x",
        Builder::new().push_int(1).into_script(),
        Timelock::NONE,
    )])
    .unwrap()
    .script_pubkey()
}

fn prepare(rt: &Regtest, leaf: ScriptBuf) -> Spend {
    let tree = TapTree::new(vec![Leaf::new("r", leaf.clone(), Timelock::NONE)]).unwrap();
    let (op, prev) = rt
        .fund(&tree.script_pubkey(), Amount::from_sat(200_000))
        .unwrap();
    let tx = build_spend(
        op,
        &Timelock::NONE,
        vec![TxOut {
            value: Amount::from_sat(150_000),
            script_pubkey: sink(),
        }],
    );
    Spend {
        tree,
        tx,
        prev,
        leaf,
    }
}

fn sign_with(secret: &SecretKey, sp: &Spend) -> Vec<u8> {
    let kp = Keypair::from_secret_key(SECP256K1, secret);
    sign_tapscript(&kp, &sp.tx, 0, std::slice::from_ref(&sp.prev), &sp.leaf)
        .unwrap()
        .as_ref()
        .to_vec()
}

fn finish(sp: &Spend, args: Vec<Vec<u8>>) -> Transaction {
    let mut tx = sp.tx.clone();
    tx.input[0].witness = tapscript_witness(&args, &sp.leaf, &sp.tree.control_block("r").unwrap());
    tx
}

fn readout_spend(
    rt: &Regtest,
    table: &EpochTable,
    att: &Attestation,
    msg: &[u8],
    claimed: &[u8],
) -> (Transaction, usize, usize) {
    let leaf = readout_leaf(table);
    let sp = prepare(rt, leaf.clone());
    let sigs: Vec<Vec<u8>> = att.secrets.iter().map(|s| sign_with(s, &sp)).collect();
    let args = readout_witness_args(table, msg, claimed, &sigs);
    let arg_bytes: usize = args.iter().map(|a| a.len()).sum();
    (finish(&sp, args), leaf.len(), arg_bytes)
}

#[test]
fn ec_wots_on_regtest() {
    let rt = Regtest::start().unwrap();
    let att = Attester::new([7u8; 32]);

    // ---- happy path, 8 chunks (a 32-bit message) ----
    let table = att.epoch_table(3, 8);
    let msg = [0xde, 0xad, 0xbe, 0xef];
    let attestation = att.attest(&table, &msg);
    assert!(
        attestation.verify(&table, &msg),
        "off-chain consistency: secrets open the points"
    );
    let (tx, leaf_bytes, arg_bytes) = readout_spend(&rt, &table, &attestation, &msg, &msg);
    let vs = rt
        .test_accept(&tx)
        .unwrap_or_else(|e| panic!("honest readout rejected: {e}"));
    println!("REGTEST readout 8 chunks: leaf {leaf_bytes} B, witness args {arg_bytes} B, spend vsize {vs}");

    // ---- happy path, 64 chunks (a 256-bit message, the full construction) ----
    let table64 = att.epoch_table(4, 64);
    let msg64: [u8; 32] =
        bitcoin::hashes::sha256::Hash::hash(b"canonical publication").to_byte_array();
    let att64 = att.attest(&table64, &msg64);
    assert!(att64.verify(&table64, &msg64));
    let (tx64, leaf64, arg64) = readout_spend(&rt, &table64, &att64, &msg64, &msg64);
    let vs64 = rt
        .test_accept(&tx64)
        .unwrap_or_else(|e| panic!("honest 256-bit readout rejected: {e}"));
    println!("REGTEST readout 64 chunks: leaf {leaf64} B, witness args {arg64} B, spend vsize {vs64} (~{} WU)", vs64 * 4);
    // the sigops budget of BIP342: 50 + witness bytes, -50 per CHECKSIG
    let witness_bytes = tx64.input[0].witness.size();
    let budget = 50 + witness_bytes as u64;
    assert!(
        budget >= 64 * 50,
        "sigops budget {budget} must cover 64 checks"
    );
    println!(
        "REGTEST sigops: budget {budget}, spent 3200, headroom {}x",
        budget / 3200
    );

    // ---- wrong claim: attestation to msg, claim of a different message ----
    let mut wrong = msg;
    wrong[0] ^= 1;
    let (tx_bad, _, _) = readout_spend(&rt, &table, &attestation, &msg, &wrong);
    assert!(
        rt.test_accept(&tx_bad).is_err(),
        "a wrong claim must be rejected"
    );

    // ---- wrong index: signature under S_{0,v} but the witness says v' ----
    let leaf = readout_leaf(&table);
    let sp = prepare(&rt, leaf.clone());
    let sigs: Vec<Vec<u8>> = attestation
        .secrets
        .iter()
        .map(|s| sign_with(s, &sp))
        .collect();
    let mut args = readout_witness_args(&table, &msg, &msg, &sigs);
    // chunk 0's v is the top of the stack = the last arg
    let n = args.len();
    let v0 = lngap_ec_wots::chunk_value(&msg, 0);
    args[n - 1] = lngap_ec_wots::snum((v0 + 1) % 16);
    assert!(
        rt.test_accept(&finish(&sp, args)).is_err(),
        "a wrong index must be rejected (the signature is under a different point)"
    );

    // ---- empty signature: the possession boolean has no bypass ----
    let sp2 = prepare(&rt, leaf);
    let sigs2: Vec<Vec<u8>> = attestation
        .secrets
        .iter()
        .map(|s| sign_with(s, &sp2))
        .collect();
    let mut args2 = readout_witness_args(&table, &msg, &msg, &sigs2);
    args2[n - 2] = vec![]; // chunk 0's signature, emptied
    assert!(
        rt.test_accept(&finish(&sp2, args2)).is_err(),
        "an empty signature must be rejected"
    );

    // ---- the slash leaf: two values attested at one chunk position ----
    let mut msg2 = msg;
    msg2[0] ^= 0x10; // differs in chunk 0 (the high nibble)
    let att2 = att.attest(&table, &msg2);
    let slash = slash_leaf(
        &table,
        0,
        lngap_ec_wots::chunk_value(&msg, 0),
        lngap_ec_wots::chunk_value(&msg2, 0),
    );
    let sp3 = prepare(&rt, slash);
    let sig_a = sign_with(&attestation.secrets[0], &sp3);
    let sig_b = sign_with(&att2.secrets[0], &sp3);
    let tx3 = finish(&sp3, slash_witness_args(sig_a, sig_b));
    let vs3 = rt
        .test_accept(&tx3)
        .unwrap_or_else(|e| panic!("honest slash rejected: {e}"));
    println!("REGTEST slash: spend vsize {vs3}");

    // ---- the slash leaf with only one side attested must fail ----
    let sp4 = prepare(
        &rt,
        slash_leaf(
            &table,
            1,
            lngap_ec_wots::chunk_value(&msg, 1),
            (lngap_ec_wots::chunk_value(&msg, 1) + 1) % 16,
        ),
    );
    let sig_a4 = sign_with(&attestation.secrets[1], &sp4);
    let bogus = sign_with(&SecretKey::from_slice(&[9u8; 32]).unwrap(), &sp4);
    assert!(
        rt.test_accept(&finish(&sp4, slash_witness_args(sig_a4, bogus)))
            .is_err(),
        "a one-sided slash must be rejected"
    );
}
