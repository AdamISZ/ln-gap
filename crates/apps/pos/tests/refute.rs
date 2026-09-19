//! The refutation flow as real tapscript spends on regtest (plan step 3):
//! a venue block carrying a move is sealed under the PoS attestation; the
//! refutation spend reads the move's head out of the attestation and ties it
//! to the mover's WOTS re-commitment; the follow-on disprove spend consumes
//! the parked tuple. Prints script/witness/vsize measurements.

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_ec_wots::{Attester, EpochTable};
use lngap_factchain::slot::SlotEntry;
use lngap_pos::refute::{
    disprove_leaf_move_range, disprove_witness, refute_key, refute_leaf, refute_witness,
    HEAD_CHUNK_START, HEAD_CHUNKS,
};
use lngap_pos::{PosMiner, SealedBlock};

const SEED: [u8; 32] = [7u8; 32];

fn sink() -> ScriptBuf {
    TapTree::new(vec![Leaf::new(
        "x",
        bitcoin::script::Builder::new().push_int(1).into_script(),
        Timelock::NONE,
    )])
    .unwrap()
    .script_pubkey()
}

/// A slot-1 block whose entry's head carries the move `mv`.
fn sealed_move(mv: u8) -> (SealedBlock, EpochTable) {
    let attester = Attester::new(SEED);
    let (gen, _t0) = lngap_pos::genesis(&attester);
    let mut miner = PosMiner::new(SEED, gen.header.digest(), 0);
    let entry = SlotEntry {
        game_id: 1,
        depth: 1,
        mover: 0,
        mv,
        state: 0x12345,
        sigs: vec![[0x11; 20]; 21],
    };
    miner.submit(entry.encode());
    miner.seal_next(1).unwrap()
}

struct Funded {
    tree: TapTree,
    op: OutPoint,
    prev: TxOut,
}

fn fund(rt: &Regtest, leaf: ScriptBuf, name: &str) -> Funded {
    let tree = TapTree::new(vec![Leaf::new(name, leaf, Timelock::NONE)]).unwrap();
    let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(200_000)).unwrap();
    Funded { tree, op, prev }
}

fn sign_chunk(secret: &SecretKey, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    let kp = Keypair::from_secret_key(SECP256K1, secret);
    sign_tapscript(&kp, tx, 0, std::slice::from_ref(prev), leaf)
        .unwrap()
        .as_ref()
        .to_vec()
}

#[test]
fn refute_and_disprove_on_regtest() {
    let rt = Regtest::start().unwrap();
    let (block, table) = sealed_move(9); // the venue attests an ILLEGAL move
    let head = block.header.head();

    let key = refute_key([9u8; 32]);
    let commit_sig = key.sign(&head).unwrap();
    assert_eq!(key.public().verify(&commit_sig).unwrap(), head.to_vec());

    // the trees: the refutation spends into the disprove output (the park)
    let dis_leaf = disprove_leaf_move_range(&key.public());
    let dis_tree = TapTree::new(vec![Leaf::new("d", dis_leaf.clone(), Timelock::NONE)]).unwrap();
    let ref_leaf = refute_leaf(&table, &key.public());
    let funded = fund(&rt, ref_leaf.clone(), "r");

    // ---- the refutation spend ----
    let mut rtx = build_spend(
        funded.op,
        &Timelock::NONE,
        vec![TxOut {
            value: Amount::from_sat(150_000),
            script_pubkey: dis_tree.script_pubkey(),
        }],
    );
    let head_sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
        .map(|j| sign_chunk(&block.attestation.secrets[HEAD_CHUNK_START + j], &rtx, &funded.prev, &ref_leaf))
        .collect();
    let args = refute_witness(&head, &head_sigs, &commit_sig);
    let arg_bytes: usize = args.iter().map(|a| a.len()).sum();
    rtx.input[0].witness = tapscript_witness(&args, &ref_leaf, &funded.tree.control_block("r").unwrap());
    let h = rt
        .mine_with(&[rtx.clone()])
        .unwrap_or_else(|e| panic!("the honest refutation must mine: {e}"));
    println!(
        "REGTEST refutation: leaf {} B, witness args {arg_bytes} B, spend {} vB (mined at {h})",
        ref_leaf.len(),
        rtx.vsize()
    );
    // the sigops budget of BIP342: 50 + witness bytes, -50 per CHECKSIG
    let witness_bytes = rtx.input[0].witness.size() as u64;
    let budget = 50 + witness_bytes;
    let spent = 50 * HEAD_CHUNKS as u64;
    assert!(budget >= spent, "sigops budget must cover the chunk CHECKSIGs");
    println!("REGTEST refutation sigops: budget {budget}, spent {spent}");

    // ---- negative: a legal move cannot be disproved (checked first,
    // while the refutation output is still unspent) ----
    let ref_op = OutPoint {
        txid: rtx.compute_txid(),
        vout: 0,
    };
    let legal_sig = key.sign(&head_with_legal()).unwrap();
    let mut dtx2 = build_spend(
        ref_op,
        &Timelock::NONE,
        vec![TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: sink(),
        }],
    );
    dtx2.input[0].witness = tapscript_witness(
        &disprove_witness(&legal_sig),
        &dis_leaf,
        &dis_tree.control_block("d").unwrap(),
    );
    assert!(
        rt.test_accept(&dtx2).is_err(),
        "a legal move's tuple must fail the disprove predicate"
    );

    // ---- the disprove spend, off the parked tuple ----
    let mut dtx = build_spend(
        ref_op,
        &Timelock::NONE,
        vec![TxOut {
            value: Amount::from_sat(100_000),
            script_pubkey: sink(),
        }],
    );
    dtx.input[0].witness = tapscript_witness(
        &disprove_witness(&commit_sig),
        &dis_leaf,
        &dis_tree.control_block("d").unwrap(),
    );
    rt.mine_with(&[dtx.clone()])
        .unwrap_or_else(|e| panic!("the disprove of an illegal move must mine: {e}"));
    println!(
        "REGTEST disprove (parked tuple): leaf {} B, spend {} vB",
        dis_leaf.len(),
        dtx.vsize()
    );

    // ---- negative: a re-commitment to a different tuple fails the tie ----
    let (block2, table2) = sealed_move(5); // a LEGAL move attested
    let head2 = block2.header.head();
    let bad_sig = key.sign(&head_with_legal_mismatch()).unwrap(); // signs neither
    let ref_leaf2 = refute_leaf(&table2, &key.public());
    let funded2 = fund(&rt, ref_leaf2.clone(), "r");
    let rtx2 = build_spend(
        funded2.op,
        &Timelock::NONE,
        vec![TxOut {
            value: Amount::from_sat(150_000),
            script_pubkey: sink(),
        }],
    );
    let head_sigs2: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
        .map(|j| sign_chunk(&block2.attestation.secrets[HEAD_CHUNK_START + j], &rtx2, &funded2.prev, &ref_leaf2))
        .collect();
    let args2 = refute_witness(&head2, &head_sigs2, &bad_sig);
    let mut rtx2 = rtx2;
    rtx2.input[0].witness = tapscript_witness(&args2, &ref_leaf2, &funded2.tree.control_block("r").unwrap());
    assert!(
        rt.test_accept(&rtx2).is_err(),
        "the re-commitment must equal the attested head, on chain"
    );
}

/// The mv-5 head (legal) used by the negative paths.
fn head_with_legal() -> [u8; 48] {
    head_with_mv(5)
}
fn head_with_legal_mismatch() -> [u8; 48] {
    head_with_mv(6)
}
fn head_with_mv(mv: u8) -> [u8; 48] {
    let mut h = [0u8; 48];
    h[4] = mv;
    h
}
