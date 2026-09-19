//! Stack-choreography checks of the refutation and disprove leaves through
//! the script32 simulator (its CHECKSIG stub pops both elements and
//! continues; the WOTS gadget's HASH160 work runs for real). Regtest remains
//! the source of truth for the crypto; this catches stack bugs.

use lngap_ec_wots::Attester;
use lngap_pos::refute::{
    disprove_leaf_move_range, disprove_witness, refute_key, refute_leaf, refute_witness,
    HEAD_CHUNKS,
};
use lngap_pos::HEADER_CHUNKS;

const DUMMY_SIG: [u8; 64] = [0x30; 64];

/// A head whose move byte (byte 4) is `mv`; the rest zero.
fn head_with(mv: u8) -> [u8; 48] {
    let mut h = [0u8; 48];
    h[4] = mv;
    h
}

/// The 96-byte header carrying `head` at slot 1.
fn header_with(head: &[u8; 48]) -> Vec<u8> {
    let mut h = vec![0u8; 96];
    h[40..88].copy_from_slice(head);
    h[88..92].copy_from_slice(&1u32.to_le_bytes());
    h
}

fn setup(mv: u8) -> (lngap_ec_wots::EpochTable, [u8; 48], Vec<Vec<u8>>) {
    let att = Attester::new([7u8; 32]);
    let table = att.epoch_table(1, HEADER_CHUNKS);
    let head = head_with(mv);
    let header = header_with(&head);
    let attestation = att.attest(&table, &header);
    assert!(attestation.verify(&table, &header));
    // the sim stubs CHECKSIG: dummy 64-byte sigs stand in per head chunk
    let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    (table, head, sigs)
}

#[test]
fn refute_runs() {
    let (table, head, sigs) = setup(5);
    let key = refute_key([9u8; 32]);
    let sig = key.sign(&head).unwrap();
    assert_eq!(key.public().verify(&sig).unwrap(), head.to_vec());
    let leaf = refute_leaf(&table, &key.public());
    let end = lngap_script32::sim::run(leaf.as_script(), refute_witness(&head, &sigs, &sig))
        .expect("a correct refutation must run");
    assert_eq!(end, vec![vec![1]], "the leaf ends with OP_1");
}

#[test]
fn refute_rejects_a_mismatched_recommitment() {
    let (table, head, sigs) = setup(5);
    let key = refute_key([9u8; 32]);
    // the re-commitment signs a DIFFERENT head than the one attested
    let other = head_with(6);
    let sig = key.sign(&other).unwrap();
    let leaf = refute_leaf(&table, &key.public());
    assert!(
        lngap_script32::sim::run(leaf.as_script(), refute_witness(&head, &sigs, &sig)).is_err(),
        "the re-committed tuple must equal the attested head, nibble by nibble"
    );
}

#[test]
fn refute_rejects_an_out_of_range_value() {
    let (table, head, sigs) = setup(5);
    let key = refute_key([9u8; 32]);
    let sig = key.sign(&head).unwrap();
    let leaf = refute_leaf(&table, &key.public());
    let mut w = refute_witness(&head, &sigs, &sig);
    // corrupt the first-consumed value (the last chunk item in wire order
    // before the wots items): 16 is out of range and must fail at OP_PICK
    let n = w.len();
    let wots_items = 2 * sig.params.total_digits() as usize;
    let v_pos = n - wots_items - 1;
    w[v_pos] = vec![16];
    assert!(lngap_script32::sim::run(leaf.as_script(), w).is_err());
}

#[test]
fn disprove_fires_on_an_out_of_range_move() {
    let key = refute_key([9u8; 32]);
    let sig = key.sign(&head_with(9)).unwrap();
    let leaf = disprove_leaf_move_range(&key.public());
    let end = lngap_script32::sim::run(leaf.as_script(), disprove_witness(&sig))
        .expect("mv = 9 is illegal: the disprove must run");
    assert_eq!(end, vec![vec![1]]);
}

#[test]
fn disprove_cannot_fire_on_a_legal_move() {
    let key = refute_key([9u8; 32]);
    let sig = key.sign(&head_with(5)).unwrap();
    let leaf = disprove_leaf_move_range(&key.public());
    assert!(
        lngap_script32::sim::run(leaf.as_script(), disprove_witness(&sig)).is_err(),
        "mv = 5 is legal: the predicate must fail at VERIFY"
    );
}
