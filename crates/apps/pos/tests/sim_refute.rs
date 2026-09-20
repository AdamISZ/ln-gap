//! Stack-choreography checks of the refutation and disprove leaves through
//! the script32 simulator (its CHECKSIG stub pops both elements and
//! continues; the WOTS gadget's HASH160 work runs for real). Regtest remains
//! the source of truth for the crypto; this catches stack bugs.

use lngap_ec_wots::Attester;
use lngap_pos::refute::{pair_key, refute_key, refute_leaf, refute_leaf_pair, refute_witness, refute_witness_pair, HEAD_CHUNKS};
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

// ----- the two-head refutation (D35) -----

/// Two slots' tables and their attested heads (mv 4 at slot 1, mv 0 at 2).
fn pair_setup() -> (
    lngap_ec_wots::EpochTable,
    lngap_ec_wots::EpochTable,
    [u8; 48],
    [u8; 48],
) {
    let att = Attester::new([7u8; 32]);
    let t1 = att.epoch_table(1, HEADER_CHUNKS);
    let t2 = att.epoch_table(2, HEADER_CHUNKS);
    let h1 = head_with(4);
    let h2 = head_with(0);
    let hdr1 = header_with(&h1);
    let mut hdr2 = header_with(&h2);
    hdr2[88..92].copy_from_slice(&2u32.to_le_bytes());
    assert!(att.attest(&t1, &hdr1).verify(&t1, &hdr1));
    assert!(att.attest(&t2, &hdr2).verify(&t2, &hdr2));
    (t1, t2, h1, h2)
}

fn pair_msg(h1: &[u8; 48], h2: &[u8; 48]) -> Vec<u8> {
    let mut m = h1.to_vec();
    m.extend_from_slice(h2);
    m
}

#[test]
fn refute_pair_runs() {
    let (t1, t2, h1, h2) = pair_setup();
    let key = pair_key([9u8; 32]);
    let sig = key.sign(&pair_msg(&h1, &h2)).unwrap();
    let leaf = refute_leaf_pair(&t1, &t2, &key.public());
    let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    let end = lngap_script32::sim::run(leaf.as_script(), refute_witness_pair(&h1, &sigs, &h2, &sigs, &sig))
        .expect("a correct two-head refutation must run");
    assert_eq!(end, vec![vec![1]], "the leaf ends with OP_1");
}

#[test]
fn refute_pair_rejects_a_mismatched_recommitment() {
    // the pair reveal signs a DIFFERENT prior head than the one read out
    let (t1, t2, h1, h2) = pair_setup();
    let key = pair_key([9u8; 32]);
    let sig = key.sign(&pair_msg(&head_with(5), &h2)).unwrap();
    let leaf = refute_leaf_pair(&t1, &t2, &key.public());
    let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    assert!(lngap_script32::sim::run(leaf.as_script(), refute_witness_pair(&h1, &sigs, &h2, &sigs, &sig)).is_err());
}
