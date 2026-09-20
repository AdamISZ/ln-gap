//! Stack-choreography checks of the refutation and disprove leaves through
//! the script32 simulator (its CHECKSIG stub pops both elements and
//! continues; the WOTS gadget's HASH160 work runs for real). Regtest remains
//! the source of truth for the crypto; this catches stack bugs.

use lngap_ec_wots::Attester;
use lngap_pos::refute::{pair_key, refute_key, refute_leaf, refute_leaf_pair_gated, refute_witness, refute_witness_pair, HEAD_CHUNKS};
use lngap_pos::HEADER_CHUNKS;

const DUMMY_SIG: [u8; 64] = [0x30; 64];

/// The fixture heads carry state 0 (all bits false); the D41 authorship
/// fragments check the presented preimages against these per-head state
/// keys.
fn state_key(seed: u8) -> lngap_lamport::SecretKey {
    lngap_lamport::SecretKey::from_entropy(lngap_factchain::slot::STATE_BITS, [seed; 32])
}

fn zero_state_reveal(seed: u8) -> lngap_lamport::Reveal {
    state_key(seed)
        .reveal_bits(&[false; lngap_factchain::slot::STATE_BITS])
        .unwrap()
}

/// The authorship gate for a depth-1 (single-head) leaf.
fn auth1(seed: u8) -> impl FnOnce(bitcoin::script::Builder) -> bitcoin::script::Builder {
    move |b| lngap_pos::ttt::authorship_fragment(b, 96, 0, &state_key(seed).public())
}

/// The authorship gate for a pair leaf: the new head's fragment (offset 96)
/// then the prior's (offset 0).
fn auth2(seed_new: u8, seed_prev: u8) -> impl FnOnce(bitcoin::script::Builder) -> bitcoin::script::Builder {
    move |b| {
        let b = lngap_pos::ttt::authorship_fragment(b, 192, 96, &state_key(seed_new).public());
        lngap_pos::ttt::authorship_fragment(b, 192, 0, &state_key(seed_prev).public())
    }
}

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
    let leaf = refute_leaf(&table, &key.public(), auth1(1));
    let end = lngap_script32::sim::run(leaf.as_script(), refute_witness(&head, &sigs, &sig, &zero_state_reveal(1)))
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
    let leaf = refute_leaf(&table, &key.public(), auth1(1));
    // the fragment reads the FILE's claimed state (the re-committed head's:
    // zero); the tie then fails the readout
    assert!(
        lngap_script32::sim::run(leaf.as_script(), refute_witness(&head, &sigs, &sig, &zero_state_reveal(1))).is_err(),
        "the re-committed tuple must equal the attested head, nibble by nibble"
    );
}

#[test]
fn refute_rejects_junk_preimages() {
    // D41: the authorship fragment — the presented preimages must open the
    // mover's state key bit by bit against the claimed state
    let (table, head, sigs) = setup(5);
    let key = refute_key([9u8; 32]);
    let sig = key.sign(&head).unwrap();
    let leaf = refute_leaf(&table, &key.public(), auth1(1));
    let junk = lngap_lamport::Reveal { preimages: vec![[0x11; 20]; 21] };
    assert!(lngap_script32::sim::run(leaf.as_script(), refute_witness(&head, &sigs, &sig, &junk)).is_err());
    // and one wrong bit's preimage among twenty good ones
    let mut r = zero_state_reveal(1);
    r.preimages[7] = [0x12; 20];
    assert!(lngap_script32::sim::run(leaf.as_script(), refute_witness(&head, &sigs, &sig, &r)).is_err());
}

#[test]
fn refute_rejects_an_out_of_range_value() {
    let (table, head, sigs) = setup(5);
    let key = refute_key([9u8; 32]);
    let sig = key.sign(&head).unwrap();
    let leaf = refute_leaf(&table, &key.public(), auth1(1));
    let mut w = refute_witness(&head, &sigs, &sig, &zero_state_reveal(1));
    // corrupt chunk 0's value (the last of the 192 chunk items — the
    // authorship block and the wots items follow): 16 is out of range and
    // must fail at OP_PICK
    let v_pos = 2 * HEAD_CHUNKS - 1;
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
    let leaf = refute_leaf_pair_gated(&t1, &t2, &key.public(), auth2(2, 1));
    let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    let end = lngap_script32::sim::run(
        leaf.as_script(),
        refute_witness_pair(&h1, &sigs, &h2, &sigs, &sig, &zero_state_reveal(1), &zero_state_reveal(2)),
    )
        .expect("a correct two-head refutation must run");
    assert_eq!(end, vec![vec![1]], "the leaf ends with OP_1");
}

#[test]
fn refute_pair_rejects_a_mismatched_recommitment() {
    // the pair reveal signs a DIFFERENT prior head than the one read out
    let (t1, t2, h1, h2) = pair_setup();
    let key = pair_key([9u8; 32]);
    let sig = key.sign(&pair_msg(&head_with(5), &h2)).unwrap();
    let leaf = refute_leaf_pair_gated(&t1, &t2, &key.public(), auth2(2, 1));
    let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    // the FILE's prior head claims state 0 (the mismatched re-commitment);
    // the prior fragment's preimages match it, then the tie fails
    assert!(
        lngap_script32::sim::run(
            leaf.as_script(),
            refute_witness_pair(&h1, &sigs, &h2, &sigs, &sig, &zero_state_reveal(1), &zero_state_reveal(2)),
        )
        .is_err()
    );
}
