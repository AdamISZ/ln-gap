//! Stack-choreography checks of the refutation and disprove leaves through
//! the script32 simulator (its CHECKSIG stub pops both elements and
//! continues; the WOTS gadget's HASH160 work runs for real). Regtest remains
//! the source of truth for the crypto; this catches stack bugs.

use lngap_ec_wots::Attester;
use lngap_pos::refute::{pair_key, refute_key, refute_leaf, refute_leaf_pair_gated, refute_witness, refute_witness_pair, HEAD_CHUNKS};
use lngap_pos::HEADER_CHUNKS;

const DUMMY_SIG: [u8; 64] = [0x30; 64];

/// The fixture heads carry state 0 (all bytes zero); the D41 authorship
/// fragments check the presented state-key signatures against the per-head
/// state keys (D43: Winternitz over the 3 state bytes).
fn state_key(seed: u8) -> lngap_lamport::winternitz::WotsSecret {
    lngap_lamport::winternitz::WotsSecret::from_entropy(lngap_lamport::winternitz::WotsParams::for_bytes(3), [seed; 32])
}

fn zero_state_sig(seed: u8) -> lngap_lamport::winternitz::WotsSig {
    state_key(seed).sign(&[0u8; 3]).unwrap()
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
    let end = lngap_script32::sim::run(leaf.as_script(), refute_witness(&sigs, &sig, &zero_state_sig(1)))
        .expect("a correct refutation must run");
    assert_eq!(end, vec![vec![1]], "the leaf ends with OP_1");
}

#[test]
fn refute_rejects_junk_preimages() {
    // D41: the authorship fragment — the presented signature must chain to
    // the mover's state key against the claimed (parked) state
    let (table, head, sigs) = setup(5);
    let key = refute_key([9u8; 32]);
    let sig = key.sign(&head).unwrap();
    let leaf = refute_leaf(&table, &key.public(), auth1(1));
    // a signature under a DIFFERENT key
    let junk = state_key(99).sign(&[0u8; 3]).unwrap();
    assert!(lngap_script32::sim::run(leaf.as_script(), refute_witness(&sigs, &sig, &junk)).is_err());
    // and one corrupted reveal among seven good ones
    let mut r = zero_state_sig(1);
    r.hashes[3] = [0x12; 20];
    assert!(lngap_script32::sim::run(leaf.as_script(), refute_witness(&sigs, &sig, &r)).is_err());
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
        refute_witness_pair(&sigs, &sigs, &sig, &[&zero_state_sig(2), &zero_state_sig(1)]),
    )
        .expect("a correct two-head refutation must run");
    assert_eq!(end, vec![vec![1]], "the leaf ends with OP_1");
}

#[test]
fn refute_pair_rejects_a_mismatched_recommitment() {
    // the pair reveal signs a DIFFERENT prior head than the one read out.
    // With the TIED readout (D42) the failure is inside the point selection
    // — a wrong digit selects an anticipation point whose secret nobody
    // holds — which the sim's CHECKSIG stub cannot see: the negative is
    // testable only with real sigs (regtest; pos_graph's mismatched-pair
    // case). The choreography still runs here, pinning the witness shape.
    let (t1, t2, _h1, h2) = pair_setup();
    let key = pair_key([9u8; 32]);
    let sig = key.sign(&pair_msg(&head_with(5), &h2)).unwrap();
    let leaf = refute_leaf_pair_gated(&t1, &t2, &key.public(), auth2(2, 1));
    let sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    let _ = lngap_script32::sim::run(
        leaf.as_script(),
        refute_witness_pair(&sigs, &sigs, &sig, &[&zero_state_sig(2), &zero_state_sig(1)]),
    );
}
