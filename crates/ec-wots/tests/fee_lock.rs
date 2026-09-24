//! The atomic fee lock on regtest (ATTESTATION_FEES.md; D49): a payment
//! from Alice to Bob whose signature is a BIP340 adaptor pre-signature
//! locked to the SUM of the anticipation points selected by Bob's head
//! under the venue's table (`EpochTable::point_sum`). Its adaptor secret
//! is the sum of the scalars the venue reveals when — and only when — it
//! attests exactly that head (`Attestation::scalar_sum`): "pay iff you
//! attest this head" with nothing on-chain but an ordinary signature.
//!
//! - before the attestation Bob holds a pre-signature that is not a
//!   signature (the node rejects it);
//! - the venue attests Bob's head; Bob sums the revealed scalars,
//!   completes, and the spend mines;
//! - Alice recovers the adaptor secret from the on-chain signature and
//!   checks it against the point sum she locked to;
//! - the venue attesting a DIFFERENT head (one nibble off) yields a
//!   scalar sum that does not complete the pre-signature.
//!
//! The payee here is a plain key; in the design the payee is the slot's
//! proposer and the lock rides a channel HTLC-shaped output. The
//! mechanism is the same.

use bitcoin::key::Keypair;
use bitcoin::script::Builder;
use bitcoin::secp256k1::{PublicKey, SecretKey, SECP256K1};
use bitcoin::{Amount, ScriptBuf, TxOut};
use lngap_btc::adaptor::{adaptor_complete, adaptor_extract, adaptor_sign, adaptor_verify};
use lngap_btc::regtest::Regtest;
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::{tapscript_sighash, verify_tapscript};
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_ec_wots::Attester;

/// The 48-byte head of Bob's move at slot 1 (any bytes; the venue attests
/// bytes, not meaning).
const HEAD: [u8; 48] = [
    0x00, 0x01, 0x02, 0x01, 0x34, 0x00, 0x00, 0x00, 0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF, 0x11, 0x22,
    0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90,
    0xA0, 0xB0, 0xC0, 0xD0,
];
const CHUNKS: usize = HEAD.len() * 2;

#[test]
fn fee_lock_resolves_on_exactly_this_attestation() {
    let rt = Regtest::start().unwrap();
    let venue = Attester::new([0x77; 32]);
    let table = venue.epoch_table(1, CHUNKS);

    // Alice (the payer), Bob (the payee)
    let alice = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[0xA1; 32]).unwrap());
    let (alice_x, _) = alice.x_only_public_key();
    let bob = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[0xB0; 32]).unwrap());
    let bob_spk = ScriptBuf::new_p2tr(SECP256K1, bob.x_only_public_key().0, None);

    // the locked output: Alice's key alone; the spend to Bob is what she
    // pre-signs under the adaptor
    let leaf = Builder::new().checksig(&alice_x).into_script();
    let tree = TapTree::new(vec![Leaf::new("pay", leaf.clone(), Timelock::NONE)]).unwrap();
    let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(50_000)).unwrap();
    let tx = build_spend(
        op,
        &Timelock::NONE,
        vec![TxOut {
            value: Amount::from_sat(49_000),
            script_pubkey: bob_spk,
        }],
    );
    let msg = tapscript_sighash(&tx, 0, std::slice::from_ref(&prev), &leaf).unwrap();

    // the lock: the sum of the table points Bob's head selects
    let t_point: PublicKey = table.point_sum(&HEAD, 0..CHUNKS);
    let pre = adaptor_sign(&alice, &msg, &t_point);
    assert!(adaptor_verify(&alice_x, &msg, &t_point, &pre), "Bob checks the pre-signature against the lock before doing anything");

    // before the attestation: the pre-signature is not a signature
    let mut fake = [0u8; 64];
    fake[..32].copy_from_slice(&pre.r_final.serialize());
    fake[32..].copy_from_slice(&pre.s_prime.secret_bytes());
    let fake = bitcoin::secp256k1::schnorr::Signature::from_slice(&fake).unwrap();
    assert!(verify_tapscript(&alice_x, &fake, &tx, 0, std::slice::from_ref(&prev), &leaf).is_err());
    let mut early = tx.clone();
    early.input[0].witness = tapscript_witness(&[fake.as_ref().to_vec()], &leaf, &tree.control_block("pay").unwrap());
    assert!(rt.test_accept(&early).is_err(), "nothing to claim before the attestation");

    // the venue attests a DIFFERENT head: the scalars do not open the lock
    let mut other = HEAD;
    other[47] ^= 0x01;
    let att_other = venue.attest(&table, &other);
    let t_other = att_other.scalar_sum(0..CHUNKS);
    let wrong = adaptor_complete(&pre, &t_other);
    assert!(verify_tapscript(&alice_x, &wrong, &tx, 0, std::slice::from_ref(&prev), &leaf).is_err(), "another head's attestation does not pay");

    // the venue attests Bob's head: the revealed scalars sum to the lock's log
    let att = venue.attest(&table, &HEAD);
    assert!(att.verify(&table, &HEAD));
    let t = att.scalar_sum(0..CHUNKS);
    assert_eq!(PublicKey::from_secret_key(SECP256K1, &t), t_point);
    let sig = adaptor_complete(&pre, &t);
    verify_tapscript(&alice_x, &sig, &tx, 0, std::slice::from_ref(&prev), &leaf).expect("the completed signature is a valid BIP340 signature under Alice's key");
    let mut paid = tx.clone();
    paid.input[0].witness = tapscript_witness(&[sig.as_ref().to_vec()], &leaf, &tree.control_block("pay").unwrap());
    rt.mine_with(&[paid.clone()]).unwrap_or_else(|e| panic!("the fee claim must mine: {e}"));
    println!("REGTEST fee lock: {} chunk points summed into one adaptor point; the claim is an ordinary key spend, {} vB", CHUNKS, paid.vsize());

    // Alice reads the secret off the chain
    let onchain = rt.get_tx(&paid.compute_txid()).unwrap();
    let onchain_sig = bitcoin::secp256k1::schnorr::Signature::from_slice(&onchain.input[0].witness[0]).unwrap();
    let extracted = adaptor_extract(&pre, &onchain_sig).unwrap();
    assert_eq!(extracted, t, "the payer learns the attestation's scalar sum from the payment itself");
    assert_eq!(PublicKey::from_secret_key(SECP256K1, &extracted), t_point);
}
