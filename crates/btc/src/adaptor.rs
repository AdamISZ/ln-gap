//! BIP340 adaptor signatures (pre-signatures).
//!
//! A signer with key `P` and message `m` produces, for an adaptor point
//! `T = t·G` it does not know the log of, a PRE-signature `(R + T, s')` such
//! that `s' + t` is a valid BIP340 signature under `P` on `m` with nonce
//! point `R + T`. The counterparty verifies the pre-signature against `T`
//! (so it knows the completed signature will be valid and will reveal
//! `t`), the holder of `t` completes it, and once the completed signature
//! is public the signer extracts `t = s − s'`.
//!
//! This is the atomic fee lock of ATTESTATION_FEES.md: `T` is a sum of
//! EC-OTS anticipation points (`EpochTable::point_sum`), `t` the sum of
//! the scalars an attestation of exactly that message reveals
//! (`Attestation::scalar_sum`), so "the payee can claim" and "the venue
//! attested this head" are the same event. Nothing about the construction
//! is specific to that use.
//!
//! BIP340 details: the challenge is over the x-only FINAL nonce `R + T`,
//! which must have even y, so the signer retries its nonce until it does
//! (it knows `T` before choosing `k`); the signer's secret is negated when
//! `P` has odd y, as in ordinary BIP340 signing; the completion adds `t`
//! to `s'` and nothing else.

use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::key::{Keypair, Parity, XOnlyPublicKey};
use bitcoin::secp256k1::{schnorr, Message, PublicKey, Scalar, SecretKey, SECP256K1};

/// A pre-signature: the final nonce point's x coordinate (what the
/// completed signature carries), the signer's own nonce point (so a
/// verifier can check `R + T` reaches it), and the pre-scalar `s'`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdaptorSig {
    pub r_final: XOnlyPublicKey,
    pub r: PublicKey,
    pub s_prime: SecretKey,
}

fn tagged(tag: &str, parts: &[&[u8]]) -> [u8; 32] {
    let th = sha256::Hash::hash(tag.as_bytes());
    let mut eng = sha256::Hash::engine();
    eng.input(th.as_ref());
    eng.input(th.as_ref());
    for p in parts {
        eng.input(p);
    }
    sha256::Hash::from_engine(eng).to_byte_array()
}

/// The BIP340 challenge `e = H_tag(R.x || P.x || m)`. (Out-of-range
/// hashes are reduced by BIP340; the probability is ~2^-128 and the
/// reduction path is not worth its own code here.)
fn challenge(r_x: &XOnlyPublicKey, pk: &XOnlyPublicKey, msg: &Message) -> Scalar {
    Scalar::from_be_bytes(tagged("BIP0340/challenge", &[&r_x.serialize(), &pk.serialize(), msg.as_ref()]))
        .expect("a BIP340 challenge is in range (2^-128 otherwise)")
}

fn to_scalar(k: &SecretKey) -> Scalar {
    Scalar::from_be_bytes(k.secret_bytes()).expect("a secret key is in range")
}

/// Produce a pre-signature on `msg` under `kp`, locked to `t_point`.
pub fn adaptor_sign(kp: &Keypair, msg: &Message, t_point: &PublicKey) -> AdaptorSig {
    let (pk_x, parity) = kp.x_only_public_key();
    let d = match parity {
        Parity::Even => kp.secret_key(),
        Parity::Odd => kp.secret_key().negate(),
    };
    for ctr in 0u32.. {
        // a deterministic nonce over the secret, the message, the adaptor
        // point and a retry counter (the final nonce's parity is the retry
        // condition)
        let k = SecretKey::from_slice(&tagged(
            "lngap/adaptor/nonce",
            &[&d.secret_bytes(), msg.as_ref(), &t_point.serialize(), &ctr.to_be_bytes()],
        ))
        .expect("tagged hash is a valid key");
        let r = PublicKey::from_secret_key(SECP256K1, &k);
        let Ok(r_final) = r.combine(t_point) else { continue };
        let (rf_x, rf_par) = r_final.x_only_public_key();
        if rf_par == Parity::Odd {
            continue;
        }
        let e = challenge(&rf_x, &pk_x, msg);
        let ed = d.mul_tweak(&e).expect("nonzero product");
        let s_prime = k.add_tweak(&to_scalar(&ed)).expect("nonzero sum");
        return AdaptorSig { r_final: rf_x, r, s_prime };
    }
    unreachable!()
}

/// Verify a pre-signature: `R + T` is the (even-y) final nonce point and
/// `s'·G = R + e·P`. A holder of `t` with `t·G = T` can then complete it.
pub fn adaptor_verify(pk: &XOnlyPublicKey, msg: &Message, t_point: &PublicKey, sig: &AdaptorSig) -> bool {
    let Ok(r_final) = sig.r.combine(t_point) else { return false };
    let (rf_x, rf_par) = r_final.x_only_public_key();
    if rf_par != Parity::Even || rf_x != sig.r_final {
        return false;
    }
    let e = challenge(&sig.r_final, pk, msg);
    let p_full = PublicKey::from_x_only_public_key(*pk, Parity::Even);
    let Ok(ep) = p_full.mul_tweak(SECP256K1, &e) else { return false };
    let Ok(rhs) = sig.r.combine(&ep) else { return false };
    PublicKey::from_secret_key(SECP256K1, &sig.s_prime) == rhs
}

/// Complete a pre-signature with the adaptor secret: `s = s' + t`.
pub fn adaptor_complete(sig: &AdaptorSig, t: &SecretKey) -> schnorr::Signature {
    let s = sig.s_prime.add_tweak(&to_scalar(t)).expect("nonzero sum");
    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(&sig.r_final.serialize());
    bytes[32..].copy_from_slice(&s.secret_bytes());
    schnorr::Signature::from_slice(&bytes).expect("64 bytes")
}

/// Recover the adaptor secret from a completed signature: `t = s − s'`.
pub fn adaptor_extract(sig: &AdaptorSig, completed: &schnorr::Signature) -> Option<SecretKey> {
    let s = SecretKey::from_slice(&completed.as_ref()[32..]).ok()?;
    let neg = to_scalar(&sig.s_prime.negate());
    s.add_tweak(&neg).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adaptor_roundtrip_and_negatives() {
        let kp = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[7u8; 32]).unwrap());
        let (pk, _) = kp.x_only_public_key();
        let msg = Message::from_digest([0xAB; 32]);
        let t = SecretKey::from_slice(&[5u8; 32]).unwrap();
        let t_point = PublicKey::from_secret_key(SECP256K1, &t);
        let pre = adaptor_sign(&kp, &msg, &t_point);
        assert!(adaptor_verify(&pk, &msg, &t_point, &pre));
        // not a signature yet: the pre-scalar under the final nonce fails
        let mut fake = [0u8; 64];
        fake[..32].copy_from_slice(&pre.r_final.serialize());
        fake[32..].copy_from_slice(&pre.s_prime.secret_bytes());
        assert!(SECP256K1.verify_schnorr(&schnorr::Signature::from_slice(&fake).unwrap(), &msg, &pk).is_err());
        // the completion is a valid BIP340 signature, and reveals t
        let sig = adaptor_complete(&pre, &t);
        assert!(SECP256K1.verify_schnorr(&sig, &msg, &pk).is_ok());
        assert_eq!(adaptor_extract(&pre, &sig).unwrap(), t);
        // the wrong secret does not complete it
        let wrong = SecretKey::from_slice(&[6u8; 32]).unwrap();
        assert!(SECP256K1.verify_schnorr(&adaptor_complete(&pre, &wrong), &msg, &pk).is_err());
        // a pre-signature does not verify against another adaptor point
        let other = PublicKey::from_secret_key(SECP256K1, &wrong);
        assert!(!adaptor_verify(&pk, &msg, &other, &pre));
        // odd-y signer keys are handled like ordinary BIP340 signing
        for seed in 1..=6u8 {
            let kp = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[seed; 32]).unwrap());
            let (pk, _) = kp.x_only_public_key();
            let pre = adaptor_sign(&kp, &msg, &t_point);
            assert!(adaptor_verify(&pk, &msg, &t_point, &pre));
            assert!(SECP256K1.verify_schnorr(&adaptor_complete(&pre, &t), &msg, &pk).is_ok());
        }
    }
}
