//! The timeliness flag (NON_INCLUSION_THRESHOLD.md; D50): a validator's
//! per-slot ONE-BIT statement, "slot `s` held no valid entry when its
//! deadline passed".
//!
//! A statement with no content needs no anticipation table: each validator
//! holds ONE committed point per slot, `F_{i,s} = f_{i,s}·G`, published in
//! the registry next to the slot's head table. When a slot passes its
//! deadline empty the validator publishes `f_{i,s}` as data (anywhere — the
//! delivery is out of band); it publishes nothing otherwise. A revealed
//! scalar is a private key for its point, so the contract side counts
//! flags as INDIVIDUAL signatures (`<F_1> CHECKSIG <F_2> CHECKSIGADD ...`,
//! the `not_timely` leaf of `lngap_pos::graph`): whoever holds `t` of the
//! `k` scalars signs its own transaction under `t` points, and every real
//! signature in that witness names the validator whose scalar produced
//! it. Threshold and attribution at once, at one signature per signer —
//! the aggregate route cannot name its signers (VENUE_QUORUM.md section 7).
//!
//! Seeded and deterministic like the attester's nonces, so the registry
//! is reproducible; even-y normalised like the chunk secrets, so the point
//! of a revealed scalar is exactly the registered x-only point lifted.

use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::key::{Keypair, Parity, XOnlyPublicKey};
use bitcoin::secp256k1::{SecretKey, SECP256K1};

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

/// One validator's flag key: the seed its per-slot flag secrets derive
/// from. In deployment each notary member holds one.
pub struct FlagKeys {
    seed: [u8; 32],
}

impl FlagKeys {
    pub fn new(seed: [u8; 32]) -> FlagKeys {
        FlagKeys { seed }
    }

    /// The flag secret of `slot`: revealing it IS the statement "slot
    /// `slot` passed its deadline empty". Even-y normalised (negated if
    /// `f·G` has odd y) so that `f·G` lifts exactly to [`flag_point`].
    ///
    /// [`flag_point`]: FlagKeys::flag_point
    pub fn flag_secret(&self, slot: u64) -> SecretKey {
        for tries in 0u8.. {
            let slot_b = slot.to_be_bytes();
            let tries_b = [tries];
            let parts: Vec<&[u8]> = vec![&self.seed, &slot_b, &tries_b];
            if let Ok(f) = SecretKey::from_slice(&tagged("ecwots/flag", &parts)) {
                return match Keypair::from_secret_key(SECP256K1, &f).x_only_public_key().1 {
                    Parity::Even => f,
                    Parity::Odd => f.negate(),
                };
            }
        }
        unreachable!()
    }

    /// The registered point of `slot` (public data, a script constant in
    /// the `not_timely` leaf of every contract that reads this slot).
    pub fn flag_point(&self, slot: u64) -> XOnlyPublicKey {
        Keypair::from_secret_key(SECP256K1, &self.flag_secret(slot)).x_only_public_key().0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::secp256k1::{Message, PublicKey};

    /// The revealed secret opens the registered point, and a signature
    /// made with it verifies under that point (the possession proof the
    /// leaf counts).
    #[test]
    fn flag_secret_opens_point_and_signs() {
        let v = FlagKeys::new([0x51; 32]);
        for slot in [0u64, 1, 7, 1 << 40] {
            let f = v.flag_secret(slot);
            let pt = v.flag_point(slot);
            let full = PublicKey::from_secret_key(SECP256K1, &f);
            assert_eq!(full.x_only_public_key().0, pt);
            assert_eq!(full.x_only_public_key().1, Parity::Even, "even-y normalised");
            let msg = Message::from_digest([slot as u8; 32]);
            let sig = SECP256K1.sign_schnorr(&msg, &Keypair::from_secret_key(SECP256K1, &f));
            SECP256K1.verify_schnorr(&sig, &msg, &pt).expect("verifies under the registered point");
            // another slot's point does not verify it
            assert!(SECP256K1.verify_schnorr(&sig, &msg, &v.flag_point(slot + 1)).is_err());
        }
        // two validators' points at one slot are unrelated
        assert_ne!(v.flag_point(3), FlagKeys::new([0x52; 32]).flag_point(3));
    }
}
