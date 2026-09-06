//! Keys: deterministic per-role derivation from a seed, and the NUMS point.

use bitcoin::hashes::{sha256, Hash};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::secp256k1::{SecretKey, SECP256K1};

/// The BIP-341 "nothing up my sleeve" point: SHA256 of the generator's
/// x-coordinate, lifted to a point. Using it as the Taproot internal key makes
/// the key path unspendable, so every spend is a script path.
pub fn nums_point() -> XOnlyPublicKey {
    const H: [u8; 32] = [
        0x50, 0x92, 0x9b, 0x74, 0xc1, 0xa0, 0x49, 0x54, 0xb7, 0x8b, 0x4b, 0x60, 0x35, 0xe9, 0x7a,
        0x5e, 0x07, 0x8a, 0x5a, 0x0f, 0x28, 0xec, 0x96, 0xd5, 0x47, 0xbf, 0xee, 0x9a, 0xce, 0x80,
        0x3a, 0xc0,
    ];
    XOnlyPublicKey::from_slice(&H).expect("BIP-341 NUMS point is valid")
}

/// A party's root secret. Every key and every one-time secret a party uses is
/// derived from its seed with a label, so two parties built from different
/// seeds cannot share material.
#[derive(Clone)]
pub struct Seed([u8; 32]);

impl std::fmt::Debug for Seed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Seed(..)")
    }
}

impl Seed {
    pub fn new(bytes: [u8; 32]) -> Seed {
        Seed(bytes)
    }

    /// Deterministic seed from a label; for tests and the regtest harness only.
    pub fn from_label(label: &str) -> Seed {
        Seed(sha256::Hash::hash(format!("lngap-seed/{label}").as_bytes()).to_byte_array())
    }

    pub fn random() -> Seed {
        use rand::RngCore;
        let mut b = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut b);
        Seed(b)
    }

    /// 32 pseudo-random bytes bound to `label`.
    pub fn derive_bytes(&self, label: &str) -> [u8; 32] {
        let mut eng = sha256::Hash::engine();
        use bitcoin::hashes::HashEngine;
        eng.input(&self.0);
        eng.input(b"/");
        eng.input(label.as_bytes());
        sha256::Hash::from_engine(eng).to_byte_array()
    }

    /// A child seed, for namespacing (e.g. one per channel, then per state).
    pub fn child(&self, label: &str) -> Seed {
        Seed(self.derive_bytes(&format!("child/{label}")))
    }

    /// A Schnorr keypair bound to `label`.
    pub fn keypair(&self, label: &str) -> Keypair {
        let bytes = self.derive_bytes(&format!("key/{label}"));
        let sk = SecretKey::from_slice(&bytes).expect("sha256 output is a valid scalar w.h.p.");
        Keypair::from_secret_key(SECP256K1, &sk)
    }
}

/// x-only public key of a keypair.
pub fn xonly(kp: &Keypair) -> XOnlyPublicKey {
    kp.x_only_public_key().0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derivation_is_deterministic_and_label_separated() {
        let s = Seed::from_label("a");
        assert_eq!(xonly(&s.keypair("x")), xonly(&s.keypair("x")));
        assert_ne!(xonly(&s.keypair("x")), xonly(&s.keypair("y")));
        assert_ne!(xonly(&s.keypair("x")), xonly(&Seed::from_label("b").keypair("x")));
    }
}
