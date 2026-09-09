//! Lamport one-time bit commitments and their Script gadgets.
//!
//! A *bit commitment* is `(h0, h1) = (HASH160(p0), HASH160(p1))`. Revealing `p0`
//! commits the bit to 0, `p1` to 1. Revealing both is equivocation.
//! A *key* for an n-bit value is n bit commitments; bit `i` is `(value >> i) & 1`,
//! so index 0 is the least significant bit.
//!
//! Stack convention (see `lngap_btc::witness`): a gadget consumes the top
//! element first. `decode_uint` consumes the most-significant bit first, so a
//! reveal's witness elements are pushed lsb-first (msb ends on top).

pub mod gadgets;
pub mod keystore;
pub mod winternitz;

use anyhow::{bail, ensure, Result};
use lngap_btc::{hash160, Hash160};
use rand::RngCore;
use serde::{Deserialize, Serialize};

pub const PREIMAGE_LEN: usize = 20;
pub type Preimage = [u8; PREIMAGE_LEN];

/// Public half of one bit commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitCommit {
    pub h0: Hash160,
    pub h1: Hash160,
}

/// Secret half of one bit commitment.
#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct BitSecret {
    pub p0: Preimage,
    pub p1: Preimage,
}

impl std::fmt::Debug for BitSecret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("BitSecret(..)")
    }
}

impl BitSecret {
    pub fn generate<R: RngCore>(rng: &mut R) -> BitSecret {
        let mut p0 = [0u8; PREIMAGE_LEN];
        let mut p1 = [0u8; PREIMAGE_LEN];
        rng.fill_bytes(&mut p0);
        rng.fill_bytes(&mut p1);
        BitSecret { p0, p1 }
    }
    pub fn commit(&self) -> BitCommit {
        BitCommit { h0: hash160(&self.p0), h1: hash160(&self.p1) }
    }
    pub fn preimage(&self, bit: bool) -> Preimage {
        if bit {
            self.p1
        } else {
            self.p0
        }
    }
}

/// Public Lamport key for an n-bit value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PublicKey {
    pub bits: Vec<BitCommit>,
}

/// Secret Lamport key for an n-bit value.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SecretKey {
    pub bits: Vec<BitSecret>,
}

/// Revealed preimages, `preimages[i]` for bit `i` (lsb = 0).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reveal {
    pub preimages: Vec<Preimage>,
}

impl SecretKey {
    pub fn generate<R: RngCore>(n_bits: usize, rng: &mut R) -> SecretKey {
        SecretKey { bits: (0..n_bits).map(|_| BitSecret::generate(rng)).collect() }
    }
    /// Deterministic key from 32 bytes of entropy (a party's seed-derived bytes).
    pub fn from_entropy(n_bits: usize, entropy: [u8; 32]) -> SecretKey {
        use rand::SeedableRng;
        let mut rng = rand::rngs::StdRng::from_seed(entropy);
        SecretKey::generate(n_bits, &mut rng)
    }
    pub fn n_bits(&self) -> usize {
        self.bits.len()
    }
    pub fn public(&self) -> PublicKey {
        PublicKey { bits: self.bits.iter().map(BitSecret::commit).collect() }
    }
    pub fn reveal_bits(&self, bits: &[bool]) -> Result<Reveal> {
        ensure!(bits.len() == self.bits.len(), "reveal_bits: {} bits for a {}-bit key", bits.len(), self.bits.len());
        Ok(Reveal { preimages: self.bits.iter().zip(bits).map(|(s, &b)| s.preimage(b)).collect() })
    }
    pub fn reveal_uint(&self, value: u32) -> Result<Reveal> {
        ensure!(self.n_bits() <= 32, "uint keys are ≤ 32 bits");
        ensure!(self.n_bits() == 32 || value >> self.n_bits() == 0, "value {value} does not fit in {} bits", self.n_bits());
        self.reveal_bits(&uint_to_bits(value, self.n_bits()))
    }
}

impl PublicKey {
    pub fn n_bits(&self) -> usize {
        self.bits.len()
    }
    /// A sub-key covering bits `range` (for decoding fields of a packed state).
    pub fn slice(&self, range: std::ops::Range<usize>) -> PublicKey {
        PublicKey { bits: self.bits[range].to_vec() }
    }
    /// Off-chain check of a reveal: which bit each preimage commits to.
    /// Errors if any preimage matches neither hash.
    pub fn decode_bits(&self, reveal: &Reveal) -> Result<Vec<bool>> {
        ensure!(reveal.preimages.len() == self.bits.len(), "reveal has {} preimages for a {}-bit key", reveal.preimages.len(), self.bits.len());
        let mut out = Vec::with_capacity(self.bits.len());
        for (i, (c, p)) in self.bits.iter().zip(&reveal.preimages).enumerate() {
            let h = hash160(p);
            if h == c.h1 {
                out.push(true)
            } else if h == c.h0 {
                out.push(false)
            } else {
                bail!("preimage for bit {i} matches neither commitment")
            }
        }
        Ok(out)
    }
    pub fn decode_uint(&self, reveal: &Reveal) -> Result<u32> {
        ensure!(self.n_bits() <= 32, "uint keys are ≤ 32 bits");
        Ok(bits_to_uint(&self.decode_bits(reveal)?))
    }
}

impl Reveal {
    /// Witness elements in the order `decode_uint` / `expect_bits` consume them
    /// (msb first). Feed to `WitnessStack::extend`.
    pub fn consumption_order(&self) -> Vec<Vec<u8>> {
        self.preimages.iter().rev().map(|p| p.to_vec()).collect()
    }
    /// Sub-reveal for bits `range`.
    pub fn slice(&self, range: std::ops::Range<usize>) -> Reveal {
        Reveal { preimages: self.preimages[range].to_vec() }
    }
    /// Rebuild a reveal from witness elements taken in consumption order
    /// (the inverse of [`consumption_order`]).
    pub fn from_consumption_order(items: &[Vec<u8>]) -> Result<Reveal> {
        let mut preimages = Vec::with_capacity(items.len());
        for it in items.iter().rev() {
            ensure!(it.len() == PREIMAGE_LEN, "witness element of {} bytes is not a preimage", it.len());
            let mut p = [0u8; PREIMAGE_LEN];
            p.copy_from_slice(it);
            preimages.push(p);
        }
        Ok(Reveal { preimages })
    }
}

pub fn uint_to_bits(value: u32, n_bits: usize) -> Vec<bool> {
    (0..n_bits).map(|i| (value >> i) & 1 == 1).collect()
}

pub fn bits_to_uint(bits: &[bool]) -> u32 {
    bits.iter().rev().fold(0u32, |acc, &b| (acc << 1) | u32::from(b))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_uint() {
        let sk = SecretKey::from_entropy(8, [7u8; 32]);
        let pk = sk.public();
        for v in [0u32, 1, 100, 101, 255] {
            let r = sk.reveal_uint(v).unwrap();
            assert_eq!(pk.decode_uint(&r).unwrap(), v);
            let items = r.consumption_order();
            assert_eq!(Reveal::from_consumption_order(&items).unwrap(), r);
        }
        assert!(sk.reveal_uint(256).is_err());
    }

    #[test]
    fn wrong_preimage_detected() {
        let sk = SecretKey::from_entropy(4, [1u8; 32]);
        let mut r = sk.reveal_uint(5).unwrap();
        r.preimages[2][0] ^= 1;
        assert!(sk.public().decode_uint(&r).is_err());
    }

    #[test]
    fn slices_agree() {
        let sk = SecretKey::from_entropy(6, [2u8; 32]);
        let pk = sk.public();
        let r = sk.reveal_uint(0b101100).unwrap();
        assert_eq!(pk.slice(0..2).decode_uint(&r.slice(0..2)).unwrap(), 0b00);
        assert_eq!(pk.slice(2..4).decode_uint(&r.slice(2..4)).unwrap(), 0b11);
        assert_eq!(pk.slice(4..6).decode_uint(&r.slice(4..6)).unwrap(), 0b10);
    }
}
