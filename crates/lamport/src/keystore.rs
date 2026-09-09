//! Per-party store of one-time keys. Keys are generated per label, consumed
//! on reveal, and can never be revealed to two different values.

use std::collections::HashMap;

use anyhow::{anyhow, bail, Result};
use lngap_btc::keys::Seed;

use crate::{PublicKey, Reveal, SecretKey};

#[derive(Debug)]
struct Entry {
    sk: SecretKey,
    revealed: Option<Vec<bool>>,
}

/// Owned by one party; derives keys deterministically from that party's seed.
#[derive(Debug)]
pub struct KeyStore {
    seed: Seed,
    keys: HashMap<String, Entry>,
    wots: HashMap<String, WotsEntry>,
}

impl KeyStore {
    pub fn new(seed: Seed) -> KeyStore {
        KeyStore { seed, keys: HashMap::new(), wots: HashMap::new() }
    }

    /// Generate (or return the existing) key for `label`. Labels must encode
    /// (contract instance, depth position, field); the store refuses to hand
    /// out a differently-sized key under a used label.
    pub fn generate(&mut self, label: &str, n_bits: usize) -> Result<PublicKey> {
        if let Some(e) = self.keys.get(label) {
            if e.sk.n_bits() != n_bits {
                bail!("label {label} already used with {} bits", e.sk.n_bits());
            }
            return Ok(e.sk.public());
        }
        let sk = SecretKey::from_entropy(n_bits, self.seed.derive_bytes(&format!("lamport/{label}")));
        let pk = sk.public();
        self.keys.insert(label.to_string(), Entry { sk, revealed: None });
        Ok(pk)
    }

    pub fn public(&self, label: &str) -> Result<PublicKey> {
        Ok(self.keys.get(label).ok_or_else(|| anyhow!("no key {label}"))?.sk.public())
    }

    /// Reveal `bits` under `label`. A second reveal of the same bits is fine
    /// (idempotent re-broadcast); a reveal of different bits is refused.
    pub fn reveal_bits(&mut self, label: &str, bits: &[bool]) -> Result<Reveal> {
        let e = self.keys.get_mut(label).ok_or_else(|| anyhow!("no key {label}"))?;
        if let Some(prev) = &e.revealed {
            if prev != bits {
                bail!("key {label} already revealed to a different value; refusing to equivocate");
            }
        }
        let r = e.sk.reveal_bits(bits)?;
        e.revealed = Some(bits.to_vec());
        Ok(r)
    }

    pub fn reveal_uint(&mut self, label: &str, value: u32) -> Result<Reveal> {
        let n = self.keys.get(label).ok_or_else(|| anyhow!("no key {label}"))?.sk.n_bits();
        self.reveal_bits(label, &crate::uint_to_bits(value, n))
    }

    pub fn is_revealed(&self, label: &str) -> bool {
        self.keys.get(label).and_then(|e| e.revealed.as_ref()).is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refuses_equivocation() {
        let mut ks = KeyStore::new(Seed::from_label("t"));
        let pk = ks.generate("c1/d1/move", 4).unwrap();
        let r = ks.reveal_uint("c1/d1/move", 3).unwrap();
        assert_eq!(pk.decode_uint(&r).unwrap(), 3);
        assert!(ks.reveal_uint("c1/d1/move", 3).is_ok());
        assert!(ks.reveal_uint("c1/d1/move", 4).is_err());
        assert!(ks.generate("c1/d1/move", 5).is_err());
    }
}

// ----- Winternitz keys (256-bit values) in the same store -----

use crate::winternitz::{WotsParams, WotsPublic, WotsSecret, WotsSig};

#[derive(Debug)]
struct WotsEntry {
    sk: WotsSecret,
    signed: Option<Vec<u8>>,
}

impl KeyStore {
    fn wots_map(&mut self) -> &mut HashMap<String, WotsEntry> {
        &mut self.wots
    }

    /// Generate (or return) the Winternitz key for `label` over `n_bytes`.
    pub fn generate_wots(&mut self, label: &str, n_bytes: u32) -> Result<WotsPublic> {
        let params = WotsParams::for_bytes(n_bytes);
        if let Some(e) = self.wots.get(label) {
            if e.sk.params != params {
                bail!("wots label {label} already used with other params");
            }
            return Ok(e.sk.public());
        }
        let sk = WotsSecret::from_entropy(params, self.seed.derive_bytes(&format!("wots/{label}")));
        let pk = sk.public();
        self.wots_map().insert(label.to_string(), WotsEntry { sk, signed: None });
        Ok(pk)
    }

    pub fn wots_public(&self, label: &str) -> Result<WotsPublic> {
        Ok(self.wots.get(label).ok_or_else(|| anyhow!("no wots key {label}"))?.sk.public())
    }

    /// Sign `msg` under `label`; refuses a second signature of a different message.
    pub fn sign_wots(&mut self, label: &str, msg: &[u8]) -> Result<WotsSig> {
        let e = self.wots.get_mut(label).ok_or_else(|| anyhow!("no wots key {label}"))?;
        if let Some(prev) = &e.signed {
            if prev != msg {
                bail!("wots key {label} already signed a different message; refusing to equivocate");
            }
        }
        let sig = e.sk.sign(msg)?;
        e.signed = Some(msg.to_vec());
        Ok(sig)
    }
}
