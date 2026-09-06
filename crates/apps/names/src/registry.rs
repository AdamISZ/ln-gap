//! Registry rules, event log, Merkle root, resolution.

use bitcoin::hashes::{sha256, Hash};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::secp256k1::{schnorr, Message, SECP256K1};
use serde::{Deserialize, Serialize};

/// Commit-reveal window: a reveal counts only if anchored within `N` blocks
/// of its commit's anchor.
pub const N: u32 = 20;
pub const MAX_NAME: usize = 16;

pub type Hash32 = [u8; 32];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Event {
    Commit { c: Hash32 },
    Reveal { name: String, owner: XOnlyPublicKey, salt: Hash32 },
    Transfer { name: String, new_owner: XOnlyPublicKey, valid_until: u32, sig: schnorr::Signature },
}

impl Event {
    pub fn describe(&self) -> String {
        match self {
            Event::Commit { c } => format!("commit {}", hex::encode(&c[..8])),
            Event::Reveal { name, owner, .. } => format!("reveal {name} -> {}", short(owner)),
            Event::Transfer { name, new_owner, valid_until, .. } => format!("transfer {name} -> {} (valid until {valid_until})", short(new_owner)),
        }
    }
    pub fn name(&self) -> Option<&str> {
        match self {
            Event::Commit { .. } => None,
            Event::Reveal { name, .. } | Event::Transfer { name, .. } => Some(name),
        }
    }
}

pub fn short(k: &XOnlyPublicKey) -> String {
    hex::encode(&k.serialize()[..4])
}

pub fn commit_hash(name: &str, owner: &XOnlyPublicKey, salt: &Hash32) -> Hash32 {
    let mut e = sha256::Hash::engine();
    use bitcoin::hashes::HashEngine;
    e.input(b"lngap-names-commit");
    e.input(name.as_bytes());
    e.input(&owner.serialize());
    e.input(salt);
    sha256::Hash::from_engine(e).to_byte_array()
}

fn transfer_msg(name: &str, new_owner: &XOnlyPublicKey, valid_until: u32) -> Message {
    let mut e = sha256::Hash::engine();
    use bitcoin::hashes::HashEngine;
    e.input(b"lngap-names-transfer");
    e.input(name.as_bytes());
    e.input(&new_owner.serialize());
    e.input(&valid_until.to_le_bytes());
    Message::from_digest(sha256::Hash::from_engine(e).to_byte_array())
}

/// The current owner signs `(name, new_owner, valid_until)` (D4).
pub fn sign_transfer(owner: &Keypair, name: &str, new_owner: &XOnlyPublicKey, valid_until: u32) -> Event {
    let sig = SECP256K1.sign_schnorr(&transfer_msg(name, new_owner, valid_until), owner);
    Event::Transfer { name: name.to_string(), new_owner: *new_owner, valid_until, sig }
}

pub fn verify_transfer(owner: &XOnlyPublicKey, name: &str, new_owner: &XOnlyPublicKey, valid_until: u32, sig: &schnorr::Signature) -> bool {
    SECP256K1.verify_schnorr(sig, &transfer_msg(name, new_owner, valid_until), owner).is_ok()
}

/// An event as anchored: the height of the anchor that carries it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Anchored {
    pub event: Event,
    pub height: u32,
}

/// The published ledger: anchored events in anchor order.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Ledger {
    pub events: Vec<Anchored>,
}

pub fn leaf_hash(a: &Anchored) -> Hash32 {
    let bytes = serde_json::to_vec(a).expect("serializable");
    sha256::Hash::hash(&bytes).to_byte_array()
}

/// Merkle root over `leaves` (duplicate the last on odd levels); empty → zeros.
pub fn merkle_root(mut level: Vec<Hash32>) -> Hash32 {
    if level.is_empty() {
        return [0u8; 32];
    }
    while level.len() > 1 {
        if level.len() % 2 == 1 {
            level.push(*level.last().unwrap());
        }
        level = level
            .chunks(2)
            .map(|p| {
                let mut e = sha256::Hash::engine();
                use bitcoin::hashes::HashEngine;
                e.input(&p[0]);
                e.input(&p[1]);
                sha256::Hash::from_engine(e).to_byte_array()
            })
            .collect();
    }
    level[0]
}

impl Ledger {
    pub fn root(&self) -> Hash32 {
        merkle_root(self.events.iter().map(leaf_hash).collect())
    }

    /// Ledger as of (including) anchors at `height`.
    pub fn as_of(&self, height: u32) -> Ledger {
        Ledger { events: self.events.iter().filter(|a| a.height <= height).cloned().collect() }
    }

    /// Client-side resolution of `name` under the rules.
    pub fn resolve(&self, name: &str) -> Option<XOnlyPublicKey> {
        // earliest anchored commit whose reveal (for this name) was anchored within N
        let mut best: Option<(u32, XOnlyPublicKey)> = None;
        for r in &self.events {
            if let Event::Reveal { name: n, owner, salt } = &r.event {
                if n != name {
                    continue;
                }
                let c = commit_hash(n, owner, salt);
                let commit_h = self.events.iter().find(|a| matches!(&a.event, Event::Commit { c: cc } if *cc == c)).map(|a| a.height);
                if let Some(ch) = commit_h {
                    if ch <= r.height && r.height <= ch + N && best.is_none_or(|(bh, _)| ch < bh) {
                        best = Some((ch, *owner));
                    }
                }
            }
        }
        let (_, mut owner) = best?;
        // transfers in anchor order, each signed by the then-owner and anchored by valid_until
        for t in &self.events {
            if let Event::Transfer { name: n, new_owner, valid_until, sig } = &t.event {
                if n == name && t.height <= *valid_until && verify_transfer(&owner, n, new_owner, *valid_until, sig) {
                    owner = *new_owner;
                }
            }
        }
        Some(owner)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lngap_btc::keys::Seed;

    #[test]
    fn rules() {
        let a = Seed::from_label("a").keypair("owner");
        let b = Seed::from_label("b").keypair("owner");
        let (ka, kb) = (a.x_only_public_key().0, b.x_only_public_key().0);
        let salt = [7u8; 32];
        let c = commit_hash("alice", &ka, &salt);
        let mut l = Ledger::default();
        l.events.push(Anchored { event: Event::Commit { c }, height: 100 });
        assert_eq!(l.resolve("alice"), None, "commit alone");
        l.events.push(Anchored { event: Event::Reveal { name: "alice".into(), owner: ka, salt }, height: 105 });
        assert_eq!(l.resolve("alice"), Some(ka));
        // a later commit by b does not win
        let salt2 = [8u8; 32];
        l.events.push(Anchored { event: Event::Commit { c: commit_hash("alice", &kb, &salt2) }, height: 106 });
        l.events.push(Anchored { event: Event::Reveal { name: "alice".into(), owner: kb, salt: salt2 }, height: 107 });
        assert_eq!(l.resolve("alice"), Some(ka));
        // transfer signed by a, anchored in time
        let t = sign_transfer(&a, "alice", &kb, 120);
        let mut late = l.clone();
        late.events.push(Anchored { event: t.clone(), height: 121 });
        assert_eq!(late.resolve("alice"), Some(ka), "late anchor ignored (D4)");
        l.events.push(Anchored { event: t, height: 110 });
        assert_eq!(l.resolve("alice"), Some(kb));
        // transfer signed by the wrong key
        let bad = sign_transfer(&a, "alice", &ka, 130);
        l.events.push(Anchored { event: bad, height: 111 });
        assert_eq!(l.resolve("alice"), Some(kb));
        assert_ne!(l.root(), Ledger::default().root());
    }
}
