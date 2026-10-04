//! A name owner: keys, salt, and the events it produces.

use bitcoin::key::{Keypair, XOnlyPublicKey};
use lngap_btc::keys::Seed;

use crate::registry::{commit_hash, sign_transfer, Event, Hash32};

pub struct NamesUser {
    pub name: String,
    pub owner: Keypair,
    pub salt: Hash32,
}

impl NamesUser {
    pub fn new(seed: &Seed, name: &str) -> NamesUser {
        NamesUser { name: name.to_string(), owner: seed.keypair("name-owner"), salt: seed.derive_bytes("name-salt") }
    }
    pub fn owner_key(&self) -> XOnlyPublicKey {
        self.owner.x_only_public_key().0
    }
    pub fn commit_event(&self) -> Event {
        Event::Commit { c: commit_hash(&self.name, &self.owner_key(), &self.salt) }
    }
    pub fn reveal_event(&self) -> Event {
        Event::Reveal { name: self.name.clone(), owner: self.owner_key(), salt: self.salt }
    }
    pub fn transfer_event(&self, new_owner: &XOnlyPublicKey, valid_until: u32) -> Event {
        sign_transfer(&self.owner, &self.name, new_owner, valid_until)
    }
}
