//! Hub statements as 32-bit Lamport slots. A statement's *label* names the
//! key; its *value* is a 32-bit id of what it says. Revealing the preimages
//! for that value under that key is the hub saying it.

use bitcoin::hashes::{sha256, Hash};
use bitcoin::key::XOnlyPublicKey;

use crate::registry::short;

pub const STATEMENT_BITS: usize = 32;

pub fn receipt_label(req_id: u32) -> String {
    format!("receipt/{req_id}")
}
/// A receipt says the request id itself.
pub fn receipt_value(req_id: u32) -> u32 {
    req_id
}

pub fn attest_label(name: &str, owner: &XOnlyPublicKey) -> String {
    format!("attest/{name}/{}", short(owner))
}
/// "the registry as anchored shows `name` owned by `owner`", as a 32-bit id.
pub fn attest_value(name: &str, owner: &XOnlyPublicKey) -> u32 {
    let mut e = sha256::Hash::engine();
    use bitcoin::hashes::HashEngine;
    e.input(b"lngap-names-attest");
    e.input(name.as_bytes());
    e.input(&owner.serialize());
    let h = sha256::Hash::from_engine(e).to_byte_array();
    u32::from_le_bytes([h[0], h[1], h[2], h[3]])
}
