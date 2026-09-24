//! Thin layer over rust-bitcoin: keys, taproot trees, sighash, tx building,
//! witness assembly and a regtest `bitcoind` wrapper.
//!
//! Everything in LN-GAP that touches the chain goes through this crate.

pub mod adaptor;
pub mod keys;
pub mod regtest;
pub mod script;
pub mod sighash;
pub mod taptree;
pub mod tx;
pub mod witness;

pub use bitcoin;
pub use bitcoin::secp256k1;

/// Hash160 digest (RIPEMD160(SHA256(x))), as used by `OP_HASH160`.
pub type Hash160 = [u8; 20];

/// `OP_HASH160` of arbitrary data.
pub fn hash160(data: &[u8]) -> Hash160 {
    use bitcoin::hashes::{hash160, Hash};
    hash160::Hash::hash(data).to_byte_array()
}
