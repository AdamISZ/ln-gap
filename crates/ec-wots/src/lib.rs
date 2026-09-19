//! EC-WOTS: a one-time attestation scheme with a Script-native readout.
//!
//! Design doc: `docs/planning/hermes-research/EC_WOTS.md`. A
//! Winternitz-family one-time signature with the one-way function moved from
//! hash chains to EC discrete logs. Per epoch, the attester commits to a table
//! of 16 anticipation points per 4-bit message chunk; an attestation reveals
//! one scalar per chunk; the Script readout ([`readout_leaf`]) is one
//! OP_CHECKSIG possession proof per chunk against the point selected by the
//! chunk value, leaving the message on the stack as verified nibbles.
//!
//! The attester in this crate is a single key standing in for a FROST quorum:
//! a FROST group key is a plain BIP340 key and indistinguishable on-chain, so
//! every Script-level property tested here is the same one a quorum gets.

mod leaf;
mod table;

pub use leaf::{
    readout_leaf, readout_value_fragment, readout_values_leaf, readout_values_witness,
    readout_witness_args, slash_leaf, slash_witness_args, CHUNK_SCRIPT_BYTES,
};
pub use table::{Attestation, Attester, EpochTable};

/// The value of message chunk `j`: the j-th nibble, high nibble first.
pub fn chunk_value(msg: &[u8], j: usize) -> u8 {
    let b = msg[j / 2];
    if j % 2 == 0 {
        b >> 4
    } else {
        b & 15
    }
}

/// Minimal script-number encoding of a nibble (0..=15): 0 is the empty
/// element, otherwise one byte.
pub fn snum(v: u8) -> Vec<u8> {
    assert!(v < 16, "a chunk value is a nibble");
    if v == 0 {
        vec![]
    } else {
        vec![v]
    }
}
