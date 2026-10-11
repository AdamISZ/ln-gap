//! The withdrawal statement of the sessions PoC (docs/planning/
//! WITHDRAW_STATEMENT.md), over a transparent notes L2:
//!
//! ```text
//! note  = (owner: 32-byte x-only key, value: u64, memo: u32, rho: 32 bytes)
//! cm    = SHA256("lngap/note" ‖ owner ‖ value ‖ memo ‖ rho)
//! T     = root of the append-only commitment tree (depth TREE_DEPTH, SHA-256)
//! R     = SHA256("lngap/root" ‖ height ‖ T ‖ N)     N: the nullifier set's root
//! ```
//!
//! The sequencer signs `R` (BIP340). The statement: a note owned by the
//! hub, of value `b` and memo `c`, is in the commitment tree of a state
//! root the sequencer signed. Its journal is `b ‖ c` (little-endian u32s).
//! Not checked here: that `R` follows from valid transitions (the
//! validity assumption; the `transition` guest's job).
//!
//! The sequencer's and the hub's keys are constants: the guest's image id
//! pins them (one image per L2 deployment). In the toy they come from
//! fixed seeds (see the host).

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

use k256::schnorr::{Signature, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// The commitment tree's depth: 2^16 notes.
pub const TREE_DEPTH: usize = 16;

/// The toy L2's sequencer key (x-only), from the seed "lngap-toy/sequencer".
pub const SEQUENCER_KEY: [u8; 32] = [
    0xa7, 0xad, 0x0e, 0xb4, 0xbc, 0xc5, 0xdf, 0x74, 0xd9, 0x6c, 0xb0, 0x35, 0xfd, 0xcc, 0x75, 0x3e,
    0x47, 0x2a, 0xfa, 0x7f, 0x54, 0x73, 0xfc, 0xcf, 0x9e, 0xe5, 0x6f, 0xc7, 0x92, 0x03, 0xd1, 0x7f,
];

/// The toy hub's key (x-only), from the seed "lngap-toy/hub".
pub const HUB_KEY: [u8; 32] = [
    0xd3, 0xb3, 0x18, 0xbc, 0x30, 0x36, 0x56, 0x6f, 0x33, 0xf5, 0xea, 0x00, 0x0a, 0x7e, 0xee, 0xfc,
    0x41, 0xcb, 0x6d, 0xac, 0x09, 0xfd, 0x3a, 0x23, 0x76, 0xf2, 0x43, 0x79, 0x84, 0xea, 0xdf, 0xea,
];

/// A note.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Note {
    pub owner: [u8; 32],
    pub value: u64,
    pub memo: u32,
    pub rho: [u8; 32],
}

impl Note {
    pub fn commitment(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(b"lngap/note");
        h.update(self.owner);
        h.update(self.value.to_be_bytes());
        h.update(self.memo.to_be_bytes());
        h.update(self.rho);
        h.finalize().into()
    }
}

/// A node of the commitment tree.
pub fn node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(left);
    h.update(right);
    h.finalize().into()
}

/// The root a leaf at `index` reaches through `path` (siblings, leaf
/// level first).
pub fn root_from_path(leaf: [u8; 32], index: u32, path: &[[u8; 32]]) -> [u8; 32] {
    let mut h = leaf;
    for (level, sib) in path.iter().enumerate() {
        h = if (index >> level) & 1 == 1 { node(sib, &h) } else { node(&h, sib) };
    }
    h
}

/// The state root the sequencer signs.
pub fn state_root(height: u64, tree: &[u8; 32], nullifiers: &[u8; 32]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"lngap/root");
    h.update(height.to_be_bytes());
    h.update(tree);
    h.update(nullifiers);
    h.finalize().into()
}

/// The guest's private input.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WithdrawInput {
    pub height: u64,
    /// The nullifier set's root at that height.
    pub nullifiers: [u8; 32],
    /// The sequencer's BIP340 signature on the state root.
    pub signature: Vec<u8>,
    /// Alice's return: a note owned by the hub, value `b`, memo `c`.
    pub note: Note,
    pub index: u32,
    pub path: Vec<[u8; 32]>,
}

/// Why a withdrawal input is rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reject {
    NotTheHubs,
    PathLength,
    TooLarge,
    BadSignature,
}

/// The statement: check `input` against the sequencer's and the hub's
/// keys; on success, the journal `b ‖ c`.
pub fn check(input: &WithdrawInput, sequencer: &[u8; 32], hub: &[u8; 32]) -> Result<[u8; 8], Reject> {
    if &input.note.owner != hub {
        return Err(Reject::NotTheHubs);
    }
    if input.path.len() != TREE_DEPTH {
        return Err(Reject::PathLength);
    }
    let b = u32::try_from(input.note.value).map_err(|_| Reject::TooLarge)?;
    let tree = root_from_path(input.note.commitment(), input.index, &input.path);
    let root = state_root(input.height, &tree, &input.nullifiers);
    let key = VerifyingKey::from_bytes(sequencer).map_err(|_| Reject::BadSignature)?;
    let sig = Signature::try_from(input.signature.as_slice()).map_err(|_| Reject::BadSignature)?;
    key.verify_raw(&root, &sig).map_err(|_| Reject::BadSignature)?;
    let mut journal = [0u8; 8];
    journal[..4].copy_from_slice(&b.to_le_bytes());
    journal[4..].copy_from_slice(&input.note.memo.to_le_bytes());
    Ok(journal)
}
