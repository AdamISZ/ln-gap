//! A sparse Merkle tree over 32-bit keys (decision 5): depth 32, SHA-256
//! of `left ‖ right` at every node, leaf = SHA-256 of the 64-byte entry
//! (name ‖ owner), empty leaf = 32 zero bytes. Key = the first 32 bits of
//! SHA-256(name). Side at level `j` (0 = leaf level) = bit `j` of the key
//! (1: the node is the right child).

use std::collections::HashMap;

use sha2::{Digest, Sha256};

pub const DEPTH: usize = 32;
pub const EMPTY_LEAF: [u8; 32] = [0u8; 32];

pub fn sha256(data: &[u8]) -> [u8; 32] {
    Sha256::digest(data).into()
}

pub fn key_of(name: &[u8]) -> u32 {
    u32::from_be_bytes(sha256(name)[..4].try_into().unwrap())
}

/// A 64-byte entry: name (32, zero-padded) ‖ owner (32).
pub fn entry_bytes(name: &[u8], owner: &[u8; 32]) -> [u8; 64] {
    let mut e = [0u8; 64];
    e[..name.len().min(32)].copy_from_slice(&name[..name.len().min(32)]);
    e[32..].copy_from_slice(owner);
    e
}

pub fn leaf_hash(entry: &[u8; 64]) -> [u8; 32] {
    sha256(entry)
}

pub fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut b = [0u8; 64];
    b[..32].copy_from_slice(left);
    b[32..].copy_from_slice(right);
    sha256(&b)
}

/// An inclusion (or non-inclusion) path: the leaf hash and 32 siblings from the leaf up.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Path {
    pub key: u32,
    pub leaf: [u8; 32],
    pub siblings: Vec<[u8; 32]>,
}

impl Path {
    pub fn side(&self, level: usize) -> bool {
        (self.key >> level) & 1 == 1
    }
    pub fn root(&self) -> [u8; 32] {
        let mut h = self.leaf;
        for (j, s) in self.siblings.iter().enumerate() {
            h = if self.side(j) { node_hash(s, &h) } else { node_hash(&h, s) };
        }
        h
    }
}

#[derive(Clone, Debug, Default)]
pub struct Ledger {
    /// key → entry
    pub entries: HashMap<u32, [u8; 64]>,
}

impl Ledger {
    pub fn insert(&mut self, name: &[u8], owner: &[u8; 32]) -> u32 {
        let k = key_of(name);
        self.entries.insert(k, entry_bytes(name, owner));
        k
    }
    /// The empty-subtree hashes by level (0 = leaf).
    fn empties() -> Vec<[u8; 32]> {
        let mut v = vec![EMPTY_LEAF];
        for j in 0..DEPTH {
            v.push(node_hash(&v[j], &v[j]));
        }
        v
    }
    /// Hash of the level-`level` node (0 = leaf, 32 = root) whose keys all
    /// have `key >> level == hi`.
    fn subtree(&self, level: usize, hi: u32, empties: &[[u8; 32]]) -> [u8; 32] {
        let shift = |k: u32| if level >= 32 { 0 } else { k >> level };
        let mut keys: Vec<&u32> = self.entries.keys().filter(|k| shift(**k) == hi).collect();
        if keys.is_empty() {
            return empties[level];
        }
        if level == 0 {
            keys.sort();
            return leaf_hash(&self.entries[keys[0]]);
        }
        let l = self.subtree(level - 1, hi << 1, empties);
        let r = self.subtree(level - 1, (hi << 1) | 1, empties);
        node_hash(&l, &r)
    }
    pub fn root(&self) -> [u8; 32] {
        self.subtree(DEPTH, 0, &Self::empties())
    }
    /// Path for `key` (inclusion if present, non-inclusion otherwise).
    pub fn path(&self, key: u32) -> Path {
        let empties = Self::empties();
        let leaf = self.entries.get(&key).map(leaf_hash).unwrap_or(EMPTY_LEAF);
        let siblings = (0..DEPTH).map(|j| self.subtree(j, (key >> j) ^ 1, &empties)).collect();
        Path { key, leaf, siblings }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paths_reach_the_root() {
        let mut l = Ledger::default();
        let a = l.insert(b"alice", &[1u8; 32]);
        let b = l.insert(b"bob", &[2u8; 32]);
        let root = l.root();
        assert_eq!(l.path(a).root(), root);
        assert_eq!(l.path(b).root(), root);
        let missing = l.path(key_of(b"carol"));
        assert_eq!(missing.leaf, EMPTY_LEAF);
        assert_eq!(missing.root(), root);
        assert_ne!(Ledger::default().root(), root);
    }
}
