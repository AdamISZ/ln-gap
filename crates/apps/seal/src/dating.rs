//! Dating moves (V25_POC_PLAN.md, Phase 3): leaves, a member's period
//! tree, paths, and the mover's choice key.
//!
//! A member's root for a period is a BLAKE3-160 Merkle root over the
//! LEAVES of the moves it received in that period. A leaf binds a move to
//! its contract and depth:
//!
//! ```text
//! leaf = BLAKE3-160( contract (4 bytes, big-endian) ‖ depth (2 bytes) ‖ choice )
//! node = BLAKE3-160( left ‖ right )
//! ```
//!
//! BLAKE3-160 is BitVMX's (the first 20 bytes of BLAKE3's output), the hash
//! the dispute leaves will recompute in Script over nibbles.
//!
//! WHY THE LEAF DOES NOT CARRY THE MOVER'S SIGNATURE (a change from the
//! v2.5 note, found while building this). The design note made the leaf
//! `BLAKE3(choice ‖ choice signature)`, so that members could date only
//! moves the mover signed (closing the "option" attack, where colluding
//! members date several candidate moves and the mover signs the best one
//! later). But a Winternitz signature's elements are 20-byte hash-chain
//! values, which Script handles only as whole stack items, while the
//! BLAKE3 script works on nibbles; without `OP_CAT` there is no way to show
//! in Script that a 20-byte item and 40 nibbles are the same value. So the
//! leaf binds the choice only, and authorship is checked in the rebuttal
//! (the choice signature, as before). The option attack returns, and is
//! harmless for deterministic games such as the search over a verifier
//! (bisection is sound against an adaptive prover); for games where time
//! has value, a nibble-native authorship token (per-digit, per-value
//! secrets committed with BLAKE3) is the extension, not built.

use anyhow::{ensure, Result};
use lngap_lamport::winternitz::{WotsParams, WotsPublic, WotsSecret, WotsSig};

/// BitVMX's BLAKE3-160: BLAKE3, truncated to 20 bytes.
pub fn blake3_160(data: &[u8]) -> [u8; 20] {
    let mut h = blake3::Hasher::new();
    h.update(data);
    let mut out = [0u8; 20];
    h.finalize_xof().fill(&mut out);
    out
}

/// The padding leaf of an incomplete tree (no move hashes to it, except
/// with negligible probability).
pub const PAD_LEAF: [u8; 20] = [0u8; 20];

/// A move to be dated: the mover's choice at one depth of one contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Choice {
    pub contract: u32,
    pub depth: u16,
    pub value: Vec<u8>,
}

impl Choice {
    /// The leaf preimage: contract ‖ depth ‖ value.
    pub fn leaf_bytes(&self) -> Vec<u8> {
        let mut v = self.contract.to_be_bytes().to_vec();
        v.extend_from_slice(&self.depth.to_be_bytes());
        v.extend_from_slice(&self.value);
        v
    }
    pub fn leaf(&self) -> [u8; 20] {
        blake3_160(&self.leaf_bytes())
    }
}

/// The mover's one-time choice key for one depth of one contract: a
/// Winternitz key over the choice's bytes, fixed at open.
pub struct ChoiceKey {
    secret: WotsSecret,
}

impl ChoiceKey {
    pub fn new(entropy: [u8; 32], choice_bytes: u32) -> ChoiceKey {
        ChoiceKey { secret: WotsSecret::from_entropy(WotsParams::for_bytes(choice_bytes), entropy) }
    }
    pub fn public(&self) -> WotsPublic {
        self.secret.public()
    }
    pub fn sign(&self, value: &[u8]) -> Result<WotsSig> {
        self.secret.sign(value)
    }
}

/// A signed move, as the mover sends it to every member.
#[derive(Clone, Debug)]
pub struct SignedChoice {
    pub choice: Choice,
    pub sig: WotsSig,
}

impl SignedChoice {
    /// Check the signature against the contract's registered choice key.
    pub fn verify(&self, key: &WotsPublic) -> Result<()> {
        ensure!(key.verify(&self.sig)? == self.choice.value, "the choice signature is for a different value");
        Ok(())
    }
}

/// A Merkle path: siblings from the leaf up, and per level whether the
/// node on the path is the RIGHT child (its sibling on the left).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Path {
    pub siblings: Vec<[u8; 20]>,
    pub is_right: Vec<bool>,
}

impl Path {
    /// The root this path leads to from `leaf`.
    pub fn root_from(&self, leaf: [u8; 20]) -> [u8; 20] {
        let mut h = leaf;
        for (sib, right) in self.siblings.iter().zip(&self.is_right) {
            let mut buf = [0u8; 40];
            if *right {
                buf[..20].copy_from_slice(sib);
                buf[20..].copy_from_slice(&h);
            } else {
                buf[..20].copy_from_slice(&h);
                buf[20..].copy_from_slice(sib);
            }
            h = blake3_160(&buf);
        }
        h
    }
    /// The child digests along the path, leaf first and root last (what a
    /// rebuttal asserts: `c_0 .. c_L`).
    pub fn digests(&self, leaf: [u8; 20]) -> Vec<[u8; 20]> {
        let mut out = vec![leaf];
        let mut h = leaf;
        for (sib, right) in self.siblings.iter().zip(&self.is_right) {
            let mut buf = [0u8; 40];
            if *right {
                buf[..20].copy_from_slice(sib);
                buf[20..].copy_from_slice(&h);
            } else {
                buf[..20].copy_from_slice(&h);
                buf[20..].copy_from_slice(sib);
            }
            h = blake3_160(&buf);
            out.push(h);
        }
        out
    }
}

/// A member's tree for one period: leaves in arrival order, padded to a
/// power of two (at least two leaves, so every path has a level).
#[derive(Clone, Debug)]
pub struct PeriodTree {
    leaves: Vec<[u8; 20]>,
    /// `levels[0]` is the padded leaf row, the last level is the root.
    levels: Vec<Vec<[u8; 20]>>,
}

impl PeriodTree {
    pub fn new(leaves: Vec<[u8; 20]>) -> PeriodTree {
        let width = leaves.len().max(2).next_power_of_two();
        let mut row = leaves.clone();
        row.resize(width, PAD_LEAF);
        let mut levels = vec![row];
        while levels.last().unwrap().len() > 1 {
            let next = levels
                .last()
                .unwrap()
                .chunks(2)
                .map(|p| {
                    let mut buf = [0u8; 40];
                    buf[..20].copy_from_slice(&p[0]);
                    buf[20..].copy_from_slice(&p[1]);
                    blake3_160(&buf)
                })
                .collect();
            levels.push(next);
        }
        PeriodTree { leaves, levels }
    }
    pub fn root(&self) -> [u8; 20] {
        self.levels.last().unwrap()[0]
    }
    /// The tree's depth `L` (path length).
    pub fn depth(&self) -> usize {
        self.levels.len() - 1
    }
    pub fn leaves(&self) -> &[[u8; 20]] {
        &self.leaves
    }
    /// The path of the leaf at `index`.
    pub fn path(&self, index: usize) -> Result<Path> {
        ensure!(index < self.leaves.len(), "no leaf at {index}");
        let mut i = index;
        let mut siblings = Vec::with_capacity(self.depth());
        let mut is_right = Vec::with_capacity(self.depth());
        for row in &self.levels[..self.depth()] {
            siblings.push(row[i ^ 1]);
            is_right.push(i % 2 == 1);
            i /= 2;
        }
        Ok(Path { siblings, is_right })
    }
    /// The path of a leaf by value (its first occurrence).
    pub fn path_of(&self, leaf: [u8; 20]) -> Option<Path> {
        self.leaves.iter().position(|l| *l == leaf).and_then(|i| self.path(i).ok())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(i: u8) -> [u8; 20] {
        Choice { contract: 7, depth: u16::from(i), value: vec![i] }.leaf()
    }

    #[test]
    fn blake3_160_matches_bitvmx() {
        // BLAKE3("") truncated: af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9
        assert_eq!(hex_of(&blake3_160(b"")), "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9");
    }

    fn hex_of(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    #[test]
    fn every_path_leads_to_the_root() {
        for n in [1usize, 2, 3, 5, 8, 13] {
            let leaves: Vec<_> = (0..n as u8).map(leaf).collect();
            let t = PeriodTree::new(leaves.clone());
            for (i, l) in leaves.iter().enumerate() {
                let p = t.path(i).unwrap();
                assert_eq!(p.siblings.len(), t.depth());
                assert_eq!(p.root_from(*l), t.root(), "n = {n}, leaf {i}");
                let d = p.digests(*l);
                assert_eq!((d[0], *d.last().unwrap()), (*l, t.root()));
            }
            // a different leaf at the same position does not reach the root
            let p = t.path(0).unwrap();
            assert_ne!(p.root_from(leaf(99)), t.root());
        }
    }

    #[test]
    fn a_choice_signature_binds_the_value() {
        let k = ChoiceKey::new([5; 32], 1);
        let c = Choice { contract: 1, depth: 3, value: vec![42] };
        let s = SignedChoice { choice: c.clone(), sig: k.sign(&[42]).unwrap() };
        s.verify(&k.public()).unwrap();
        let forged = SignedChoice { choice: Choice { value: vec![43], ..c }, sig: s.sig.clone() };
        assert!(forged.verify(&k.public()).is_err());
    }
}
