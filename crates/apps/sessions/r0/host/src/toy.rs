//! A toy transparent-notes L2 (docs/planning/WITHDRAW_STATEMENT.md),
//! deterministic from fixed seeds, so that any machine builds the same
//! state and the same withdrawal input: an append-only commitment tree of
//! notes, an (empty) nullifier set, and a sequencer that signs state roots
//! with BIP340.

use k256::schnorr::SigningKey;
use lngap_r0_core::{node, state_root, Note, WithdrawInput, TREE_DEPTH};
use sha2::{Digest, Sha256};

fn seed(label: &str) -> [u8; 32] {
    Sha256::digest(label.as_bytes()).into()
}

/// The toy sequencer's signing key.
pub fn sequencer() -> SigningKey {
    SigningKey::from_bytes(&seed("lngap-toy/sequencer")).expect("a valid scalar")
}

/// The toy hub's signing key (it owns the returned notes).
pub fn hub() -> SigningKey {
    SigningKey::from_bytes(&seed("lngap-toy/hub")).expect("a valid scalar")
}

pub fn xonly(k: &SigningKey) -> [u8; 32] {
    k.verifying_key().to_bytes().into()
}

/// The commitment tree: the leaves so far, empty leaves zero.
pub struct Tree {
    leaves: Vec<[u8; 32]>,
}

impl Tree {
    pub fn new() -> Tree {
        Tree { leaves: vec![] }
    }
    pub fn append(&mut self, cm: [u8; 32]) -> u32 {
        self.leaves.push(cm);
        (self.leaves.len() - 1) as u32
    }
    /// Every level, leaves first; each level holds only the nodes over
    /// filled leaves, the rest being the empty subtree's hash.
    fn levels(&self) -> (Vec<Vec<[u8; 32]>>, Vec<[u8; 32]>) {
        let mut zero = vec![[0u8; 32]];
        for l in 0..TREE_DEPTH {
            zero.push(node(&zero[l], &zero[l]));
        }
        let mut levels = vec![self.leaves.clone()];
        for l in 0..TREE_DEPTH {
            let row = &levels[l];
            let next: Vec<[u8; 32]> = row.chunks(2).map(|p| node(&p[0], p.get(1).unwrap_or(&zero[l]))).collect();
            levels.push(next);
        }
        (levels, zero)
    }
    pub fn root(&self) -> [u8; 32] {
        let (levels, zero) = self.levels();
        levels[TREE_DEPTH].first().copied().unwrap_or(zero[TREE_DEPTH])
    }
    pub fn path(&self, index: u32) -> Vec<[u8; 32]> {
        let (levels, zero) = self.levels();
        (0..TREE_DEPTH).map(|l| levels[l].get(((index >> l) ^ 1) as usize).copied().unwrap_or(zero[l])).collect()
    }
}

/// The empty nullifier set's root (the toy has no spends).
pub fn nullifier_root() -> [u8; 32] {
    Sha256::digest(b"lngap/nullifiers/empty").into()
}

/// A deterministic L2 state in which Alice has returned `b` to the hub
/// with memo `c` (among a few other notes), and the withdrawal input for
/// that return, the root signed by the sequencer.
pub fn withdraw_input(b: u32, c: u32) -> WithdrawInput {
    let mut tree = Tree::new();
    let other = |i: u8| Note { owner: seed(&format!("lngap-toy/user/{i}")), value: 100 + u64::from(i), memo: 0, rho: seed(&format!("lngap-toy/rho/{i}")) };
    for i in 0..5 {
        tree.append(other(i).commitment());
    }
    let note = Note { owner: xonly(&hub()), value: u64::from(b), memo: c, rho: seed(&format!("lngap-toy/return/{b}/{c}")) };
    let index = tree.append(note.commitment());
    for i in 5..7 {
        tree.append(other(i).commitment());
    }
    let height = 42;
    let nullifiers = nullifier_root();
    let root = state_root(height, &tree.root(), &nullifiers);
    let signature = sequencer().sign_raw(&root, &[0u8; 32]).expect("signing").to_bytes().to_vec();
    WithdrawInput { height, nullifiers, signature, note, index, path: tree.path(index) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lngap_r0_core::{check, root_from_path, Reject, HUB_KEY, SEQUENCER_KEY};

    #[test]
    fn the_constants_are_the_seeds_keys() {
        assert_eq!(SEQUENCER_KEY, xonly(&sequencer()), "core's SEQUENCER_KEY: {}", hex::encode(xonly(&sequencer())));
        assert_eq!(HUB_KEY, xonly(&hub()), "core's HUB_KEY: {}", hex::encode(xonly(&hub())));
    }

    #[test]
    fn paths_reach_the_root() {
        let mut t = Tree::new();
        for i in 0..7u8 {
            t.append([i; 32]);
        }
        for i in 0..7u32 {
            assert_eq!(root_from_path([i as u8; 32], i, &t.path(i)), t.root(), "leaf {i}");
        }
    }

    #[test]
    fn the_statement_holds_and_rejects() {
        let input = withdraw_input(9, 42);
        assert_eq!(check(&input, &SEQUENCER_KEY, &HUB_KEY), Ok([9, 0, 0, 0, 42, 0, 0, 0]));
        let mut bad = input.clone();
        bad.note.value = 10;
        assert_eq!(check(&bad, &SEQUENCER_KEY, &HUB_KEY), Err(Reject::BadSignature), "another value is not in the signed state");
        let mut bad = input.clone();
        bad.note.owner = [7; 32];
        assert_eq!(check(&bad, &SEQUENCER_KEY, &HUB_KEY), Err(Reject::NotTheHubs));
        let mut bad = input;
        bad.signature[0] ^= 1;
        assert_eq!(check(&bad, &SEQUENCER_KEY, &HUB_KEY), Err(Reject::BadSignature));
    }
}
