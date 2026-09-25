//! The fee lock's venue side (ATTESTATION_FEES.md; D49, D52, D53): the
//! point a payer locks a fee to, and the secret the venue's attestation
//! reveals.
//!
//! The head a mover will publish selects one anticipation point per head
//! chunk under the slot's shared content table; their sum `C_h` has the
//! log `c_h`, the sum of the scalars an attestation of exactly that head
//! reveals. With ONE content key shared by the members (D53) every member
//! can compute `c_h` in advance, so the lock also names its payee: the
//! adaptor point is `T = C_h + P_{i,s}`, the intended proposer's per-slot
//! point, and its secret `t = c_h + p_{i,s}` — only member `i` can
//! complete it, and completing it is member `i`'s statement that it
//! sealed slot `s` with head `h` (a claim with no such block on the venue
//! names `i`). The sealed block carries `p_{i,s}`, so
//! [`lock_secret`] is the attestation's scalar sum plus it.

use bitcoin::key::Parity;
use bitcoin::secp256k1::{PublicKey, Scalar, SecretKey, SECP256K1};
use bitcoin::Amount;
use lngap_channel::{FeeLock, Role};
use lngap_ec_wots::{Attester, EpochTable};
use lngap_factchain::HEAD_BYTES;

use crate::refute::{HEAD_CHUNK_START, HEAD_CHUNKS};
use crate::roster::Registry;
use crate::SealedBlock;

/// The head's chunk positions within the header.
pub fn head_chunks() -> std::ops::Range<usize> {
    HEAD_CHUNK_START..HEAD_CHUNK_START + HEAD_CHUNKS
}

/// The content sum `C_h` of `head` under `table`: the sum of the
/// anticipation points the head selects over the head chunks.
pub fn content_point(table: &EpochTable, head: &[u8; HEAD_BYTES]) -> PublicKey {
    table.point_sum(head, head_chunks())
}

/// The content secret `c_h` a sealed block reveals: the sum of its
/// attestation's scalars over the head chunks — the log of
/// [`content_point`] of ITS head.
pub fn content_secret(block: &SealedBlock) -> SecretKey {
    block.attestation.scalar_sum(head_chunks())
}

/// `c_h` computed from the shared content key without sealing anything
/// (what any member can do under D53 — the rogue fee claim's material).
pub fn content_secret_of(content: &Attester, slot: u32, head: &[u8; HEAD_BYTES]) -> SecretKey {
    let mut acc: Option<SecretKey> = None;
    for (k, j) in head_chunks().enumerate() {
        let s = content.chunk_secret(u64::from(slot), j, lngap_ec_wots::chunk_value(head, k));
        acc = Some(match acc {
            None => s,
            Some(a) => a.add_tweak(&Scalar::from_be_bytes(s.secret_bytes()).expect("in range")).expect("nonzero"),
        });
    }
    acc.expect("head chunks")
}

/// The lock point `T = C_h + P_{i,s}`: the head's content sum under
/// `registry`'s table for `slot` plus member `i`'s proposer point.
pub fn lock_point(registry: &Registry, slot: u32, head: &[u8; HEAD_BYTES], member: usize) -> PublicKey {
    let p = PublicKey::from_x_only_public_key(registry.proposers(slot)[member], Parity::Even);
    content_point(registry.table(slot), head).combine(&p).expect("not the identity")
}

/// The lock secret `t = c_h + p_{i,s}` a sealed block reveals: its
/// attestation's scalar sum plus its proposer's revealed scalar.
pub fn lock_secret(block: &SealedBlock) -> SecretKey {
    content_secret(block).add_tweak(&Scalar::from_be_bytes(block.proposer_secret.secret_bytes()).expect("in range")).expect("nonzero")
}

/// A fee lock of `value` from `payer` to the counterparty — member
/// `member`'s node, the intended proposer — for the attestation of
/// `head` at `slot`, refundable from `expiry`.
#[allow(clippy::too_many_arguments)]
pub fn fee_lock(id: u32, payer: Role, value: Amount, registry: &Registry, slot: u32, head: &[u8; HEAD_BYTES], member: usize, expiry: u32) -> FeeLock {
    FeeLock {
        id,
        payer,
        value,
        lock: lock_point(registry, slot, head, member),
        expiry,
        memo: format!("head {} at slot {slot}, sealed by member {member}", hex::encode(&head[..8])),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{genesis, Member, PosMiner};
    use lngap_factchain::entry_head;

    /// The sealed block's scalar sum plus its proposer reveal opens the
    /// lock of ITS head to ITS proposer, and only that.
    #[test]
    fn attestation_by_the_named_member_opens_the_lock() {
        const CONTENT: [u8; 32] = [0x39; 32];
        let members: Vec<Member> = (0..5u8).map(|i| Member::new([0x40 + i; 32])).collect();
        let (gen, _) = genesis(&Attester::new(CONTENT), &members[0], 0);
        let mut miner = PosMiner::new(CONTENT, members, gen.header.digest(), 0);
        let registry = miner.registry(8).unwrap();
        let entry = b"the mover's entry at slot 3".to_vec();
        let head = entry_head(&entry);
        // the mover pays member 3's node
        let lock = fee_lock(7, Role::User, Amount::from_sat(5_000), &registry, 3, &head, 3, 100);
        miner.seal_next(1).unwrap();
        miner.seal_next(2).unwrap();
        miner.submit(entry.clone());
        let (block, table) = miner.seal_by(3, 3).unwrap();
        assert_eq!(&table, registry.table(3));
        let t = lock_secret(&block);
        assert!(lock.opens(&t), "member 3's attestation of exactly this head opens the lock");
        assert_eq!(PublicKey::from_secret_key(SECP256K1, &t), lock_point(&registry, 3, &head, 3));
        // the content secret alone (any member can compute it) does not
        assert!(!lock.opens(&content_secret(&block)));
        assert_eq!(content_secret_of(miner.content(), 3, &head), content_secret(&block), "the shared key computes c_h without sealing");
        // another member sealing the same head: the same content secret,
        // ITS proposer scalar — a different lock
        let other = SealedBlock { proposer: 1, proposer_secret: miner.proposer_secret(1, 3), ..block };
        assert!(!lock.opens(&lock_secret(&other)));
        assert!(fee_lock(8, Role::User, Amount::from_sat(1), &registry, 3, &head, 1, 100).opens(&lock_secret(&other)));
        // a different head by member 3: a different content secret
        let entry_b = b"a different entry".to_vec();
        let header = lngap_factchain::Header::new(&other.header.prev(), &lngap_factchain::entry_root(&entry_b), &entry_head(&entry_b), 3);
        let attestation = miner.content().attest(&table, header.as_bytes());
        let block_b = SealedBlock { header, entry: entry_b, attestation, proposer: 3, proposer_secret: miner.proposer_secret(3, 3) };
        assert!(!lock.opens(&lock_secret(&block_b)));
    }
}
