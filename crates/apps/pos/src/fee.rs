//! The fee lock's venue side (ATTESTATION_FEES.md; D49, D52): the point a
//! payer locks a fee to, and the secret the venue's attestation reveals.
//!
//! The head a mover will publish selects one anticipation point per head
//! chunk under the slot's table (the SCHEDULED member's, D51); their sum
//! `ΣP` is the adaptor point of the fee lock (`lngap_channel::FeeLock`),
//! and the sealed block's revealed scalars over the same chunks sum to its
//! discrete log — exactly when the member attested exactly that head at
//! exactly that slot. The payee is the slot's proposer (`registry.proposer`).

use bitcoin::secp256k1::{PublicKey, SecretKey};
use bitcoin::Amount;
use lngap_channel::{FeeLock, Role};
use lngap_ec_wots::EpochTable;
use lngap_factchain::HEAD_BYTES;

use crate::refute::{HEAD_CHUNK_START, HEAD_CHUNKS};
use crate::roster::Registry;
use crate::SealedBlock;

/// The head's chunk positions within the header.
pub fn head_chunks() -> std::ops::Range<usize> {
    HEAD_CHUNK_START..HEAD_CHUNK_START + HEAD_CHUNKS
}

/// The lock point of `head` under `table`: the sum of the anticipation
/// points the head selects over the head chunks.
pub fn lock_point(table: &EpochTable, head: &[u8; HEAD_BYTES]) -> PublicKey {
    table.point_sum(head, head_chunks())
}

/// The lock secret a sealed block reveals: the sum of its attestation's
/// scalars over the head chunks — the log of [`lock_point`] of ITS head.
pub fn lock_secret(block: &SealedBlock) -> SecretKey {
    block.attestation.scalar_sum(head_chunks())
}

/// A fee lock of `value` from `payer` to the counterparty (the proposer's
/// node) for the attestation of `head` at `slot`, refundable from
/// `expiry`.
pub fn fee_lock(id: u32, payer: Role, value: Amount, registry: &Registry, slot: u32, head: &[u8; HEAD_BYTES], expiry: u32) -> FeeLock {
    FeeLock {
        id,
        payer,
        value,
        lock: lock_point(registry.table(slot), head),
        expiry,
        memo: format!("head {} at slot {slot} (proposer: member {})", hex::encode(&head[..8]), registry.proposer(slot)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{genesis, Member, PosMiner};
    use bitcoin::secp256k1::SECP256K1;
    use lngap_factchain::entry_head;

    /// The sealed block's scalar sum opens the lock of ITS head under the
    /// scheduled member's table, and only that head's.
    #[test]
    fn attestation_opens_the_heads_lock() {
        let members: Vec<Member> = (0..5u8).map(|i| Member::new([0x40 + i; 32])).collect();
        let (gen, _) = genesis(&members[0].attester);
        let mut miner = PosMiner::new(members, gen.header.digest(), 0);
        let registry = miner.registry(8).unwrap();
        let entry = b"the mover's entry at slot 3".to_vec();
        let head = entry_head(&entry);
        let lock = fee_lock(7, Role::User, Amount::from_sat(5_000), &registry, 3, &head, 100);
        assert_eq!(registry.proposer(3), 3);
        // slots 1 and 2 seal empty; slot 3 seals the entry
        miner.seal_next(1).unwrap();
        miner.seal_next(2).unwrap();
        miner.submit(entry);
        let (block, table) = miner.seal_next(3).unwrap();
        assert_eq!(&table, registry.table(3));
        let t = lock_secret(&block);
        assert!(lock.opens(&t), "the attestation of exactly this head opens the lock");
        assert_eq!(PublicKey::from_secret_key(SECP256K1, &t), lock_point(registry.table(3), &head));
        // another head at the same slot (a second seal by hand under the same table)
        let other = b"a different entry".to_vec();
        let other_head = entry_head(&other);
        let header = lngap_factchain::Header::new(&block.header.prev(), &lngap_factchain::entry_root(&other), &other_head, 3);
        let attestation = miner.attester_at(3).attest(&table, header.as_bytes());
        let other_block = SealedBlock { header, entry: other, attestation };
        assert!(!lock.opens(&lock_secret(&other_block)), "a different head's scalars do not open it");
        // the same head at a different slot (another table) does not either
        let mut m2 = PosMiner::new((0..5u8).map(|i| Member::new([0x40 + i; 32])).collect(), gen.header.digest(), 0);
        m2.submit(b"the mover's entry at slot 3".to_vec());
        let (b1, _) = m2.seal_next(1).unwrap();
        assert_eq!(b1.header.head(), head);
        assert!(!lock.opens(&lock_secret(&b1)));
    }
}
