//! The PoS venue chain: the fact chain's 96-byte header sealed by an EC-OTS
//! attestation instead of proof of work.
//!
//! Design: docs/DECISIONS.md D32 and
//! docs/planning/hermes-research/POS_FACTCHAIN_PLAN.md. The header is
//! byte-identical to the PoW chain's (`prev(20) root(20) head(48) height(4)
//! pad(4)`); the `height` field carries the SLOT (epoch = slot). The seal is
//! an attestation over all [`HEADER_CHUNKS`] chunks of the header under the
//! slot's epoch table, produced by a single attester key standing in for the
//! FROST group key. The per-chunk statements let a later dispute read out any
//! subset of the header (the head for a stall refutation, the root for an
//! entry exhibit) without a separate attestation form.
//!
//! The chain runs a CONSTANT CADENCE by default: one block per slot, empty
//! if no entry is pending (various venue-level reasons may prefer or even
//! require this — liveness, ordering for non-game apps). But density is a
//! default, not a validity rule: clients accept any strictly increasing
//! slot sequence, and the dispute layer never depends on it — a "Bob did
//! not publish in the window" claim is enforced by the challenge window
//! itself: a refutation that does not exist cannot be exhibited. (Density
//! WAS a hard requirement of the D28 PoW stall claim's fixed-position
//! header scan; the thin PoS claim drops that, and gaps are a liveness
//! event, not a validity failure.)

use lngap_ec_wots::{Attestation, Attester, EpochTable};
use lngap_factchain::{entry_head, entry_root, Header, HEADER_BYTES, HEAD_BYTES};
use lngap_n4bit::{Digest, DIGEST_BYTES};

pub mod bond;
pub mod chess;
pub mod graph;
pub mod refute;
pub mod instance;
pub mod ttt;

/// Attested chunks per header: one per nibble (96 bytes = 192 chunks).
pub const HEADER_CHUNKS: usize = HEADER_BYTES * 2;

/// A block sealed by the venue's attestation over the header bytes.
pub struct SealedBlock {
    pub header: Header,
    /// The single entry this block carries (stage 1).
    pub entry: Vec<u8>,
    /// One revealed scalar per header chunk, under the slot's epoch table.
    pub attestation: Attestation,
}

impl SealedBlock {
    /// The positional checks: head = entry's head, root = entry's root,
    /// prev link. Shared with the PoW chain minus the target.
    pub fn verify_structure(&self, expected_prev: &Digest) -> Result<(), String> {
        self.verify_content()?;
        if self.header.prev() != *expected_prev {
            return Err(format!(
                "prev mismatch at slot {}: expected {} but got {}",
                self.header.height(),
                hex::encode(expected_prev),
                hex::encode(self.header.prev())
            ));
        }
        Ok(())
    }

    /// The position-free checks: head = entry's head, root = entry's root.
    pub fn verify_content(&self) -> Result<(), String> {
        if self.header.head() != entry_head(&self.entry) {
            return Err(format!("head mismatch at slot {}", self.header.height()));
        }
        let computed_root = entry_root(&self.entry);
        if computed_root != self.header.root() {
            return Err(format!(
                "root mismatch at slot {}: header says {} but hash(entry) = {}",
                self.header.height(),
                hex::encode(self.header.root()),
                hex::encode(computed_root)
            ));
        }
        Ok(())
    }

    /// The seal: the attestation opens every chunk of the header under the
    /// slot's table (the table's epoch must be the slot).
    pub fn verify_seal(&self, table: &EpochTable) -> Result<(), String> {
        if table.index != self.header.height() as u64 {
            return Err(format!(
                "table epoch {} is not slot {}",
                table.index,
                self.header.height()
            ));
        }
        if table.chunks != HEADER_CHUNKS {
            return Err(format!(
                "table has {} chunks, the header has {HEADER_CHUNKS}",
                table.chunks
            ));
        }
        if !self.attestation.verify(table, self.header.as_bytes()) {
            return Err(format!(
                "attestation does not open the header at slot {}",
                self.header.height()
            ));
        }
        Ok(())
    }
}

/// The genesis block: slot 0, prev = all-zeros, empty entry, attested at
/// epoch 0. Returns the block and its epoch table (registry data).
pub fn genesis(attester: &Attester) -> (SealedBlock, EpochTable) {
    let entry = vec![];
    let header = Header::new(
        &[0u8; DIGEST_BYTES],
        &entry_root(&entry),
        &[0u8; HEAD_BYTES],
        0,
    );
    let table = attester.epoch_table(0, HEADER_CHUNKS);
    let attestation = attester.attest(&table, header.as_bytes());
    (
        SealedBlock {
            header,
            entry,
            attestation,
        },
        table,
    )
}

/// The sealer: accepts pending entries, builds blocks, attests them. One
/// block per slot on a constant cadence — empty blocks seal empty slots
/// (see the crate docs: cadence is the default, not a validity rule).
pub struct PosMiner {
    attester: Attester,
    /// The slot of the last sealed block.
    pub height: u32,
    pub tip: Digest,
    pending: Vec<Vec<u8>>,
}

impl PosMiner {
    pub fn new(seed: [u8; 32], genesis_digest: Digest, genesis_height: u32) -> PosMiner {
        PosMiner {
            attester: Attester::new(seed),
            height: genesis_height,
            tip: genesis_digest,
            pending: Vec::new(),
        }
    }

    /// The fixed-R nonce-discipline variant (D38): one nonce per (slot,
    /// chunk), so an equivocation leaks the group key — the bond's burn
    /// path (`bond.rs`) is keyed to it.
    pub fn new_fixed_r(seed: [u8; 32], genesis_digest: Digest, genesis_height: u32) -> PosMiner {
        PosMiner {
            attester: Attester::new_fixed_r(seed),
            height: genesis_height,
            tip: genesis_digest,
            pending: Vec::new(),
        }
    }

    pub fn attester(&self) -> &Attester {
        &self.attester
    }

    /// Submit an entry to be included in the next sealed block.
    pub fn submit(&mut self, entry: Vec<u8>) {
        self.pending.push(entry);
    }

    /// How many entries are waiting.
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Seal the block at `slot`: the first pending entry, or an empty block
    /// (the cadence default). Returns the block and its epoch table
    /// (registry data the venue publishes alongside). `slot` must follow
    /// the last sealed slot.
    pub fn seal_next(&mut self, slot: u32) -> Result<(SealedBlock, EpochTable), String> {
        if slot <= self.height {
            return Err(format!(
                "slot {slot} does not follow the tip slot {}",
                self.height
            ));
        }
        let entry = if self.pending.is_empty() {
            Vec::new()
        } else {
            self.pending.remove(0)
        };
        let header = Header::new(&self.tip, &entry_root(&entry), &entry_head(&entry), slot);
        let table = self.attester.epoch_table(slot as u64, HEADER_CHUNKS);
        let attestation = self.attester.attest(&table, header.as_bytes());
        self.tip = header.digest();
        self.height = slot;
        Ok((
            SealedBlock {
                header,
                entry,
                attestation,
            },
            table,
        ))
    }
}

/// What an observed sealed block turned out to be.
#[derive(Debug, PartialEq, Eq)]
pub enum Observation {
    /// Extends the verified tip (or the checkpoint).
    ExtendsTip,
    /// Already held: the same header at that slot.
    Known,
    /// A second, DIFFERENT attested header at a slot we already hold: the
    /// attester equivocated. Both headers open under the same epoch table,
    /// which is the clean on-chain slash case (`lngap_ec_wots::slash_leaf`).
    Equivocation(Equivocation),
    /// The block continues a held non-tip header while we hold a different
    /// continuation: a chain-level fork. Distinct from same-slot
    /// equivocation (the two successors have different slots); slash-relevant
    /// through the venue's fork-choice rule rather than the per-epoch leaf.
    Fork(Fork),
}

/// Two conflicting attested headers at one slot.
#[derive(Debug, PartialEq, Eq)]
pub struct Equivocation {
    pub slot: u32,
    /// The header the client already held.
    pub first: Header,
    /// The newly observed conflicting header.
    pub second: Header,
}

/// Two attested continuations of one parent: the held one and the new one.
#[derive(Debug, PartialEq, Eq)]
pub struct Fork {
    pub parent_slot: u32,
    /// The continuation the client already holds.
    pub first: Header,
    /// The newly observed conflicting continuation.
    pub second: Header,
}

/// A PoS venue client: verifies structure and seals, tracks the chain.
#[derive(Clone, Debug, Default)]
pub struct PosClient {
    /// Verified headers in slot order.
    pub headers: Vec<Header>,
    /// The checkpoint the client started from (slot, digest).
    pub checkpoint: (u32, Digest),
}

impl PosClient {
    /// Start from a checkpoint.
    pub fn from_checkpoint(slot: u32, digest: Digest) -> Self {
        PosClient {
            headers: Vec::new(),
            checkpoint: (slot, digest),
        }
    }

    /// The tip digest (or the checkpoint if no blocks verified yet).
    pub fn tip(&self) -> Digest {
        self.headers
            .last()
            .map(|h| h.digest())
            .unwrap_or(self.checkpoint.1)
    }

    /// The tip slot.
    pub fn tip_height(&self) -> u32 {
        self.headers
            .last()
            .map(|h| h.height())
            .unwrap_or(self.checkpoint.0)
    }

    /// Find the header at a given slot, if verified.
    pub fn header_at(&self, slot: u32) -> Option<&Header> {
        self.headers.iter().find(|h| h.height() == slot)
    }

    /// Number of headers since the checkpoint.
    pub fn chain_length(&self) -> usize {
        self.headers.len()
    }

    /// The headers from the checkpoint to the tip.
    pub fn chain_headers(&self) -> &[Header] {
        &self.headers
    }

    /// Verify and append a block extending the tip: structure, seal, and a
    /// strictly increasing slot.
    pub fn verify_and_append(
        &mut self,
        block: &SealedBlock,
        table: &EpochTable,
    ) -> Result<(), String> {
        let expected_prev = self.tip();
        block.verify_structure(&expected_prev)?;
        block.verify_seal(table)?;
        if block.header.height() <= self.tip_height() {
            return Err(format!(
                "slot {} does not follow the tip slot {}",
                block.header.height(),
                self.tip_height()
            ));
        }
        self.headers.push(block.header.clone());
        Ok(())
    }

    /// Observe a sealed block that names its own parent — possibly a fork.
    /// The parent is found BY the prev link: a held header, or the
    /// checkpoint. The result says whether the block extends the tip, is
    /// already known, equivocates at a held slot, or forks a held parent.
    pub fn observe(&self, block: &SealedBlock, table: &EpochTable) -> Result<Observation, String> {
        let slot = block.header.height();
        let parent_slot = if block.header.prev() == self.checkpoint.1 {
            self.checkpoint.0
        } else {
            match self
                .headers
                .iter()
                .find(|h| h.digest() == block.header.prev())
            {
                Some(p) => p.height(),
                None => return Err(format!("unknown parent for slot {slot}")),
            }
        };
        if slot <= parent_slot {
            return Err(format!(
                "slot {slot} does not follow its parent slot {parent_slot}"
            ));
        }
        block.verify_content()?;
        block.verify_seal(table)?;
        if let Some(held) = self.header_at(slot) {
            return if held.digest() == block.header.digest() {
                Ok(Observation::Known)
            } else {
                Ok(Observation::Equivocation(Equivocation {
                    slot,
                    first: held.clone(),
                    second: block.header.clone(),
                }))
            };
        }
        if block.header.prev() == self.tip() {
            return Ok(Observation::ExtendsTip);
        }
        // The parent is held but the block enters history behind the tip:
        // the held chain continues the parent with a different block.
        let held_successor = self
            .headers
            .iter()
            .find(|h| h.prev() == block.header.prev())
            .expect("the held parent has a held successor")
            .clone();
        Ok(Observation::Fork(Fork {
            parent_slot,
            first: held_successor,
            second: block.header.clone(),
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEED: [u8; 32] = [7u8; 32];

    /// A running start: genesis sealed, a miner and a client checkpointed on
    /// it (the ChainClient idiom: the checkpoint is not itself a held header).
    fn boot() -> (PosMiner, PosClient) {
        let attester = Attester::new(SEED);
        let (gen, _table0) = genesis(&attester);
        let client = PosClient::from_checkpoint(0, gen.header.digest());
        let miner = PosMiner::new(SEED, gen.header.digest(), 0);
        (miner, client)
    }

    #[test]
    fn genesis_verifies() {
        let attester = Attester::new(SEED);
        let (gen, table0) = genesis(&attester);
        gen.verify_structure(&[0u8; DIGEST_BYTES]).unwrap();
        gen.verify_seal(&table0).unwrap();
        assert_eq!(gen.header.height(), 0);
        assert_eq!(gen.header.head(), [0u8; HEAD_BYTES]);
    }

    #[test]
    fn cadence_seals_empty_slots() {
        let (mut miner, mut client) = boot();
        // Nothing pending: the slot still gets its (empty) block.
        let (b1, t1) = miner.seal_next(1).unwrap();
        assert!(b1.entry.is_empty());
        assert_eq!(b1.header.head(), [0u8; HEAD_BYTES]);
        client.verify_and_append(&b1, &t1).unwrap();
    }

    #[test]
    fn chain_verifies_with_gaps() {
        let (mut miner, mut client) = boot();
        miner.submit(b"move at slot 1".to_vec());
        miner.submit(b"move at slot 3".to_vec());
        miner.submit(b"move at slot 7".to_vec());
        let (b1, t1) = miner.seal_next(1).unwrap();
        let (b3, t3) = miner.seal_next(3).unwrap();
        let (b7, t7) = miner.seal_next(7).unwrap();
        // Gaps are legal to the client: validity is strictly-increasing
        // slots, not density (cadence is the sealer's default, not a rule).
        client.verify_and_append(&b1, &t1).unwrap();
        client.verify_and_append(&b3, &t3).unwrap();
        client.verify_and_append(&b7, &t7).unwrap();
        assert_eq!(client.tip_height(), 7);
        assert_eq!(client.chain_length(), 3);
        assert_ne!(client.header_at(1).unwrap().head(), [0u8; HEAD_BYTES]);
        assert!(client.header_at(2).is_none());
    }

    #[test]
    fn non_increasing_slot_rejected() {
        let (mut miner, mut client) = boot();
        miner.submit(b"a".to_vec());
        miner.submit(b"b".to_vec());
        let (b3, t3) = miner.seal_next(3).unwrap();
        // Miner-side: the next seal must follow slot 3.
        assert!(miner.seal_next(3).is_err());
        assert!(miner.seal_next(2).is_err());
        // Client-side: a block at a held-or-earlier slot does not append.
        client.verify_and_append(&b3, &t3).unwrap();
        assert!(client.verify_and_append(&b3, &t3).is_err());
    }

    #[test]
    fn seal_rejects_tampered_header() {
        let (mut miner, client) = boot();
        miner.submit(b"x".to_vec());
        let (mut block, table) = miner.seal_next(1).unwrap();
        // Flip a byte in the pad field (the old nonce): the structural
        // checks do not read it, so only the seal can catch this.
        block.header.0[95] ^= 1;
        block
            .verify_structure(&client.tip())
            .expect("structure passes");
        assert!(block.verify_seal(&table).is_err());
    }

    #[test]
    fn seal_rejects_wrong_epoch_table() {
        let (mut miner, _client) = boot();
        miner.submit(b"x".to_vec());
        let (block, _table) = miner.seal_next(1).unwrap();
        let wrong = miner.attester().epoch_table(99, HEADER_CHUNKS);
        assert!(block.verify_seal(&wrong).is_err());
    }

    #[test]
    fn structure_rejects_tampered_entry() {
        let (mut miner, client) = boot();
        miner.submit(b"some move".to_vec());
        let (mut block, _table) = miner.seal_next(1).unwrap();
        block.entry[0] ^= 1;
        assert!(block.verify_structure(&client.tip()).is_err());
    }

    #[test]
    fn equivocation_is_detected() {
        let (mut miner, mut client) = boot();
        miner.submit(b"move A".to_vec());
        let (block_a, table) = miner.seal_next(1).unwrap();
        client.verify_and_append(&block_a, &table).unwrap();

        // The attester equivocates: a second, different block at slot 1,
        // attested under the SAME epoch table.
        let prev = client.checkpoint.1;
        let entry_b = b"move B".to_vec();
        let header_b = Header::new(&prev, &entry_root(&entry_b), &entry_head(&entry_b), 1);
        let attestation_b = miner.attester().attest(&table, header_b.as_bytes());
        let block_b = SealedBlock {
            header: header_b,
            entry: entry_b,
            attestation: attestation_b,
        };
        // Both verify in isolation...
        block_b.verify_structure(&prev).unwrap();
        block_b.verify_seal(&table).unwrap();
        // ...and the client names the equivocation.
        match client.observe(&block_b, &table) {
            Ok(Observation::Equivocation(e)) => {
                assert_eq!(e.slot, 1);
                assert_eq!(e.first, block_a.header);
                assert_eq!(e.second, block_b.header);
            }
            other => panic!("expected equivocation, got {other:?}"),
        }
        // Re-observing the held block is just Known.
        assert_eq!(
            client.observe(&block_a, &table).unwrap(),
            Observation::Known
        );
    }

    #[test]
    fn fork_is_detected() {
        let (mut miner, mut client) = boot();
        miner.submit(b"move at 1".to_vec());
        miner.submit(b"move at 7".to_vec());
        let (b1, t1) = miner.seal_next(1).unwrap();
        let (b7, t7) = miner.seal_next(7).unwrap();
        client.verify_and_append(&b1, &t1).unwrap();
        client.verify_and_append(&b7, &t7).unwrap();

        // A block appears continuing slot 1 while we hold the slot-7
        // continuation: a fork, with no same-slot clash.
        let entry_c = b"fork move at 4".to_vec();
        let header_c = Header::new(
            &b1.header.digest(),
            &entry_root(&entry_c),
            &entry_head(&entry_c),
            4,
        );
        let table_c = miner.attester().epoch_table(4, HEADER_CHUNKS);
        let attestation_c = miner.attester().attest(&table_c, header_c.as_bytes());
        let block_c = SealedBlock {
            header: header_c,
            entry: entry_c,
            attestation: attestation_c,
        };
        block_c.verify_seal(&table_c).unwrap();
        match client.observe(&block_c, &table_c) {
            Ok(Observation::Fork(f)) => {
                assert_eq!(f.parent_slot, 1);
                assert_eq!(f.first, b7.header);
                assert_eq!(f.second, block_c.header);
            }
            other => panic!("expected fork, got {other:?}"),
        }
    }
}
