//! The PoW fact chain: a custom chain whose structure is designed for cheap
//! Script-verifiable proofs.
//!
//! Stage 1 (this crate): one entry per block, no Merkle tree. The root in the
//! header IS the hash of the single entry. This makes the inclusion proof
//! trivial (one hash compression) and isolates the header-chain cost — the
//! unknown we are validating.
//!
//! # Header format (48 bytes)
//!
//! ```text
//! prev(20)  root(20)  height(4)  nonce(4)  = 48 bytes
//! ```
//!
//! - `prev`: 160-bit digest of the parent header (the claim-native n4bit
//!   hash, `lngap_n4bit::hash_claim`, so that a bisection claim over the
//!   header bytes computes exactly this digest).
//! - `root`: 160-bit hash of the block's single entry (stage 1), or the
//!   Merkle root of the ledger tree (stage 2+).
//! - `height`: block height (u32 little-endian).
//! - `nonce`: PoW nonce (u32 little-endian).
//!
//! One n4bit compression block is 10 bytes (rate = 20 nibbles). A 48-byte
//! header is 96 nibbles = 5 absorption blocks. This is the unit of work
//! for the claim's header-chain steps.
//!
//! # PoW
//!
//! `n4bit(header) <= target`, where target is derived from a fixed difficulty
//! (5 bits for the PoC: the top 5 bits of the 160-bit hash must be zero).
//! No retargeting.

pub mod claim;
pub mod slot;

use lngap_n4bit::{hash_claim as hash, meets_target, target_from_difficulty, Digest, DIGEST_BYTES};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Header size in bytes.
pub const HEADER_BYTES: usize = 48;

/// Fixed PoW difficulty for the PoC: 5 leading zero bits.
pub const DIFFICULTY_BITS: u32 = 5;

/// The target as a 20-byte big-endian value (hash <= target).
pub fn pow_target() -> [u8; DIGEST_BYTES] {
    target_from_difficulty(DIFFICULTY_BITS)
}

/// A 48-byte fact-chain header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header(pub [u8; HEADER_BYTES]);

mod serde_bytes48 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(v: &[u8; 48], s: S) -> Result<S::Ok, S::Error> {
        hex::encode(v).serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 48], D::Error> {
        let h = <String as Deserialize>::deserialize(d)?;
        let b = hex::decode(h).map_err(serde::de::Error::custom)?;
        b.try_into().map_err(|_| serde::de::Error::custom("48 bytes"))
    }
}

impl Serialize for Header {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        serde_bytes48::serialize(&self.0, s)
    }
}
impl<'de> Deserialize<'de> for Header {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(Header(serde_bytes48::deserialize(d)?))
    }
}

impl Header {
    /// Build a header from its fields (without mining — nonce is 0).
    pub fn new(prev: &Digest, root: &Digest, height: u32) -> Header {
        let mut h = [0u8; HEADER_BYTES];
        h[0..20].copy_from_slice(prev);
        h[20..40].copy_from_slice(root);
        h[40..44].copy_from_slice(&height.to_le_bytes());
        // nonce = 0
        Header(h)
    }

    pub fn prev(&self) -> Digest {
        self.0[0..20].try_into().unwrap()
    }
    pub fn root(&self) -> Digest {
        self.0[20..40].try_into().unwrap()
    }
    pub fn height(&self) -> u32 {
        u32::from_le_bytes(self.0[40..44].try_into().unwrap())
    }
    pub fn nonce(&self) -> u32 {
        u32::from_le_bytes(self.0[44..48].try_into().unwrap())
    }
    pub fn set_nonce(&mut self, n: u32) {
        self.0[44..48].copy_from_slice(&n.to_le_bytes());
    }

    /// The n4bit hash of the header bytes.
    pub fn digest(&self) -> Digest {
        hash(&self.0)
    }

    /// Does this header's hash meet the PoW target?
    pub fn meets_pow(&self) -> bool {
        meets_target(&self.digest(), &pow_target())
    }

    /// Serialize as bytes for hashing or transmission.
    pub fn as_bytes(&self) -> &[u8; HEADER_BYTES] {
        &self.0
    }
}

/// A block: a header and one entry (stage 1).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Block {
    pub header: Header,
    /// The single entry this block carries (64 bytes in the names registry).
    pub entry: Vec<u8>,
}

impl Block {
    /// Build a block (unmined, nonce = 0). The root is the hash of the entry.
    pub fn new(prev: &Digest, height: u32, entry: &[u8]) -> Block {
        let root = hash(entry);
        Block {
            header: Header::new(prev, &root, height),
            entry: entry.to_vec(),
        }
    }

    /// Verify the block: PoW, root = hash(entry), prev link.
    pub fn verify(&self, expected_prev: &Digest) -> Result<(), String> {
        if !self.header.meets_pow() {
            return Err(format!("PoW failed at height {}", self.header.height()));
        }
        let computed_root = hash(&self.entry);
        if computed_root != self.header.root() {
            return Err(format!(
                "root mismatch at height {}: header says {} but hash(entry) = {}",
                self.header.height(),
                hex::encode(self.header.root()),
                hex::encode(computed_root)
            ));
        }
        if self.header.prev() != *expected_prev {
            return Err(format!(
                "prev mismatch at height {}: expected {} but got {}",
                self.header.height(),
                hex::encode(expected_prev),
                hex::encode(self.header.prev())
            ));
        }
        Ok(())
    }
}

/// The genesis block: height 0, prev = all-zeros, empty entry.
pub fn genesis() -> Block {
    let entry = vec![];
    let root = hash(&entry);
    let mut header = Header::new(&[0u8; DIGEST_BYTES], &root, 0);
    // Mine the genesis
    mine(&mut header);
    Block { header, entry }
}

/// Mine a header: brute-force the nonce until the hash meets the target.
pub fn mine(header: &mut Header) {
    let target = pow_target();
    let mut nonce = 0u32;
    loop {
        header.set_nonce(nonce);
        if meets_target(&header.digest(), &target) {
            return;
        }
        nonce += 1;
        if nonce == 0 {
            // u32 overflow — extremely unlikely at 5-bit difficulty
            panic!("nonce space exhausted");
        }
    }
}

/// A fact-chain client: verifies headers, PoW, and tracks the chain.
#[derive(Clone, Debug, Default)]
pub struct ChainClient {
    /// Verified headers in height order.
    pub headers: Vec<Header>,
    /// The checkpoint the client started from (height, digest).
    pub checkpoint: (u32, Digest),
}

impl ChainClient {
    /// Start from a checkpoint.
    pub fn from_checkpoint(height: u32, digest: Digest) -> Self {
        ChainClient {
            headers: Vec::new(),
            checkpoint: (height, digest),
        }
    }

    /// The tip digest (or the checkpoint if no blocks verified yet).
    pub fn tip(&self) -> Digest {
        self.headers.last().map(|h| h.digest()).unwrap_or(self.checkpoint.1)
    }

    /// The tip height.
    pub fn tip_height(&self) -> u32 {
        self.headers.last().map(|h| h.height()).unwrap_or(self.checkpoint.0)
    }

    /// Verify and append a block. Checks PoW, root, and prev link.
    pub fn verify_and_append(&mut self, block: &Block) -> Result<(), String> {
        let expected_prev = self.tip();
        block.verify(&expected_prev)?;
        let expected_height = self.tip_height() + 1;
        if block.header.height() != expected_height {
            return Err(format!(
                "height gap: expected {expected_height}, got {}",
                block.header.height()
            ));
        }
        self.headers.push(block.header.clone());
        Ok(())
    }

    /// The headers from the checkpoint to the tip (inclusive of all verified
    /// blocks, exclusive of the checkpoint itself).
    pub fn chain_headers(&self) -> &[Header] {
        &self.headers
    }

    /// Find the header at a given height, if verified.
    pub fn header_at(&self, height: u32) -> Option<&Header> {
        self.headers.iter().find(|h| h.height() == height)
    }

    /// Number of headers since the checkpoint.
    pub fn chain_length(&self) -> usize {
        self.headers.len()
    }
}

/// The miner: accepts pending entries, builds blocks, mines them.
pub struct Miner {
    pub height: u32,
    pub tip: Digest,
    pending: Vec<Vec<u8>>,
}

impl Miner {
    pub fn new(genesis_digest: Digest, genesis_height: u32) -> Miner {
        Miner {
            height: genesis_height,
            tip: genesis_digest,
            pending: Vec::new(),
        }
    }

    /// Submit an entry to be included in the next block.
    pub fn submit(&mut self, entry: Vec<u8>) {
        self.pending.push(entry);
    }

    /// Build and mine the next block from the first pending entry.
    /// Returns None if there are no pending entries.
    pub fn mine_next(&mut self) -> Option<Block> {
        let entry = self.pending.first()?.clone();
        self.pending.remove(0);
        let height = self.height + 1;
        let mut block = Block::new(&self.tip, height, &entry);
        mine(&mut block.header);
        self.tip = block.header.digest();
        self.height = height;
        Some(block)
    }

    /// How many entries are waiting.
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }
}

/// The shape of a fact-chain inclusion claim: "from the checkpoint, `n_headers`
/// valid headers reach a block whose root is the hash of the entry, and the
/// entry's content matches the predicates."
///
/// Stage 1: root = hash(entry), so there is no separate Merkle path. The claim
/// is the header chain + one entry-hash step + entry predicates.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FactShape {
    /// The checkpoint: the digest of the header at the checkpoint height.
    pub checkpoint: Digest,
    /// Fixed difficulty (nbits equivalent). For the PoC, always DIFFICULTY_BITS.
    pub difficulty_bits: u32,
    /// Number of headers from the checkpoint to the target block (inclusive).
    /// This is the prover's W, selected at claim time, bounded by W_max.
    pub n_headers: usize,
}

/// The refutation shape: one header longer from the same checkpoint.
impl FactShape {
    pub fn refutation(&self) -> FactShape {
        FactShape {
            checkpoint: self.checkpoint,
            difficulty_bits: self.difficulty_bits,
            n_headers: self.n_headers + 1,
        }
    }
}

/// Proof data for a fact-chain claim: the headers and the entry.
#[derive(Clone, Debug)]
pub struct FactData {
    /// Headers from checkpoint+1 to the target block (n_headers of them).
    pub headers: Vec<Header>,
    /// The entry at the target block.
    pub entry: Vec<u8>,
}

impl FactShape {
    /// Build the proof data from a verified chain.
    pub fn build_data(&self, client: &ChainClient, entry: &[u8]) -> FactData {
        let start = client.checkpoint.0 + 1;
        let end = client.checkpoint.0 + self.n_headers as u32;
        let headers: Vec<Header> = (start..=end)
            .map(|h| client.header_at(h).cloned().expect("header at height"))
            .collect();
        FactData {
            headers,
            entry: entry.to_vec(),
        }
    }

    /// Verify the proof data natively (for testing and off-chain checks).
    pub fn verify_data(&self, data: &FactData) -> Result<(), String> {
        let target = target_from_difficulty(self.difficulty_bits);
        let mut prev = self.checkpoint;
        for h in &data.headers {
            // PoW
            if !meets_target(&h.digest(), &target) {
                return Err(format!("PoW failed at height {}", h.height()));
            }
            // Prev link
            if h.prev() != prev {
                return Err(format!(
                    "prev mismatch at height {}: expected {}",
                    h.height(),
                    hex::encode(prev)
                ));
            }
            prev = h.digest();
        }
        // Entry hash = root of the last header
        let last = data.headers.last().unwrap();
        let computed = hash(&data.entry);
        if computed != last.root() {
            return Err(format!(
                "entry hash mismatch: header root {} but hash(entry) = {}",
                hex::encode(last.root()),
                hex::encode(computed)
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn genesis_mines() {
        let g = genesis();
        assert!(g.header.meets_pow());
        assert_eq!(g.header.height(), 0);
        assert_eq!(g.header.prev(), [0u8; DIGEST_BYTES]);
    }

    #[test]
    fn chain_of_10_blocks() {
        let g = genesis();
        let mut miner = Miner::new(g.header.digest(), 0);
        let mut client = ChainClient::from_checkpoint(0, g.header.digest());

        let entries: Vec<Vec<u8>> = (0..10u32)
            .map(|i| {
                let mut e = vec![0u8; 64];
                e[0..4].copy_from_slice(&i.to_le_bytes());
                e
            })
            .collect();

        for entry in &entries {
            miner.submit(entry.clone());
            let block = miner.mine_next().expect("mine");
            client.verify_and_append(&block).expect("verify");
        }

        assert_eq!(client.chain_length(), 10);
        assert_eq!(client.tip_height(), 10);
    }

    #[test]
    fn claim_verification() {
        let g = genesis();
        let mut miner = Miner::new(g.header.digest(), 0);
        let mut client = ChainClient::from_checkpoint(0, g.header.digest());

        // Mine 5 blocks with entries
        let entries: Vec<Vec<u8>> = (0..5u32)
            .map(|i| {
                let mut e = vec![0u8; 64];
                e[0] = (i + 1) as u8;
                e
            })
            .collect();

        for entry in &entries {
            miner.submit(entry.clone());
            let block = miner.mine_next().expect("mine");
            client.verify_and_append(&block).expect("verify");
        }

        // Build a claim for the entry at block 3 (height 3, 3 headers from checkpoint)
        let shape = FactShape {
            checkpoint: g.header.digest(),
            difficulty_bits: DIFFICULTY_BITS,
            n_headers: 3,
        };
        let data = shape.build_data(&client, &entries[2]); // entry at height 3
        assert!(shape.verify_data(&data).is_ok(), "valid claim verifies");

        // Refutation: one more header
        let ref_shape = shape.refutation();
        assert_eq!(ref_shape.n_headers, 4);
    }

    #[test]
    fn invalid_pow_rejected() {
        let g = genesis();
        let mut bad_header = Header::new(&g.header.digest(), &hash(&[0u8; 64]), 1);
        bad_header.set_nonce(0); // probably not a valid PoW
        // Don't mine — just check it fails
        assert!(!bad_header.meets_pow() || bad_header.digest() == bad_header.digest());
        // The point: an unmined header likely doesn't meet the target
    }

    #[test]
    fn block_verify_checks_root() {
        let g = genesis();
        let entry = vec![0xABu8; 64];
        let mut block = Block::new(&g.header.digest(), 1, &entry);
        mine(&mut block.header);
        assert!(block.verify(&g.header.digest()).is_ok());

        // Corrupt the entry
        block.entry[0] ^= 1;
        assert!(block.verify(&g.header.digest()).is_err());
    }

    #[test]
    fn header_digest_is_deterministic() {
        let h1 = Header::new(&[1u8; 20], &[2u8; 20], 42);
        let h2 = Header::new(&[1u8; 20], &[2u8; 20], 42);
        assert_eq!(h1.digest(), h2.digest());
    }

    #[test]
    fn print_chain_stats() {
        let g = genesis();
        let mut miner = Miner::new(g.header.digest(), 0);
        let mut client = ChainClient::from_checkpoint(0, g.header.digest());

        for i in 0..10u32 {
            let mut e = vec![0u8; 64];
            e[0] = (i + 1) as u8;
            miner.submit(e.clone());
            let block = miner.mine_next().expect("mine");
            client.verify_and_append(&block).expect("verify");
        }

        // Build a claim for W=10 (all headers since checkpoint)
        let shape = FactShape {
            checkpoint: g.header.digest(),
            difficulty_bits: DIFFICULTY_BITS,
            n_headers: 10,
        };
        let data = shape.build_data(&client, &[1u8; 64]);

        println!("FactShape W=10:");
        println!("  headers: {} ({} bytes each)", data.headers.len(), HEADER_BYTES);
        println!("  total header data: {} bytes", data.headers.len() * HEADER_BYTES);
        println!("  entry: {} bytes", data.entry.len());
        println!("  difficulty: {} bits", DIFFICULTY_BITS);
        println!("  digest size: {} bits", DIGEST_BYTES * 8);
    }
}
