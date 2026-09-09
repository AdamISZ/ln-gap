//! Claim builders: the register-file programs for "these headers form a
//! valid chain from the checkpoint" and "this ledger entry is anchored in
//! a block of such a chain", with the prover data they take.
//!
//! Registers (24 words): `D` = words 0..8 (the running digest), `A` =
//! 8..16 (the anchor block's Merkle root), `R` = 16..24 (the ledger root).
//! Data enters as block words; every check is a predicate over the
//! committed values, so a claim is valid iff every predicate holds.

use lngap_contract::claim::{state_nibbles, words_from_bytes, ClaimData, ClaimSpec, Copy, Init, Pred, Src, Step};
use serde::{Deserialize, Serialize};

use crate::chain::{outpoint_bytes, MerklePath, RawHeader, ANCHOR_ROOT_OFFSET, ANCHOR_TX_LEN};
use crate::ledger::Path;

pub const N_WORDS: usize = 24;
/// Nibble offset of the block words in a compression step's predicate space.
const NB: usize = 8 * N_WORDS;
const D: usize = 0;
const A: usize = 64;
const R: usize = 128;

fn nibbles(b: &[u8]) -> Vec<u8> {
    lngap_contract::script_hash::nibbles(b)
}

fn words(b: &[u8]) -> Vec<u32> {
    words_from_bytes(b)
}

fn data_words(n: usize) -> [Src; 16] {
    core::array::from_fn(|j| if j < n { Src::Data(j) } else { Src::Const(0) })
}

/// Block: `n_data` data words, then the SHA-256 padding for a message of `bits` bits.
fn data_padded(n_data: usize, bits: u32) -> [Src; 16] {
    let mut b = data_words(n_data);
    b[n_data] = Src::Const(0x8000_0000);
    b[15] = Src::Const(bits);
    b
}

/// The second SHA-256 of a 32-byte digest in `D`.
fn hash_of_d() -> [Src; 16] {
    let mut b: [Src; 16] = core::array::from_fn(|j| if j < 8 { Src::Reg(j) } else { Src::Const(0) });
    b[8] = Src::Const(0x8000_0000);
    b[15] = Src::Const(256);
    b
}

/// The padding block after a full 64-byte data block.
fn pad_512() -> [Src; 16] {
    let mut b = [Src::Const(0); 16];
    b[0] = Src::Const(0x8000_0000);
    b[15] = Src::Const(512);
    b
}

/// `D ‖ sibling` or `sibling ‖ D` as one block (sibling as 8 data words).
fn node_block(right: bool) -> [Src; 16] {
    core::array::from_fn(|j| match (j < 8, right) {
        (true, false) | (false, true) => Src::Reg(j % 8),
        _ => Src::Data(j % 8),
    })
}

/// The steps verifying one header whose predecessor's digest is in `D`.
/// Afterwards `D` = the header's digest and `A` = its Merkle root.
fn header_steps(nbits: u32, target_le: [u8; 32], steps: &mut Vec<Step>) {
    let c1 = Step::compress("hdr_c1", Init::Iv, data_words(16))
        .with_preds(vec![Pred::EqNibbles { a: NB + 8, b: D, n: 64 }])
        .with_copies(vec![Copy { src: NB + 72, dst: A, n: 56 }]);
    let c2 = Step::compress("hdr_c2", Init::D, data_padded(4, 640))
        .with_preds(vec![Pred::EqConst { off: NB + 16, nibbles: nibbles(&nbits.to_le_bytes()) }])
        .with_copies(vec![Copy { src: NB, dst: A + 56, n: 8 }]);
    let c3 = Step::compress("hdr_c3", Init::Iv, hash_of_d());
    let target = Step::check("target", vec![Pred::LeTarget { target: target_le }]);
    steps.extend([c1, c2, c3, target]);
}

/// A header's data: its first 64 bytes, then the last 16.
fn header_data(h: &RawHeader, data: &mut ClaimData) {
    data.push(words(&h.0[..64]));
    data.push(words(&h.0[64..80]));
}

fn pad_to_power(steps: &mut Vec<Step>, k: usize) {
    let mut n = 1;
    while n < steps.len() {
        n *= k;
    }
    while steps.len() < n {
        steps.push(Step::nop());
    }
}

fn start_state(checkpoint: &[u8; 32]) -> Vec<u32> {
    let mut s = vec![0u32; N_WORDS];
    s[..8].copy_from_slice(&words(checkpoint));
    s
}

/// The constants of a header-chain claim, fixed when a contract opens.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HeaderShape {
    pub checkpoint: [u8; 32],
    pub nbits: u32,
    pub n_headers: usize,
}

impl HeaderShape {
    pub fn spec(&self) -> ClaimSpec {
        let mut steps = Vec::new();
        let target = RawHeader::target_le(self.nbits);
        for _ in 0..self.n_headers {
            header_steps(self.nbits, target, &mut steps);
        }
        pad_to_power(&mut steps, 2);
        ClaimSpec { n_words: N_WORDS, start: start_state(&self.checkpoint), steps, k: 2, inner: true }
    }
    /// The data for `headers` (one per header step group).
    pub fn data(&self, headers: &[RawHeader]) -> ClaimData {
        assert_eq!(headers.len(), self.n_headers);
        let mut data = Vec::new();
        for h in headers {
            header_data(h, &mut data);
        }
        data
    }
}

/// "These headers form a valid chain from the checkpoint at fixed difficulty."
#[derive(Clone, Debug)]
pub struct HeaderChainClaim {
    pub checkpoint: [u8; 32],
    pub nbits: u32,
    pub headers: Vec<RawHeader>,
}

impl HeaderChainClaim {
    pub fn shape(&self) -> HeaderShape {
        HeaderShape { checkpoint: self.checkpoint, nbits: self.nbits, n_headers: self.headers.len() }
    }
    pub fn build(&self) -> (ClaimSpec, ClaimData) {
        let sh = self.shape();
        (sh.spec(), sh.data(&self.headers))
    }
}

/// The constants of an anchored-entry claim, fixed when a contract opens:
/// the chain window, the previous anchor the anchor transaction must
/// spend, the entry, its ledger key (the path's sides), and the Merkle
/// path's sides (the anchor transaction's position in its block).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnchorShape {
    pub chain: HeaderShape,
    pub prev_anchor: bitcoin::OutPoint,
    #[serde(with = "serde_bytes64")]
    pub entry: [u8; 64],
    pub key: u32,
    pub merkle_sides: Vec<bool>,
}

mod serde_bytes64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(v: &[u8; 64], s: S) -> Result<S::Ok, S::Error> {
        hex::encode(v).serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 64], D::Error> {
        let h = String::deserialize(d)?;
        let b = hex::decode(h).map_err(serde::de::Error::custom)?;
        b.try_into().map_err(|_| serde::de::Error::custom("64 bytes"))
    }
}

/// The prover's data for an anchored-entry claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnchorData {
    pub headers: Vec<RawHeader>,
    /// The anchor transaction's legacy serialization ([`ANCHOR_TX_LEN`] bytes).
    pub anchor_tx: Vec<u8>,
    pub merkle_siblings: Vec<[u8; 32]>,
    pub ledger_siblings: Vec<[u8; 32]>,
}

impl AnchorShape {
    pub fn side(&self, level: usize) -> bool {
        (self.key >> level) & 1 == 1
    }
    /// "The entry is in the ledger whose root the anchor transaction
    /// (spending the previous anchor) carries, and that transaction is in
    /// the last of the chain's headers."
    pub fn spec(&self) -> ClaimSpec {
        let mut steps = Vec::new();
        let target = RawHeader::target_le(self.chain.nbits);
        for _ in 0..self.chain.n_headers {
            header_steps(self.chain.nbits, target, &mut steps);
        }
        // the anchor transaction: SHA-256d of 208 bytes; outpoint check on chunk 1, root copy from chunk 3
        let a1 = Step::compress("anchor_c1", Init::Iv, data_words(16)).with_preds(vec![Pred::EqConst { off: NB + 10, nibbles: nibbles(&outpoint_bytes(&self.prev_anchor)) }]);
        let a2 = Step::compress("anchor_c2", Init::D, data_words(16));
        let a3 = Step::compress("anchor_c3", Init::D, data_words(16)).with_copies(vec![Copy { src: NB + 2 * (ANCHOR_ROOT_OFFSET - 128), dst: R, n: 64 }]);
        let a4 = Step::compress("anchor_c4", Init::D, data_padded(4, 8 * ANCHOR_TX_LEN as u32));
        let a5 = Step::compress("anchor_c5", Init::Iv, hash_of_d());
        steps.extend([a1, a2, a3, a4, a5]);
        // Merkle path to the block's root (SHA-256d per node), then compare with A
        for right in &self.merkle_sides {
            steps.push(Step::compress("merkle_c1", Init::Iv, node_block(*right)));
            steps.push(Step::compress("merkle_c2", Init::D, pad_512()));
            steps.push(Step::compress("merkle_c3", Init::Iv, hash_of_d()));
        }
        steps.push(Step::check("merkle_root", vec![Pred::EqNibbles { a: D, b: A, n: 64 }]));
        // the entry's leaf hash (constant), the ledger path (single SHA-256 per node), compare with R
        let ew: [Src; 16] = core::array::from_fn(|j| Src::Const(words(&self.entry)[j]));
        steps.push(Step::compress("entry_c1", Init::Iv, ew));
        steps.push(Step::compress("entry_c2", Init::D, pad_512()));
        for j in 0..crate::ledger::DEPTH {
            steps.push(Step::compress("ledger_c1", Init::Iv, node_block(self.side(j))));
            steps.push(Step::compress("ledger_c2", Init::D, pad_512()));
        }
        steps.push(Step::check("ledger_root", vec![Pred::EqNibbles { a: D, b: R, n: 64 }]));
        pad_to_power(&mut steps, 2);
        ClaimSpec { n_words: N_WORDS, start: start_state(&self.chain.checkpoint), steps, k: 2, inner: true }
    }
    pub fn data(&self, d: &AnchorData) -> ClaimData {
        assert_eq!(d.headers.len(), self.chain.n_headers);
        assert_eq!(d.anchor_tx.len(), ANCHOR_TX_LEN);
        assert_eq!(d.merkle_siblings.len(), self.merkle_sides.len());
        assert_eq!(d.ledger_siblings.len(), crate::ledger::DEPTH);
        let mut data = Vec::new();
        for h in &d.headers {
            header_data(h, &mut data);
        }
        for chunk in [0..64, 64..128, 128..192, 192..208] {
            data.push(words(&d.anchor_tx[chunk]));
        }
        for s in &d.merkle_siblings {
            data.push(words(s));
        }
        for s in &d.ledger_siblings {
            data.push(words(s));
        }
        data
    }
    /// The heavier-chain refutation of this claim: one header longer from the same checkpoint.
    pub fn refutation(&self) -> HeaderShape {
        HeaderShape { checkpoint: self.chain.checkpoint, nbits: self.chain.nbits, n_headers: self.chain.n_headers + 1 }
    }
}

/// A complete anchored-entry claim (shape and data together).
#[derive(Clone, Debug)]
pub struct AnchorClaim {
    pub chain: HeaderChainClaim,
    pub prev_anchor: bitcoin::OutPoint,
    pub anchor_tx: Vec<u8>,
    pub merkle: MerklePath,
    pub entry: [u8; 64],
    pub ledger: Path,
}

impl AnchorClaim {
    pub fn shape(&self) -> AnchorShape {
        AnchorShape { chain: self.chain.shape(), prev_anchor: self.prev_anchor, entry: self.entry, key: self.ledger.key, merkle_sides: self.merkle.sides.clone() }
    }
    pub fn data(&self) -> AnchorData {
        AnchorData { headers: self.chain.headers.clone(), anchor_tx: self.anchor_tx.clone(), merkle_siblings: self.merkle.siblings.clone(), ledger_siblings: self.ledger.siblings.clone() }
    }
    pub fn build(&self) -> (ClaimSpec, ClaimData) {
        let sh = self.shape();
        (sh.spec(), sh.data(&self.data()))
    }
}

/// Native verdict on a claim with its data: the first step whose predicate
/// fails, if any (a valid claim has none).
pub fn first_failing_step(spec: &ClaimSpec, data: &ClaimData) -> Option<(usize, String)> {
    let mut s = spec.start.clone();
    for (i, step) in spec.steps.iter().enumerate() {
        let (next, ok) = spec.apply(step, &s, spec.data_for(data, i));
        if !ok {
            return Some((i, step.name()));
        }
        s = next;
    }
    None
}

/// The final register file as nibbles (for debugging).
pub fn end_nibbles(spec: &ClaimSpec, data: &ClaimData) -> Vec<u8> {
    state_nibbles(spec.states(data).last().unwrap())
}
