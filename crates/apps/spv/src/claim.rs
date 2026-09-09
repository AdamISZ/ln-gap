//! Claim builders: the register-file programs for "these headers form a
//! valid chain from the checkpoint" and "this ledger entry is anchored in
//! a block of such a chain", with the prover data they take.
//!
//! Registers (24 words): `D` = words 0..8 (the running digest), `A` =
//! 8..16 (the anchor block's Merkle root), `R` = 16..24 (the ledger root).
//! Data enters as block words; every check is a predicate over the
//! committed values, so a claim is valid iff every predicate holds.

use lngap_contract::claim::{state_nibbles, words_from_bytes, ClaimData, ClaimSpec, Copy, Init, Pred, Src, Step};

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

/// The steps and data verifying one header whose predecessor's digest is in `D`.
/// Afterwards `D` = the header's digest and `A` = its Merkle root.
fn header_steps(h: &RawHeader, nbits: u32, target_le: [u8; 32], steps: &mut Vec<Step>, data: &mut ClaimData) {
    let c1 = Step::compress("hdr_c1", Init::Iv, data_words(16))
        .with_preds(vec![Pred::EqNibbles { a: NB + 8, b: D, n: 64 }])
        .with_copies(vec![Copy { src: NB + 72, dst: A, n: 56 }]);
    let c2 = Step::compress("hdr_c2", Init::D, data_padded(4, 640))
        .with_preds(vec![Pred::EqConst { off: NB + 16, nibbles: nibbles(&nbits.to_le_bytes()) }])
        .with_copies(vec![Copy { src: NB, dst: A + 56, n: 8 }]);
    let c3 = Step::compress("hdr_c3", Init::Iv, hash_of_d());
    let target = Step::check("target", vec![Pred::LeTarget { target: target_le }]);
    steps.extend([c1, c2, c3, target]);
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

/// "These headers form a valid chain from the checkpoint at fixed difficulty."
#[derive(Clone, Debug)]
pub struct HeaderChainClaim {
    pub checkpoint: [u8; 32],
    pub nbits: u32,
    pub headers: Vec<RawHeader>,
}

impl HeaderChainClaim {
    pub fn build(&self) -> (ClaimSpec, ClaimData) {
        let mut steps = Vec::new();
        let mut data = Vec::new();
        let target = RawHeader::target_le(self.nbits);
        for h in &self.headers {
            header_steps(h, self.nbits, target, &mut steps, &mut data);
        }
        pad_to_power(&mut steps, 2);
        (ClaimSpec { n_words: N_WORDS, start: start_state(&self.checkpoint), steps, k: 2, inner: true }, data)
    }
}

/// "The entry is in the ledger whose root the anchor transaction (spending
/// the agreed previous anchor) carries, and that transaction is in the last
/// of these headers, a valid chain from the checkpoint."
#[derive(Clone, Debug)]
pub struct AnchorClaim {
    pub chain: HeaderChainClaim,
    pub prev_anchor: bitcoin::OutPoint,
    /// The anchor transaction's legacy serialization ([`ANCHOR_TX_LEN`] bytes).
    pub anchor_tx: Vec<u8>,
    pub merkle: MerklePath,
    pub entry: [u8; 64],
    pub ledger: Path,
}

impl AnchorClaim {
    pub fn build(&self) -> (ClaimSpec, ClaimData) {
        assert_eq!(self.anchor_tx.len(), ANCHOR_TX_LEN);
        let mut steps = Vec::new();
        let mut data = Vec::new();
        let target = RawHeader::target_le(self.chain.nbits);
        for h in &self.chain.headers {
            header_steps(h, self.chain.nbits, target, &mut steps, &mut data);
        }
        // the anchor transaction: SHA-256d of 208 bytes; outpoint check on chunk 1, root copy from chunk 3
        let a1 = Step::compress("anchor_c1", Init::Iv, data_words(16)).with_preds(vec![Pred::EqConst { off: NB + 10, nibbles: nibbles(&outpoint_bytes(&self.prev_anchor)) }]);
        let a2 = Step::compress("anchor_c2", Init::D, data_words(16));
        let a3 = Step::compress("anchor_c3", Init::D, data_words(16)).with_copies(vec![Copy { src: NB + 2 * (ANCHOR_ROOT_OFFSET - 128), dst: R, n: 64 }]);
        let a4 = Step::compress("anchor_c4", Init::D, data_padded(4, 8 * ANCHOR_TX_LEN as u32));
        let a5 = Step::compress("anchor_c5", Init::Iv, hash_of_d());
        steps.extend([a1, a2, a3, a4, a5]);
        for chunk in [0..64, 64..128, 128..192, 192..208] {
            data.push(words(&self.anchor_tx[chunk]));
        }
        // Merkle path to the block's root (SHA-256d per node), then compare with A
        for (s, right) in self.merkle.siblings.iter().zip(&self.merkle.sides) {
            steps.push(Step::compress("merkle_c1", Init::Iv, node_block(*right)));
            steps.push(Step::compress("merkle_c2", Init::D, pad_512()));
            steps.push(Step::compress("merkle_c3", Init::Iv, hash_of_d()));
            data.push(words(s));
        }
        steps.push(Step::check("merkle_root", vec![Pred::EqNibbles { a: D, b: A, n: 64 }]));
        // the entry's leaf hash (constant), the ledger path (single SHA-256 per node), compare with R
        let ew: [Src; 16] = core::array::from_fn(|j| Src::Const(words(&self.entry)[j]));
        steps.push(Step::compress("entry_c1", Init::Iv, ew));
        steps.push(Step::compress("entry_c2", Init::D, pad_512()));
        for (j, s) in self.ledger.siblings.iter().enumerate() {
            steps.push(Step::compress("ledger_c1", Init::Iv, node_block(self.ledger.side(j))));
            steps.push(Step::compress("ledger_c2", Init::D, pad_512()));
            data.push(words(s));
        }
        steps.push(Step::check("ledger_root", vec![Pred::EqNibbles { a: D, b: R, n: 64 }]));
        pad_to_power(&mut steps, 2);
        (ClaimSpec { n_words: N_WORDS, start: start_state(&self.chain.checkpoint), steps, k: 2, inner: true }, data)
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
