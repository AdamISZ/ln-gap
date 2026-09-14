//! Slot claims: "the entry for game `g`, move `d` by `mover` sits in the
//! block `d` headers after the checkpoint, on a valid PoW chain".
//!
//! This is the full inclusion claim the venue design needs (unlike
//! [`crate::claim::FactChainShape`], which only hashes the header bytes).
//! Every check is a predicate the bisection can isolate:
//!
//! - prev link: each header's `prev` field equals the previous digest,
//!   held in register `P` (the checkpoint for the first header);
//! - proof of work: the digest is at most the target (`LeTargetBe`);
//! - root: the last header's `root` field (copied to register `R` as the
//!   header is absorbed) equals the hash of the entry;
//! - entry content: the entry's first word is the constant
//!   `(game_id, depth, mover)`, and its second word `(move, state)` is
//!   copied to register `E`, which the Move leaf compares against the
//!   mover's Lamport reveal ([`lngap_contract::EndBind`]).
//!
//! Register file (16 words, 128 nibbles):
//!
//! ```text
//! D  words  0..5   nibbles   0..40   the hash state
//! P  words  5..10  nibbles  40..80   previous digest
//! R  words 10..15  nibbles  80..120  the last header's root field
//! E  word  15      nibbles 120..128  entry word 1 = (move, state)
//! ```
//!
//! A 48-byte header is absorbed in 6 steps of 16 nibbles; the fields sit
//! at header nibbles `prev 0..40`, `root 40..80`, `height 80..88`,
//! `nonce 88..96`, so step `b` carries header nibbles `16b..16b+16`.
//!
//! Steps: per header `hdr_b0..hdr_b5`, `hdr_pad` (zero block), `hdr_end`
//! (PoW check, `D -> P`); then `ent_b0..ent_b3`, `ent_pad`, `root_ok`.
//! `8 n_headers + 6` steps, padded to a power of two.

use lngap_contract::claim::{ClaimData, ClaimSpec, Copy, HashKind, Init, Pred, Src, Step};
use lngap_n4bit::{claim_blocks, hash_claim, Digest, DIGEST_BYTES};

pub const N_WORDS: usize = 16;
pub const NB: usize = 8 * N_WORDS;
pub const D_OFF: usize = 0;
pub const P_OFF: usize = 40;
pub const R_OFF: usize = 80;
pub const E_OFF: usize = 120;
/// The register word holding the entry's `(move, state)` word.
pub const E_WORD: usize = 15;
/// Bytes of an encoded [`SlotEntry`].
pub const ENTRY_BYTES: usize = 28;
/// Steps per header (6 absorbs, the pad block, the end check).
pub const STEPS_PER_HEADER: usize = 8;
/// Steps for the entry (4 absorbs, the pad block, the root check).
pub const ENTRY_STEPS: usize = 6;

/// A published move. `state` is the 21-bit tic-tac-toe state as a number
/// (`bits_to_uint` of the program's state bits); `tag` is the claim-native
/// hash of the mover's Lamport preimages for `(move, state)`, served
/// alongside the entry so anyone can check them against the pinned key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotEntry {
    pub game_id: u16,
    pub depth: u8,
    pub mover: u8,
    pub mv: u8,
    pub state: u32,
    pub tag: Digest,
}

impl SlotEntry {
    /// Word 0 of the entry: `game_id << 16 | depth << 8 | mover`.
    pub fn word0(game_id: u16, depth: u8, mover: u8) -> u32 {
        (u32::from(game_id) << 16) | (u32::from(depth) << 8) | u32::from(mover)
    }
    /// Word 1 of the entry: `move << 24 | state` (state fits 24 bits).
    pub fn word1(mv: u8, state: u32) -> u32 {
        assert!(state >> 24 == 0, "state fits 24 bits");
        (u32::from(mv) << 24) | state
    }
    pub fn encode(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(ENTRY_BYTES);
        v.extend_from_slice(&Self::word0(self.game_id, self.depth, self.mover).to_be_bytes());
        v.extend_from_slice(&Self::word1(self.mv, self.state).to_be_bytes());
        v.extend_from_slice(&self.tag);
        v
    }
    pub fn decode(b: &[u8]) -> Option<SlotEntry> {
        if b.len() != ENTRY_BYTES {
            return None;
        }
        let w0 = u32::from_be_bytes(b[0..4].try_into().ok()?);
        let w1 = u32::from_be_bytes(b[4..8].try_into().ok()?);
        let mut tag = [0u8; DIGEST_BYTES];
        tag.copy_from_slice(&b[8..28]);
        Some(SlotEntry { game_id: (w0 >> 16) as u16, depth: ((w0 >> 8) & 0xff) as u8, mover: (w0 & 0xff) as u8, mv: (w1 >> 24) as u8, state: w1 & 0x00ff_ffff, tag })
    }
    /// The tag over served preimages (concatenated, move then state).
    pub fn tag_of(preimages: &[[u8; 20]]) -> Digest {
        hash_claim(&preimages.concat())
    }
}

/// The constants of a slot claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotShape {
    pub checkpoint: Digest,
    pub target: Digest,
    /// Headers from the checkpoint to the slot's block, inclusive: the slot index.
    pub n_headers: usize,
    pub game_id: u16,
    pub depth: u8,
    pub mover: u8,
}

fn nibbles(bytes: &[u8]) -> Vec<u8> {
    bytes.iter().flat_map(|&b| [b >> 4, b & 15]).collect()
}

impl SlotShape {
    pub fn n_steps(&self) -> usize {
        STEPS_PER_HEADER * self.n_headers + ENTRY_STEPS
    }

    /// The prover's data: the headers' 6 word pairs each, then the entry's 4.
    pub fn data(&self, headers: &[[u8; 48]], entry: &[u8]) -> ClaimData {
        assert_eq!(headers.len(), self.n_headers, "slot claim needs {} headers", self.n_headers);
        assert_eq!(entry.len(), ENTRY_BYTES);
        let mut data = Vec::new();
        for h in headers {
            for w in claim_blocks(h) {
                data.push(w.to_vec());
            }
        }
        for w in claim_blocks(entry) {
            data.push(w.to_vec());
        }
        data
    }

    /// The start state: `P` = checkpoint, everything else zero.
    pub fn start(&self) -> Vec<u32> {
        let mut s = vec![0u32; N_WORDS];
        for (i, w) in claim_blocks(&self.checkpoint).iter().flatten().enumerate().take(5) {
            s[5 + i] = *w;
        }
        s
    }

    pub fn spec(&self) -> ClaimSpec {
        let mut steps = Vec::new();
        let data = || vec![Src::Data(0), Src::Data(1)];
        let zero = || vec![Src::Const(0), Src::Const(0)];
        for _ in 0..self.n_headers {
            for b in 0..6 {
                let init = if b == 0 { Init::Iv } else { Init::D };
                let mut step = Step::compress(&format!("hdr_b{b}"), init, data());
                // prev field: header nibbles 0..40 = steps 0, 1 and half of 2
                step = match b {
                    0 => step.with_preds(vec![Pred::EqNibbles { a: NB, b: P_OFF, n: 16 }]),
                    1 => step.with_preds(vec![Pred::EqNibbles { a: NB, b: P_OFF + 16, n: 16 }]),
                    2 => step.with_preds(vec![Pred::EqNibbles { a: NB, b: P_OFF + 32, n: 8 }]).with_copies(vec![Copy { src: NB + 8, dst: R_OFF, n: 8 }]),
                    3 => step.with_copies(vec![Copy { src: NB, dst: R_OFF + 8, n: 16 }]),
                    4 => step.with_copies(vec![Copy { src: NB, dst: R_OFF + 24, n: 16 }]),
                    _ => step,
                };
                steps.push(step);
            }
            steps.push(Step::compress("hdr_pad", Init::D, zero()));
            steps.push(Step::Simple {
                name: "hdr_end".into(),
                preds: vec![Pred::LeTargetBe { off: D_OFF, target: nibbles(&self.target) }],
                copies: vec![Copy { src: D_OFF, dst: P_OFF, n: 40 }],
            });
        }
        let w0 = SlotEntry::word0(self.game_id, self.depth, self.mover);
        steps.push(
            Step::compress("ent_b0", Init::Iv, data())
                .with_preds(vec![Pred::EqConst { off: NB, nibbles: nibbles(&w0.to_be_bytes()) }])
                .with_copies(vec![Copy { src: NB + 8, dst: E_OFF, n: 8 }]),
        );
        for b in 1..4 {
            steps.push(Step::compress(&format!("ent_b{b}"), Init::D, data()));
        }
        steps.push(Step::compress("ent_pad", Init::D, zero()));
        steps.push(Step::check("root_ok", vec![Pred::EqNibbles { a: D_OFF, b: R_OFF, n: 40 }]));
        let mut n = 1;
        while n < steps.len() {
            n *= 2;
        }
        while steps.len() < n {
            steps.push(Step::nop());
        }
        ClaimSpec { n_words: N_WORDS, start: self.start(), steps, k: 2, inner: true, hash: HashKind::N4Bit, flat_inner: true }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{genesis, ChainClient, Miner, DIFFICULTY_BITS};
    use lngap_n4bit::target_from_difficulty;

    fn chain(n: usize, entries: &[Vec<u8>]) -> (Digest, Vec<[u8; 48]>) {
        let g = genesis();
        let mut miner = Miner::new(g.header.digest(), 0);
        let mut client = ChainClient::from_checkpoint(0, g.header.digest());
        for i in 0..n {
            miner.submit(entries.get(i).cloned().unwrap_or_default());
            let b = miner.mine_next().unwrap();
            client.verify_and_append(&b).unwrap();
        }
        (g.header.digest(), client.chain_headers().iter().map(|h| h.0).collect())
    }

    fn entry(depth: u8) -> SlotEntry {
        SlotEntry { game_id: 7, depth, mover: 0, mv: 4, state: 0x1234, tag: [9u8; 20] }
    }

    #[test]
    fn header_digest_is_the_claim_hash() {
        let (_, headers) = chain(2, &[]);
        let h = crate::Header(headers[1]);
        let mut spec_state = vec![0u32; N_WORDS];
        let shape = SlotShape { checkpoint: [0; 20], target: [0xff; 20], n_headers: 1, game_id: 0, depth: 1, mover: 0 };
        let spec = shape.spec();
        let data = shape.data(&[headers[1]], &entry(1).encode());
        for (i, step) in spec.steps.iter().enumerate().take(7) {
            spec_state = spec.apply(i, step, &spec_state, spec.data_for(&data, i)).0;
        }
        let d: Vec<u32> = claim_blocks(&h.digest()).iter().flatten().copied().take(5).collect();
        assert_eq!(&spec_state[..5], &d[..], "D after the header's 7 compressions is Header::digest");
    }

    #[test]
    fn honest_slot_claim_is_valid_at_every_depth() {
        let entries: Vec<Vec<u8>> = (1..=4).map(|d| entry(d).encode()).collect();
        let (cp, headers) = chain(4, &entries);
        for d in 1..=4usize {
            let shape = SlotShape { checkpoint: cp, target: target_from_difficulty(DIFFICULTY_BITS), n_headers: d, game_id: 7, depth: d as u8, mover: 0 };
            let spec = shape.spec();
            let data = shape.data(&headers[..d], &entries[d - 1]);
            assert!(spec.valid(&data), "depth {d}");
            let end = spec.states(&data).last().unwrap().clone();
            assert_eq!(end[E_WORD], SlotEntry::word1(4, 0x1234), "E holds (move, state)");
            assert_eq!(spec.steps.len(), (STEPS_PER_HEADER * d + ENTRY_STEPS).next_power_of_two());
        }
    }

    #[test]
    fn wrong_entry_wrong_prev_and_wrong_content_fail() {
        let entries: Vec<Vec<u8>> = (1..=2).map(|d| entry(d).encode()).collect();
        let (cp, headers) = chain(2, &entries);
        let shape = SlotShape { checkpoint: cp, target: target_from_difficulty(DIFFICULTY_BITS), n_headers: 2, game_id: 7, depth: 2, mover: 0 };
        let spec = shape.spec();
        // an entry from another slot: root_ok fails
        assert!(!spec.valid(&shape.data(&headers, &entries[0])));
        // a header chain not linked to the checkpoint: prev fails
        let mut bad = headers.clone();
        bad[0][0] ^= 1;
        assert!(!spec.valid(&shape.data(&bad, &entries[1])));
        // the right slot but claimed for the other mover: content fails
        let other = SlotShape { mover: 1, ..shape.clone() };
        assert!(!other.spec().valid(&other.data(&headers, &entries[1])));
        // wrong depth claimed (entry says 2, claim says 1 with 1 header): root fails
        let d1 = SlotShape { n_headers: 1, depth: 1, ..shape.clone() };
        assert!(!d1.spec().valid(&d1.data(&headers[..1], &entries[1])));
    }

    #[test]
    fn entry_roundtrip() {
        let e = entry(3);
        assert_eq!(SlotEntry::decode(&e.encode()), Some(e));
    }
}
