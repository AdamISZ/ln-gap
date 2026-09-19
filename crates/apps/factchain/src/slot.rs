//! Slot claims: "the entries for game `g` at moves `d-1` (the counterparty's)
//! and `d` (mine) sit in the blocks `d-1` and `d` headers after the
//! checkpoint, on a valid PoW chain, each stating its move and carrying a
//! valid signature under its mover's key".
//!
//! Every check is a predicate the bisection can isolate:
//!
//! - prev link: each header's `prev` field equals the previous digest,
//!   held in register `P` (the checkpoint for the first header);
//! - proof of work: the digest is at most the target (`LeTargetBe`);
//! - root: a header's `root` field (copied to `R` as the header is
//!   absorbed) equals the entry root of the block's entry;
//! - content: the entry's first word is the constant `(game_id, depth,
//!   mover)`, and its second word `(move, state)` is copied to register `E`
//!   (my slot) or `E2` (the counterparty's), which the Move leaf compares
//!   against the Lamport reveals ([`lngap_contract::EndBind`]);
//! - signature: the entry root is the hash of a stream holding the digest
//!   of each 20-byte chunk of the entry ([`crate::entry_root`]); the chunks
//!   are the mover's Lamport preimages for the state bits, so each digest
//!   in the stream must equal the pinned commitment selected by the
//!   corresponding state bit of the content word (`EqConstBit`). The claim
//!   never hashes a preimage: the block's root already commits to the
//!   digests, and the predicates tie them to the key.
//!
//! Register file (17 words, 136 nibbles):
//!
//! ```text
//! D   words  0..5   nibbles   0..40   the hash state
//! P   words  5..10  nibbles  40..80   previous digest
//! R   words 10..15  nibbles  80..120  the current header's root field
//! E   word  15      nibbles 120..128  my entry's word 1 = (move, state)
//! E2  word  16      nibbles 128..136  the counterparty's entry's word 1
//! ```
//!
//! Steps: per header `hdr_b0..hdr_b11`, `hdr_pad`, `hdr_end` (PoW, `D -> P`);
//! after header `d-1` the counterparty's entry (`pe_*`), after header `d`
//! mine (`oe_*`): 64 absorbs of the 512-byte entry stream (the content
//! block, then 3 blocks per digest), `_pad`, `_root`. `14 d + 66` steps for
//! a depth-1 claim, `14 d + 132` from depth 2, padded to a power of two.
//! This is the per-depth claim the built tic-tac-toe path uses; the
//! depth-independent one is [`crate::stall`].

use lngap_contract::claim::{ClaimData, ClaimSpec, Copy, HashKind, Init, Pred, Src, Step};
use lngap_n4bit::{claim_blocks, hash_claim, Digest, DIGEST_BYTES};

use crate::{entry_stream, CHUNK, CHUNK_PAD, ENTRY_HEAD, HEADER_BYTES, STREAM_BYTES};

pub const N_WORDS: usize = 17;
pub const NB: usize = 8 * N_WORDS;
pub const D_OFF: usize = 0;
pub const P_OFF: usize = 40;
pub const R_OFF: usize = 80;
pub const E_OFF: usize = 120;
pub const E2_OFF: usize = 128;
/// The register words holding my and the counterparty's `(move, state)` words.
pub const E_WORD: usize = 15;
pub const E2_WORD: usize = 16;
/// Signed state bits per entry (tic-tac-toe's state).
pub const STATE_BITS: usize = 21;
/// Bytes of an encoded [`SlotEntry`]: the 8-byte content and one preimage per state bit.
pub const ENTRY_BYTES: usize = ENTRY_HEAD + STATE_BITS * CHUNK;
/// Steps per header (12 absorbs, the pad block, the end check).
pub const STEPS_PER_HEADER: usize = crate::HEADER_ABSORBS + 2;
/// Steps per entry (64 stream absorbs, the pad block, the root check).
pub const ENTRY_STEPS: usize = STREAM_BYTES / 8 + 2;

/// A published move: content plus the mover's Lamport preimages for the
/// state bits (`sigs[i]` opens bit `i` of `state`). `state` is the 21-bit
/// tic-tac-toe state as a number (`bits_to_uint` of the program's bits).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotEntry {
    pub game_id: u16,
    pub depth: u8,
    pub mover: u8,
    pub mv: u8,
    pub state: u32,
    pub sigs: Vec<[u8; CHUNK]>,
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
        assert_eq!(self.sigs.len(), STATE_BITS);
        let mut v = Vec::with_capacity(ENTRY_BYTES);
        v.extend_from_slice(&Self::word0(self.game_id, self.depth, self.mover).to_be_bytes());
        v.extend_from_slice(&Self::word1(self.mv, self.state).to_be_bytes());
        for s in &self.sigs {
            v.extend_from_slice(s);
        }
        v
    }
    pub fn decode(b: &[u8]) -> Option<SlotEntry> {
        if b.len() != ENTRY_BYTES {
            return None;
        }
        let w0 = u32::from_be_bytes(b[0..4].try_into().ok()?);
        let w1 = u32::from_be_bytes(b[4..8].try_into().ok()?);
        let sigs = b[ENTRY_HEAD..].chunks(CHUNK).map(|c| c.try_into().unwrap()).collect();
        Some(SlotEntry { game_id: (w0 >> 16) as u16, depth: ((w0 >> 8) & 0xff) as u8, mover: (w0 & 0xff) as u8, mv: (w1 >> 24) as u8, state: w1 & 0x00ff_ffff, sigs })
    }
    /// Do the preimages open the state bits under these commitments
    /// (`commits[i] = [h(p0), h(p1)]`)? What the claim checks, natively.
    pub fn check_sigs(&self, commits: &[[Digest; 2]]) -> bool {
        commits.len() == STATE_BITS
            && self.sigs.len() == STATE_BITS
            && self.sigs.iter().enumerate().all(|(i, p)| hash_claim(p) == commits[i][((self.state >> i) & 1) as usize])
    }
}

/// One slot's constants: whose move, at what depth, under which commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotSpec {
    pub depth: u8,
    pub mover: u8,
    /// `[h(p0), h(p1)]` per state bit; empty (all zero) when only the
    /// claim's shape matters.
    pub commits: Vec<[Digest; 2]>,
}

/// The constants of a slot claim at depth `depth`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotClaim {
    pub checkpoint: Digest,
    pub target: Digest,
    pub game_id: u16,
    /// Headers from the checkpoint to my slot's block, inclusive.
    pub depth: usize,
    /// The counterparty's slot (`depth - 1`), absent at depth 1.
    pub prev: Option<SlotSpec>,
    pub own: SlotSpec,
}

fn nibbles(bytes: &[u8]) -> Vec<u8> {
    bytes.iter().flat_map(|&b| [b >> 4, b & 15]).collect()
}

impl SlotClaim {
    pub fn n_steps(&self) -> usize {
        STEPS_PER_HEADER * self.depth + ENTRY_STEPS * (1 + usize::from(self.prev.is_some()))
    }

    /// The prover's data, in step order: each header's 6 word pairs, the
    /// counterparty's entry stream (64 pairs) after header `depth - 1`,
    /// mine after header `depth`. A missing entry streams as empty.
    pub fn data(&self, headers: &[[u8; HEADER_BYTES]], prev_entry: Option<&[u8]>, own_entry: &[u8]) -> ClaimData {
        assert_eq!(headers.len(), self.depth, "slot claim needs {} headers", self.depth);
        let mut data = Vec::new();
        for (h, hdr) in headers.iter().enumerate() {
            for w in claim_blocks(hdr) {
                data.push(w.to_vec());
            }
            if h + 2 == self.depth && self.prev.is_some() {
                for w in claim_blocks(&entry_stream(prev_entry.unwrap_or(&[]))) {
                    data.push(w.to_vec());
                }
            }
            if h + 1 == self.depth {
                for w in claim_blocks(&entry_stream(own_entry)) {
                    data.push(w.to_vec());
                }
            }
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

    fn header_steps(steps: &mut Vec<Step>, target: &Digest) {
        let data = || vec![Src::Data(0), Src::Data(1)];
        for b in 0..crate::HEADER_ABSORBS {
            let init = if b == 0 { Init::Iv } else { Init::D };
            let mut step = Step::compress(&format!("hdr_b{b}"), init, data());
            // prev field: header nibbles 0..40 = steps 0, 1 and half of 2; root field: 40..80
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
        steps.push(Step::compress("hdr_pad", Init::D, vec![Src::Const(0), Src::Const(0)]));
        steps.push(Step::Simple { name: "hdr_end".into(), preds: vec![Pred::LeTargetBe { off: D_OFF, target: nibbles(target) }], copies: vec![Copy { src: D_OFF, dst: P_OFF, n: 40 }] });
    }

    /// The entry stream's 64 absorbs (content, then 3 blocks per digest),
    /// the pad block and the root check. `e_off` is where the content's
    /// `(move, state)` word lands; the state's bit `i` is then bit `i % 4`
    /// of nibble `e_off + 7 - i / 4` (the word's low 24 bits, big-endian).
    fn entry_steps(steps: &mut Vec<Step>, game_id: u16, slot: &SlotSpec, e_off: usize, tag: &str) {
        let data = || vec![Src::Data(0), Src::Data(1)];
        let w0 = SlotEntry::word0(game_id, slot.depth, slot.mover);
        steps.push(
            Step::compress(&format!("{tag}_c"), Init::Iv, data())
                .with_preds(vec![Pred::EqConst { off: NB, nibbles: nibbles(&w0.to_be_bytes()) }])
                .with_copies(vec![Copy { src: NB + 8, dst: e_off, n: 8 }]),
        );
        let zero = [[0u8; DIGEST_BYTES]; 2];
        for i in 0..STATE_BITS {
            let c = slot.commits.get(i).unwrap_or(&zero);
            let (n0, n1) = (nibbles(&c[0]), nibbles(&c[1]));
            let nib = e_off + 7 - i / 4;
            let bit = (i % 4) as u8;
            let by_bit = |lo: usize, hi: usize| Pred::EqConstBit { nib, bit, off: NB, if0: n0[lo..hi].to_vec(), if1: n1[lo..hi].to_vec() };
            steps.push(Step::compress(&format!("{tag}_s{i}a"), Init::D, data()).with_preds(vec![by_bit(0, 16)]));
            steps.push(Step::compress(&format!("{tag}_s{i}b"), Init::D, data()).with_preds(vec![by_bit(16, 32)]));
            steps.push(Step::compress(&format!("{tag}_s{i}c"), Init::D, data()).with_preds(vec![by_bit(32, 40), Pred::EqConst { off: NB + 8, nibbles: vec![0; 2 * (CHUNK_PAD - CHUNK)] }]));
        }
        steps.push(Step::compress(&format!("{tag}_pad"), Init::D, vec![Src::Const(0), Src::Const(0)]));
        steps.push(Step::check("ent_root", vec![Pred::EqNibbles { a: D_OFF, b: R_OFF, n: 40 }]));
    }

    pub fn spec(&self) -> ClaimSpec {
        let mut steps = Vec::new();
        for h in 0..self.depth {
            Self::header_steps(&mut steps, &self.target);
            if h + 2 == self.depth {
                if let Some(p) = &self.prev {
                    Self::entry_steps(&mut steps, self.game_id, p, E2_OFF, "pe");
                }
            }
            if h + 1 == self.depth {
                Self::entry_steps(&mut steps, self.game_id, &self.own, E_OFF, "oe");
            }
        }
        assert_eq!(steps.len(), self.n_steps());
        let n = steps.len().next_power_of_two();
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

    /// A toy key: preimages `p_{i,b}` and their commitments.
    struct Key {
        pre: Vec<[[u8; CHUNK]; 2]>,
    }
    impl Key {
        fn new(seed: u8) -> Key {
            Key { pre: (0..STATE_BITS as u8).map(|i| [[seed ^ i; CHUNK], [seed ^ i ^ 0x80; CHUNK]]).collect() }
        }
        fn commits(&self) -> Vec<[Digest; 2]> {
            self.pre.iter().map(|p| [hash_claim(&p[0]), hash_claim(&p[1])]).collect()
        }
        fn sign(&self, state: u32) -> Vec<[u8; CHUNK]> {
            (0..STATE_BITS).map(|i| self.pre[i][((state >> i) & 1) as usize]).collect()
        }
    }

    fn entry(key: &Key, depth: u8, state: u32) -> SlotEntry {
        SlotEntry { game_id: 7, depth, mover: (depth % 2 == 0) as u8, mv: 4, state, sigs: key.sign(state) }
    }

    fn chain(entries: &[Vec<u8>]) -> (Digest, Vec<[u8; HEADER_BYTES]>) {
        let g = genesis();
        let mut miner = Miner::new(g.header.digest(), 0);
        let mut client = ChainClient::from_checkpoint(0, g.header.digest());
        for e in entries {
            miner.submit(e.clone());
            let b = miner.mine_next().unwrap();
            client.verify_and_append(&b).unwrap();
        }
        (g.header.digest(), client.chain_headers().iter().map(|h| h.0).collect())
    }

    fn claim(cp: Digest, keys: &[Key; 2], depth: usize) -> SlotClaim {
        let spec = |d: usize| SlotSpec { depth: d as u8, mover: (d % 2 == 0) as u8, commits: keys[d % 2].commits() };
        SlotClaim { checkpoint: cp, target: target_from_difficulty(DIFFICULTY_BITS), game_id: 7, depth, prev: (depth >= 2).then(|| spec(depth - 1)), own: spec(depth) }
    }

    #[test]
    fn honest_claims_are_valid_at_every_depth() {
        let keys = [Key::new(1), Key::new(2)];
        let entries: Vec<Vec<u8>> = (1..=4u8).map(|d| entry(&keys[d as usize % 2], d, 0x1000 + u32::from(d)).encode()).collect();
        let (cp, headers) = chain(&entries);
        for d in 1..=4usize {
            let c = claim(cp, &keys, d);
            let spec = c.spec();
            let data = c.data(&headers[..d], (d >= 2).then(|| entries[d - 2].as_slice()), &entries[d - 1]);
            assert!(spec.valid(&data), "depth {d}");
            let end = spec.states(&data).last().unwrap().clone();
            assert_eq!(end[E_WORD], SlotEntry::word1(4, 0x1000 + d as u32), "E is my (move, state)");
            if d >= 2 {
                assert_eq!(end[E2_WORD], SlotEntry::word1(4, 0x1000 + d as u32 - 1), "E2 is the counterparty's");
            }
            assert_eq!(spec.steps.len(), c.n_steps().next_power_of_two());
        }
    }

    #[test]
    fn garbage_signatures_and_wrong_slots_fail() {
        let keys = [Key::new(1), Key::new(2)];
        let good = entry(&keys[0], 2, 0x2002);
        let mut garbage = good.clone();
        garbage.sigs[5] = [0xEE; CHUNK];
        let e1 = entry(&keys[1], 1, 0x2001).encode();
        let (cp, headers) = chain(&[e1.clone(), garbage.encode()]);
        let c = claim(cp, &keys, 2);
        let spec = c.spec();
        // the block really holds the garbage-signed entry: root ok, signature predicate fails
        assert!(!spec.valid(&c.data(&headers, Some(&e1), &garbage.encode())));
        // claiming the good entry instead: signatures ok, root fails
        assert!(!spec.valid(&c.data(&headers, Some(&e1), &good.encode())));
        // an empty counterparty slot
        let (cp2, headers2) = chain(&[vec![], good.encode()]);
        let c2 = claim(cp2, &keys, 2);
        assert!(!c2.spec().valid(&c2.data(&headers2, Some(&[]), &good.encode())));
        // native check agrees
        assert!(good.check_sigs(&keys[0].commits()));
        assert!(!garbage.check_sigs(&keys[0].commits()));
        assert!(!good.check_sigs(&keys[1].commits()));
    }

    #[test]
    fn entry_roundtrip() {
        let e = entry(&Key::new(3), 3, 0x1234);
        assert_eq!(SlotEntry::decode(&e.encode()), Some(e));
    }
}
