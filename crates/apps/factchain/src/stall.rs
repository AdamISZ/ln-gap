//! The depth-independent stall claim (docs/planning/VENUE.md §10c, as
//! revised while building it, docs/design-notes/DECISIONS.md D28): "my entry is in slot
//! `d`, the counterparty's in slot `d - 1`, and slot `d + 1` holds nothing
//! of the counterparty's", one program for every depth; and its variant
//! the LIE EXHIBIT: "the counterparty's entry is in slot `d`, mine in
//! `d - 1`" (`check_next = false`).
//!
//! What makes it depth-independent: the claim always covers `w_max` header
//! slots after the checkpoint, and the depth is a register the prover
//! states up front (bound to its reveal by the stall leaf, or living inside
//! the state it reveals). Each header step's checks are gated on that
//! register against the step's own index: links and proof of work through
//! the last slot the claim needs, the head checks at exactly `d - 1`, `d`
//! and `d + 1`, nothing beyond, where the prover feeds zeros. The header
//! carries the entry's head (8 bytes of content: game, depth, mover, move;
//! then 40 bytes of state), so what a slot holds is header data, and no
//! entry stream is absorbed at all.
//!
//! What the claim does NOT check: signatures. A slot holds an entry if its
//! header's head says so; whether that entry's Lamport preimages open the
//! mover's key is a separate fact, and a garbage-signed entry is a lie its
//! victim exhibits, not an absence.
//!
//! The register [`Layout`] is the game's: `D` and `P` (the hash state and
//! the previous header digest, five words each), then `E` and `E2` (the
//! state word or words of slots `d` and `d - 1`) and the depth number
//! (its own word, or two nibbles inside `E`). Tic-tac-toe: 13 words, the
//! head's `(move, state)` word; chess: 30 words, a whole 40-byte position
//! with the move and the depth in its spare bytes.
//!
//! Steps: the preamble absorbs the `E`, `E2` (and depth) words as data and
//! copies them into their registers, then checks the depth's range and,
//! at depth 1, that `E2` is the initial state; then per header slot
//! `h = 1..=w_max`: twelve absorbs (links on the first three against `P`,
//! or the checkpoint constant at `h = 1`; the head on blocks 5 to 10),
//! the pad block, the end check (proof of work, `D -> P`). Padded to a
//! power of `k` with no-ops.

use lngap_contract::claim::{words_from_bytes, ClaimData, ClaimSpec, Cmp, Copy, HashKind, Init, Pred, Src, Step};
use lngap_n4bit::{claim_blocks, Digest};

use crate::slot::SlotEntry;
use crate::{HEADER_ABSORBS, HEADER_BYTES};

pub const D_OFF: usize = 0;
pub const P_OFF: usize = 40;
/// Absorbs, the pad block, the end check.
pub const STEPS_PER_HEADER: usize = HEADER_ABSORBS + 2;
/// The first header block holding the head (bytes 40..48 of the header).
const HEAD_BLOCK: usize = 5;
/// Nibbles of the depth number.
pub const DEP_NIBBLES: usize = 2;

/// Where a game's state words live in the register file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub n_words: usize,
    /// Nibble offset and width of `E` (slot `d`'s state word or words).
    pub e_off: usize,
    pub e_nibbles: usize,
    /// Nibble offset of `E2` (slot `d - 1`'s), the same width.
    pub e2_off: usize,
    /// Nibble offset of the two-nibble depth number.
    pub dep_nib: usize,
    /// The word holding the depth number when it is not inside `E`
    /// (absorbed and copied by the preamble).
    pub dep_word: Option<usize>,
    /// Byte offset of `E` within the header's 48-byte head.
    pub head_e_at: usize,
}

impl Layout {
    /// Tic-tac-toe: `D P E E2 DEP`, 13 words; `E` is the head's second
    /// word `(move, state)`.
    pub fn tictactoe() -> Layout {
        Layout { n_words: 13, e_off: 80, e_nibbles: 8, e2_off: 88, dep_nib: 102, dep_word: Some(12), head_e_at: 4 }
    }
    /// Chess: `D P E E2`, 30 words; `E` is the 40-byte state after the
    /// move: the position's 36 bytes, then from, to, promotion and the
    /// depth in byte 39 (`lngap_chess_fc`), so the depth number is `E`'s
    /// nibbles 78..80.
    pub fn chess() -> Layout {
        Layout { n_words: 30, e_off: 80, e_nibbles: 80, e2_off: 160, dep_nib: 80 + 78, dep_word: None, head_e_at: 8 }
    }
    pub fn nb(&self) -> usize {
        8 * self.n_words
    }
    pub fn e_words(&self) -> usize {
        self.e_nibbles / 8
    }
    /// The register word holding the depth number.
    pub fn dep_word_index(&self) -> usize {
        self.dep_nib / 8
    }
}

/// The constants of a role's stall claim (or lie exhibit): the same for
/// every depth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StallClaim {
    pub layout: Layout,
    pub checkpoint: Digest,
    pub target: Digest,
    pub game_id: u16,
    /// The claimant's mover byte.
    pub me: u8,
    /// Header slots the claim covers; a claim at depth `d` needs `d < w_max`.
    pub w_max: usize,
    /// The bytes `E2` takes at depth 1 (the initial state's word or words).
    pub initial_e2: Vec<u8>,
    /// Level-1 branching factor.
    pub k: u32,
    /// Check that slot `d + 1` holds nothing of the counterparty's (a stall
    /// proof). A lie exhibit sets this false: it proves slots `d - 1` and
    /// `d` only, with the counterparty's move at `d` in `E`.
    pub check_next: bool,
}

fn nibbles(bytes: &[u8]) -> Vec<u8> {
    bytes.iter().flat_map(|&b| [b >> 4, b & 15]).collect()
}

impl StallClaim {
    /// Preamble steps: one absorb per pair of state words (E, E2, and the
    /// depth word if separate), then the check step.
    pub fn preamble_steps(&self) -> usize {
        self.preamble_words().div_ceil(2) + 1
    }
    fn preamble_words(&self) -> usize {
        2 * self.layout.e_words() + usize::from(self.layout.dep_word.is_some())
    }
    pub fn n_steps(&self) -> usize {
        self.preamble_steps() + STEPS_PER_HEADER * self.w_max
    }
    pub fn other(&self) -> u8 {
        1 - self.me
    }
    /// The step index of header `h`'s first absorb.
    pub fn header_step(&self, h: usize) -> usize {
        self.preamble_steps() + (h - 1) * STEPS_PER_HEADER
    }
    fn gate(&self, cmp: Cmp, value: usize, then: Vec<Pred>) -> Pred {
        Pred::gate(self.layout.dep_nib, DEP_NIBBLES, cmp, value as u32, then)
    }
    /// The last slot whose header the claim checks: `d + 1` for a stall
    /// proof, `d` for a lie exhibit.
    fn last_slot(&self, d: usize) -> usize {
        if self.check_next { d + 1 } else { d }
    }
    /// The register word destinations of the preamble's data words, in order.
    fn preamble_dests(&self) -> Vec<usize> {
        let l = &self.layout;
        let mut v: Vec<usize> = (0..l.e_words()).map(|i| l.e_off / 8 + i).collect();
        v.extend((0..l.e_words()).map(|i| l.e2_off / 8 + i));
        v.extend(l.dep_word);
        v
    }
    /// The prover's data, in step order: the state words `e` (slot `d`),
    /// `e2` (slot `d - 1`) and the depth, then twelve word pairs per header
    /// slot, zeros for slots the chain does not reach.
    pub fn data(&self, depth: usize, headers: &[[u8; HEADER_BYTES]], e: &[u32], e2: &[u32]) -> ClaimData {
        assert!(headers.len() >= self.last_slot(depth), "a claim at depth {depth} needs {} headers", self.last_slot(depth));
        assert_eq!(e.len(), self.layout.e_words(), "E has {} words", self.layout.e_words());
        assert_eq!(e2.len(), self.layout.e_words(), "E2 has {} words", self.layout.e_words());
        let mut words: Vec<u32> = e.to_vec();
        words.extend_from_slice(e2);
        if self.layout.dep_word.is_some() {
            words.push(depth as u32);
        }
        let mut data: Vec<Vec<u32>> = words.chunks(2).map(|c| vec![c[0], c.get(1).copied().unwrap_or(0)]).collect();
        for h in 0..self.w_max {
            match headers.get(h) {
                Some(hdr) => data.extend(claim_blocks(hdr).iter().map(|w| w.to_vec())),
                None => data.extend(std::iter::repeat_n(vec![0u32, 0u32], HEADER_ABSORBS)),
            }
        }
        data
    }
    /// The start state: all zero (the checkpoint is a constant of step 1).
    pub fn start(&self) -> Vec<u32> {
        vec![0u32; self.layout.n_words]
    }
    /// The state words of a 40-byte (or 4-byte) state as claim words.
    pub fn e_words_of(&self, bytes: &[u8]) -> Vec<u32> {
        assert_eq!(bytes.len(), self.layout.e_nibbles / 2);
        words_from_bytes(bytes)
    }

    fn header_steps(&self, steps: &mut Vec<Step>, h: usize) {
        let data = || vec![Src::Data(0), Src::Data(1)];
        let cp = nibbles(&self.checkpoint);
        let nb = self.layout.nb();
        // links and proof of work are checked through the last slot: h <= d + 1
        // (stall proof) or h <= d (lie exhibit), i.e. DEP >= h - 1 or DEP >= h
        let through = if self.check_next { h - 1 } else { h };
        let link = |lo: usize, n: usize| -> Pred {
            if h == 1 {
                Pred::EqConst { off: nb, nibbles: cp[lo..lo + n].to_vec() }
            } else {
                self.gate(Cmp::Ge, through, vec![Pred::EqNibbles { a: nb, b: P_OFF + lo, n }])
            }
        };
        for b in 0..HEADER_ABSORBS {
            let init = if b == 0 { Init::Iv } else { Init::D };
            let mut step = Step::compress(&format!("h{h}_b{b}"), init, data());
            step = match b {
                0 => step.with_preds(vec![link(0, 16)]),
                1 => step.with_preds(vec![link(16, 16)]),
                2 => step.with_preds(vec![link(32, 8)]),
                HEAD_BLOCK..=10 => step.with_preds(self.head_preds(h, b)),
                _ => step,
            };
            steps.push(step);
        }
        steps.push(Step::compress(&format!("h{h}_pad"), Init::D, vec![Src::Const(0), Src::Const(0)]));
        let pow = Pred::LeTargetBe { off: D_OFF, target: nibbles(&self.target) };
        let pow = if h == 1 { pow } else { self.gate(Cmp::Ge, through, vec![pow]) };
        steps.push(Step::Simple { name: format!("h{h}_end"), preds: vec![pow], copies: vec![Copy { src: D_OFF, dst: P_OFF, n: 40 }] });
    }

    /// The mover of slot `d` (mine for a stall proof, the counterparty's
    /// for a lie exhibit) and of slot `d - 1`.
    fn movers(&self) -> (u8, u8) {
        if self.check_next { (self.me, self.other()) } else { (self.other(), self.me) }
    }

    /// The checks on head block `b` (5..=10) of slot `h`: on block 5 the
    /// content word (the slot-`d` mover's at `d`, the slot-`(d-1)` mover's
    /// at `d - 1`, not the counterparty's at `d + 1`); on every block, the
    /// part of `E` (at `d`) or `E2` (at `d - 1`) it carries.
    fn head_preds(&self, h: usize, b: usize) -> Vec<Pred> {
        let l = &self.layout;
        let nb = l.nb();
        let word0 = |mover: u8| nibbles(&SlotEntry::word0(self.game_id, h as u8, mover).to_be_bytes());
        let (at_d, at_prev) = self.movers();
        let mut at_d_preds = Vec::new();
        let mut at_prev_preds = Vec::new();
        if b == HEAD_BLOCK {
            at_d_preds.push(Pred::EqConst { off: nb, nibbles: word0(at_d) });
            at_prev_preds.push(Pred::EqConst { off: nb, nibbles: word0(at_prev) });
        }
        // the head nibbles this block carries, and E's place in the head
        let blk = (b - HEAD_BLOCK) * 16;
        let (e_lo, e_hi) = (2 * l.head_e_at, 2 * l.head_e_at + l.e_nibbles);
        let lo = blk.max(e_lo);
        let hi = (blk + 16).min(e_hi);
        if lo < hi {
            let n = hi - lo;
            at_d_preds.push(Pred::EqNibbles { a: nb + (lo - blk), b: l.e_off + (lo - e_lo), n });
            at_prev_preds.push(Pred::EqNibbles { a: nb + (lo - blk), b: l.e2_off + (lo - e_lo), n });
        }
        let mut v = Vec::new();
        if !at_d_preds.is_empty() {
            v.push(self.gate(Cmp::Eq, h, at_d_preds));
        }
        if h + 1 < self.w_max && !at_prev_preds.is_empty() {
            v.push(self.gate(Cmp::Eq, h + 1, at_prev_preds));
        }
        if b == HEAD_BLOCK && h >= 2 && self.check_next {
            v.push(self.gate(Cmp::Eq, h - 1, vec![Pred::NeConst { off: nb, nibbles: word0(self.other()) }]));
        }
        v
    }

    pub fn spec(&self) -> ClaimSpec {
        assert!(self.w_max >= 2 && self.w_max <= 255, "w_max in 2..=255");
        let l = &self.layout;
        let nb = l.nb();
        let data = || vec![Src::Data(0), Src::Data(1)];
        let mut steps = Vec::new();
        // the preamble: absorb the state words and copy them into place
        let dests = self.preamble_dests();
        for (k, pair) in dests.chunks(2).enumerate() {
            let mut copies = vec![Copy { src: nb, dst: 8 * pair[0], n: 8 }];
            let mut preds = Vec::new();
            if let Some(&w) = pair.get(1) {
                copies.push(Copy { src: nb + 8, dst: 8 * w, n: 8 });
            } else {
                preds.push(Pred::EqConst { off: nb + 8, nibbles: vec![0; 8] });
            }
            // a separate depth word carries only the depth number
            for (j, &w) in pair.iter().enumerate() {
                if Some(w) == l.dep_word {
                    preds.push(Pred::EqConst { off: nb + 8 * j, nibbles: vec![0; 6] });
                }
            }
            steps.push(Step::compress(&format!("pre_{k}"), Init::Iv, data()).with_preds(preds).with_copies(copies));
        }
        steps.push(Step::check(
            "pre_chk",
            vec![
                Pred::InRange { off: l.dep_nib, n: DEP_NIBBLES, lo: 1, hi: self.w_max as u32 },
                self.gate(Cmp::Eq, 1, vec![Pred::EqConst { off: l.e2_off, nibbles: nibbles(&self.initial_e2) }]),
            ],
        ));
        assert_eq!(steps.len(), self.preamble_steps());
        for h in 1..=self.w_max {
            self.header_steps(&mut steps, h);
        }
        assert_eq!(steps.len(), self.n_steps());
        let mut n = 1;
        while n < steps.len() {
            n *= self.k as usize;
        }
        while steps.len() < n {
            steps.push(Step::nop());
        }
        ClaimSpec { n_words: l.n_words, start: self.start(), steps, k: self.k, inner: true, hash: HashKind::N4Bit, flat_inner: true }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slot::STATE_BITS;
    use crate::{genesis, pow_target, ChainClient, Miner, CHUNK};

    const GAME: u16 = 7;

    /// A tic-tac-toe entry for `game` at `depth` by `mover` (signatures are
    /// not the stall claim's business: zeros).
    fn entry(game: u16, depth: u8, mover: u8, mv: u8, state: u32) -> Vec<u8> {
        SlotEntry { game_id: game, depth, mover, mv, state, sigs: vec![[0u8; CHUNK]; STATE_BITS] }.encode()
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

    fn claim(cp: Digest, me: u8, w_max: usize) -> StallClaim {
        StallClaim { layout: Layout::tictactoe(), checkpoint: cp, target: pow_target(), game_id: GAME, me, w_max, initial_e2: SlotEntry::word1(0, 0x100).to_be_bytes().to_vec(), k: 4, check_next: true }
    }

    /// A game of `n` moves (mover alternates, 0 first), then `tail` more
    /// blocks holding what `tail` says; the `(move, state)` words.
    fn game_chain(n: usize, tail: &[Vec<u8>]) -> (Digest, Vec<[u8; HEADER_BYTES]>, Vec<u32>) {
        let mut entries = Vec::new();
        let mut words = Vec::new();
        for d in 1..=n {
            let state = 0x1000 + d as u32;
            entries.push(entry(GAME, d as u8, ((d + 1) % 2) as u8, d as u8, state));
            words.push(SlotEntry::word1(d as u8, state));
        }
        entries.extend_from_slice(tail);
        let (cp, headers) = chain(&entries);
        (cp, headers, words)
    }

    fn w(x: u32) -> Vec<u32> {
        vec![x]
    }

    #[test]
    fn one_spec_serves_every_depth() {
        let w_max = 9;
        let (cp, headers, words) = game_chain(8, &[vec![], vec![0xAB; 30], vec![0xCD; 5]]);
        for me in 0..2u8 {
            let c = claim(cp, me, w_max);
            let spec = c.spec();
            for d in 1..w_max {
                let mover = ((d + 1) % 2) as u8;
                if mover != me {
                    continue;
                }
                let e2 = if d >= 2 { words[d - 2] } else { 0x100 };
                let data = c.data(d, &headers, &w(words[d - 1]), &w(e2));
                let (end, ok) = spec.segment_reference(0, spec.steps.len(), &spec.start, &data);
                assert_eq!(ok, d == 8, "role {me} depth {d}");
                assert_eq!(end[10], words[d - 1]);
                assert_eq!(end[11], e2);
                assert_eq!(end[12], d as u32);
            }
        }
    }

    #[test]
    fn stalls_and_lies() {
        let w_max = 9;
        let (cp, headers, words) = game_chain(5, &[vec![]]);
        let c = claim(cp, 0, w_max);
        let spec = c.spec();
        let honest = c.data(5, &headers, &w(words[4]), &w(words[3]));
        assert!(spec.valid(&honest), "mover 1 stalled at slot 6");
        let c1 = claim(cp, 1, w_max);
        assert!(!c1.spec().valid(&c1.data(5, &headers, &w(words[4]), &w(words[3]))));
        assert!(!spec.valid(&c.data(5, &headers, &w(words[4] ^ 1), &w(words[3]))));
        assert!(!spec.valid(&c.data(5, &headers, &w(words[4]), &w(words[3] ^ 1))));
        assert!(!spec.valid(&c.data(3, &headers, &w(words[2]), &w(words[1]))), "at depth 3 slot 4 holds the other's move");
        let mut d0 = honest.clone();
        d0[1] = vec![0, 0];
        assert!(!spec.valid(&d0));
        let mut dmax = honest.clone();
        dmax[1] = vec![w_max as u32, 0];
        assert!(!spec.valid(&dmax));
        // a forged header at slot 6 (wrong link) and one whose nonce fails the target
        let step0 = c.header_step(6);
        let mut forged = honest.clone();
        forged[step0][0] ^= 1;
        assert!(!spec.valid(&forged));
        let mut h6 = headers[5];
        let mut flip = 0u32;
        loop {
            h6[HEADER_BYTES - 1] ^= 1 << flip;
            if !crate::Header(h6).meets_pow() {
                break;
            }
            flip += 1;
        }
        let mut nopow = honest.clone();
        for (k, wds) in claim_blocks(&h6).iter().enumerate() {
            nopow[step0 + k] = wds.to_vec();
        }
        assert!(!spec.valid(&nopow));
        // junk beyond slot d+1 is ignored
        let mut junk = honest.clone();
        for step in &mut junk[c.header_step(7)..] {
            step[0] = 0xdead_beef;
        }
        assert!(spec.valid(&junk));
        // slot 6 holding another game's entry is still a stall
        let (cp2, headers2, words2) = game_chain(5, &[entry(GAME + 1, 6, 1, 1, 1)]);
        let c2 = claim(cp2, 0, w_max);
        assert!(c2.spec().valid(&c2.data(5, &headers2, &w(words2[4]), &w(words2[3]))));
        // depth 1: the prior must be the initial word
        let (cp3, headers3, words3) = game_chain(1, &[vec![]]);
        let c3 = claim(cp3, 0, w_max);
        assert!(c3.spec().valid(&c3.data(1, &headers3, &w(words3[0]), &w(0x100))));
        assert!(!c3.spec().valid(&c3.data(1, &headers3, &w(words3[0]), &w(0x101))));
    }

    #[test]
    fn lie_exhibit_reads_the_other_move() {
        let w_max = 9;
        let (cp, headers, words) = game_chain(5, &[vec![]]);
        let lie = StallClaim { check_next: false, ..claim(cp, 0, w_max) };
        let spec = lie.spec();
        assert!(spec.valid(&lie.data(4, &headers, &w(words[3]), &w(words[2]))));
        assert!(spec.valid(&lie.data(4, &headers[..4], &w(words[3]), &w(words[2]))));
        assert!(spec.valid(&lie.data(2, &headers, &w(words[1]), &w(words[0]))));
        assert!(!spec.valid(&lie.data(4, &headers, &w(words[3] ^ 1), &w(words[2]))));
        assert!(!spec.valid(&lie.data(3, &headers, &w(words[2]), &w(words[1]))), "slot 3 is my own move");
        let stall = claim(cp, 0, w_max);
        assert!(!stall.spec().valid(&stall.data(4, &headers, &w(words[3]), &w(words[2]))));
    }

    /// The chess layout: a 40-byte state in the head, the depth inside it.
    #[test]
    fn chess_layout_binds_a_whole_state() {
        let w_max = 9;
        // entries: content(8) || E(40) with E's byte 38 the depth
        let state = |d: u8, mover: u8, seed: u8| -> Vec<u8> {
            let mut e = vec![0u8; 40];
            for (i, b) in e.iter_mut().enumerate().take(36) {
                *b = seed.wrapping_mul(31).wrapping_add(i as u8);
            }
            e[36] = 12;
            e[37] = 28;
            e[39] = d;
            let mut entry = SlotEntry::word0(GAME, d, mover).to_be_bytes().to_vec();
            entry.extend_from_slice(&[0u8; 4]);
            entry.extend_from_slice(&e);
            entry
        };
        let initial = vec![0u8; 40];
        let entries: Vec<Vec<u8>> = (1..=5u8).map(|d| state(d, (d + 1) % 2, d)).collect();
        let mut all = entries.clone();
        all.push(vec![]);
        let (cp, headers) = chain(&all);
        let e_of = |d: usize| entries[d - 1][8..48].to_vec();
        let c = StallClaim { layout: Layout::chess(), checkpoint: cp, target: pow_target(), game_id: GAME, me: 0, w_max, initial_e2: initial.clone(), k: 2, check_next: true };
        let spec = c.spec();
        assert_eq!(spec.n_words, 30);
        let data = c.data(5, &headers, &c.e_words_of(&e_of(5)), &c.e_words_of(&e_of(4)));
        let (end, ok) = spec.segment_reference(0, spec.steps.len(), &spec.start, &data);
        assert!(ok, "mover 1 stalled at slot 6");
        assert_eq!(&end[10..20], &c.e_words_of(&e_of(5))[..]);
        assert_eq!(&end[20..30], &c.e_words_of(&e_of(4))[..]);
        // a state whose depth byte disagrees with the slot fails the head check
        let mut wrong = e_of(5);
        wrong[39] = 4;
        assert!(!spec.valid(&c.data(4, &headers, &c.e_words_of(&wrong), &c.e_words_of(&e_of(3)))));
        // a corrupted square fails
        let mut bad = e_of(5);
        bad[7] ^= 0x10;
        assert!(!spec.valid(&c.data(5, &headers, &c.e_words_of(&bad), &c.e_words_of(&e_of(4)))));
        // depth 1 against the initial state
        let (cp1, headers1) = chain(&[state(1, 0, 9), vec![]]);
        let c1 = StallClaim { checkpoint: cp1, ..c.clone() };
        let e1 = state(1, 0, 9)[8..48].to_vec();
        assert!(c1.spec().valid(&c1.data(1, &headers1, &c1.e_words_of(&e1), &c1.e_words_of(&initial))));
        let mut not_initial = initial.clone();
        not_initial[0] = 1;
        assert!(!c1.spec().valid(&c1.data(1, &headers1, &c1.e_words_of(&e1), &c1.e_words_of(&not_initial))));
        // the lie exhibit variant
        let lie = StallClaim { check_next: false, ..c.clone() };
        assert!(lie.spec().valid(&lie.data(4, &headers, &lie.e_words_of(&e_of(4)), &lie.e_words_of(&e_of(3)))));
    }

    #[test]
    fn measure() {
        for (name, layout, w_max, k) in [("ttt", Layout::tictactoe(), 10usize, 4u32), ("ttt", Layout::tictactoe(), 200, 4), ("chess", Layout::chess(), 20, 2), ("chess", Layout::chess(), 200, 2)] {
            let c = StallClaim { layout, checkpoint: [0; 20], target: pow_target(), game_id: GAME, me: 0, w_max, initial_e2: vec![0; 4], k, check_next: true };
            let c = StallClaim { initial_e2: vec![0; c.layout.e_nibbles / 2], ..c };
            let spec = c.spec();
            println!("MEASURE stall claim {name} W_max={w_max} k={k}: {} steps -> {} padded, {} rounds, {} words", c.n_steps(), spec.steps.len(), spec.rounds(), spec.n_words);
        }
    }
}
