//! The SIGNATURE EXHIBIT (docs/DECISIONS.md D31): "slot `d` holds the
//! counterparty's entry, but the preimage it publishes for signed bit `i`
//! does not open the counterparty's depth-`d` commitment for the bit the
//! entry's head states". One program for every depth and every bit, like
//! the stall claim (`stall.rs`, D28), whose header loop it shares in
//! shape.
//!
//! Why it exists: the stall claim reads slots from header heads and checks
//! no signature. A slot whose head names the counterparty is "held" as far
//! as a stall proof can tell, even if its preimages are garbage (a miner's
//! fabrication, or the mover's own). The victim exhibits that: this claim
//! proves the entry is in the slot (its stream hashes to the header's
//! root), what one of its chunk digests is, what the counterparty's
//! commitment for that bit is (a leaf of a per-depth commitment tree whose
//! root is a constant of the claim), and that the two differ.
//!
//! The claim, in register terms (22 words):
//!
//! - `D` (0..40): the hash state.
//! - `X` (40..80): the exhibited chunk digest as the stream carries it;
//!   after the stream phase this is `P`, the previous header digest.
//! - `R` (80..120): the stream's root, copied from `D` after the stream.
//! - `C` (120..160): the commitment the exhibited bit should open; during
//!   the tree phase the running node digest.
//! - `J` (word 20): the leaf index `2 i + b`, three nibbles.
//! - `DEP` (word 21): the depth, two nibbles.
//!
//! Phases:
//!
//! 1. The preamble absorbs `X`, `C`, `J` and `DEP` as data and copies them
//!    into place; `pre_chk` requires `X != C`, the depth in range and one
//!    of the counterparty's, the index in range.
//! 2. The entry stream (`stream_bytes` for the game's chunk count) is
//!    absorbed; at chunk slot `chunk_offset + i` the block data must equal
//!    `X`, gated on `J = 2 i` or `2 i + 1`. Then the pad block and `D -> R`.
//! 3. The commitment tree: 16-ary, `levels` deep, leaves `c[i][b]` at index
//!    `2 i + b`. Each level absorbs 16 children (320 bytes, 40 blocks); the
//!    child at nibble `L` of `J` must equal `C`; after the level's pad
//!    block `D -> C`, and after the last level `D` must equal the root
//!    constant of the depth `DEP` names.
//! 4. The headers, as the lie exhibit's loop (links and proof of work
//!    through `DEP`): at `DEP` the header's root must equal `R` and its
//!    head's content word must be the counterparty's at that depth; at
//!    `DEP - 1` the head's content word must be mine. The head's bit `i`
//!    must agree with `J`'s low bit, checked on the block that carries it
//!    (`places` maps signed bits to head bytes).
//!
//! Padded to a power of `k` with no-ops. The prover states nothing but
//! the outcome code and the end state on Bitcoin (the claim is `wots_only`);
//! the judge reads `J` and `DEP` from the end state and recomputes.

use lngap_contract::claim::{words_from_bytes, ClaimData, ClaimSpec, Cmp, Copy, HashKind, Init, Pred, Src, Step};
use lngap_n4bit::{claim_blocks, hash_claim as hash, Digest, DIGEST_BYTES};

use crate::slot::SlotEntry;
use crate::stall::STEPS_PER_HEADER;
use crate::{entry_stream, stream_bytes, HEADER_ABSORBS, HEADER_BYTES};

pub const N_WORDS: usize = 22;
pub const D_OFF: usize = 0;
pub const X_OFF: usize = 40;
pub const P_OFF: usize = 40;
pub const R_OFF: usize = 80;
pub const C_OFF: usize = 120;
pub const J_WORD: usize = 20;
pub const DEP_WORD: usize = 21;
/// `J`'s three nibbles (the low end of its word).
pub const J_OFF: usize = 8 * J_WORD + 5;
pub const J_NIBBLES: usize = 3;
/// `DEP`'s two nibbles.
pub const DEP_OFF: usize = 8 * DEP_WORD + 6;
pub const DEP_NIBBLES: usize = 2;
/// Nibbles of one tree node's children (16 digests).
const NODE_NIBBLES: usize = 16 * 2 * DIGEST_BYTES;
const NODE_BLOCKS: usize = NODE_NIBBLES / 16;
const HEAD_BLOCK: usize = 5;

/// Where a signed bit sits in the 48-byte head: byte and bit (least
/// significant first).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Place {
    pub byte: usize,
    pub bit: u8,
}

/// The constants of a role's signature exhibit: the same for every depth
/// and bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SigExhibit {
    pub checkpoint: Digest,
    pub target: Digest,
    pub game_id: u16,
    /// The victim's (claimant's) mover byte.
    pub me: u8,
    pub w_max: usize,
    pub k: u32,
    /// Chunk slots of an entry's stream (the game's entry length).
    pub n_chunks: usize,
    /// The chunk slot of signed bit 0's preimage.
    pub chunk_offset: usize,
    /// Signed bit `i`'s place in the head.
    pub places: Vec<Place>,
    /// The counterparty's commitment tree root at depth `d` (index `d`,
    /// `None` at depths where it does not move or that the claim does not
    /// cover).
    pub roots: Vec<Option<Digest>>,
    /// Tree levels (16-ary).
    pub levels: usize,
}

fn nibbles(bytes: &[u8]) -> Vec<u8> {
    bytes.iter().flat_map(|&b| [b >> 4, b & 15]).collect()
}

fn nib3(v: usize) -> Vec<u8> {
    vec![((v >> 8) & 15) as u8, ((v >> 4) & 15) as u8, (v & 15) as u8]
}

/// Tree levels for `n_leaves` leaves.
pub fn levels_for(n_leaves: usize) -> usize {
    let mut l = 1;
    while 16usize.pow(l as u32) < n_leaves {
        l += 1;
    }
    l
}

/// A 16-ary commitment tree over a depth's `(c0, c1)` pairs, leaf `2 i + b`
/// holding `c[i][b]`, zero digests beyond; a node is the claim-native hash
/// of its 16 children.
#[derive(Clone, Debug)]
pub struct CommitTree {
    /// `levels[0]` are the leaves, `levels[L]` the nodes above.
    pub levels: Vec<Vec<Digest>>,
}

impl CommitTree {
    pub fn new(commits: &[[Digest; 2]], levels: usize) -> CommitTree {
        let mut leaves: Vec<Digest> = commits.iter().flat_map(|c| [c[0], c[1]]).collect();
        leaves.resize(16usize.pow(levels as u32), [0u8; DIGEST_BYTES]);
        let mut out = vec![leaves];
        for _ in 0..levels {
            let prev = out.last().unwrap();
            let next: Vec<Digest> = prev.chunks(16).map(|c| hash(&c.concat())).collect();
            out.push(next);
        }
        CommitTree { levels: out }
    }
    pub fn root(&self) -> Digest {
        self.levels.last().unwrap()[0]
    }
    pub fn leaf(&self, j: usize) -> Digest {
        self.levels[0][j]
    }
    /// The 16 children of the node on leaf `j`'s path at each level, bottom
    /// up: the prover's data for the tree phase.
    pub fn path(&self, j: usize) -> Vec<Vec<Digest>> {
        (0..self.levels.len() - 1).map(|l| self.levels[l][(j >> (4 * l)) & !15..][..16].to_vec()).collect()
    }
}

impl SigExhibit {
    pub fn other(&self) -> u8 {
        1 - self.me
    }
    pub fn n_bits(&self) -> usize {
        self.places.len()
    }
    pub fn stream_blocks(&self) -> usize {
        stream_bytes(self.n_chunks) / 8
    }
    /// Preamble: six absorbs (`X`, `C`, `J`, `DEP`), the check.
    pub const PREAMBLE_STEPS: usize = 7;
    /// The step index of the stream's first absorb.
    pub fn stream_step(&self) -> usize {
        Self::PREAMBLE_STEPS
    }
    /// The step index of tree level `l`'s first absorb.
    pub fn tree_step(&self, l: usize) -> usize {
        self.stream_step() + self.stream_blocks() + 2 + l * (NODE_BLOCKS + 2)
    }
    /// The step index of header `h`'s first absorb.
    pub fn header_step(&self, h: usize) -> usize {
        self.tree_step(self.levels) + (h - 1) * STEPS_PER_HEADER
    }
    pub fn n_steps(&self) -> usize {
        self.header_step(self.w_max + 1)
    }
    fn dep_gate(&self, cmp: Cmp, value: usize, then: Vec<Pred>) -> Pred {
        Pred::gate(DEP_OFF, DEP_NIBBLES, cmp, value as u32, then)
    }
    fn j_gate(&self, value: usize, then: Vec<Pred>) -> Pred {
        Pred::gate(J_OFF, J_NIBBLES, Cmp::Eq, value as u32, then)
    }

    fn preamble(&self, steps: &mut Vec<Step>) {
        let nb = 8 * N_WORDS;
        let data = || vec![Src::Data(0), Src::Data(1)];
        let dests: Vec<usize> = (X_OFF / 8..X_OFF / 8 + 5).chain(C_OFF / 8..C_OFF / 8 + 5).chain([J_WORD, DEP_WORD]).collect();
        for (k, pair) in dests.chunks(2).enumerate() {
            let copies: Vec<Copy> = pair.iter().enumerate().map(|(j, &w)| Copy { src: nb + 8 * j, dst: 8 * w, n: 8 }).collect();
            let mut preds = Vec::new();
            for (j, &w) in pair.iter().enumerate() {
                if w == J_WORD {
                    preds.push(Pred::EqConst { off: nb + 8 * j, nibbles: vec![0; 8 - J_NIBBLES] });
                }
                if w == DEP_WORD {
                    preds.push(Pred::EqConst { off: nb + 8 * j, nibbles: vec![0; 8 - DEP_NIBBLES] });
                }
            }
            steps.push(Step::compress(&format!("pre_{k}"), Init::Iv, data()).with_preds(preds).with_copies(copies));
        }
        let mut preds = vec![
            Pred::InRange { off: DEP_OFF, n: DEP_NIBBLES, lo: 1, hi: self.w_max as u32 },
            Pred::InRange { off: J_OFF, n: J_NIBBLES, lo: 0, hi: 2 * self.n_bits() as u32 },
            Pred::NeNibbles { a: X_OFF, b: C_OFF, n: 40 },
        ];
        for d in 1..self.w_max {
            if self.roots.get(d).copied().flatten().is_none() {
                preds.push(Pred::NeConst { off: DEP_OFF, nibbles: vec![(d >> 4) as u8, (d & 15) as u8] });
            }
        }
        steps.push(Step::check("pre_chk", preds));
    }

    fn stream_steps(&self, steps: &mut Vec<Step>) {
        let nb = 8 * N_WORDS;
        let data = || vec![Src::Data(0), Src::Data(1)];
        for t in 0..self.stream_blocks() {
            let init = if t == 0 { Init::Iv } else { Init::D };
            let mut preds = Vec::new();
            if t >= 1 {
                let (c, part) = ((t - 1) / 3, (t - 1) % 3);
                if c >= self.chunk_offset && c - self.chunk_offset < self.n_bits() {
                    let i = c - self.chunk_offset;
                    let n = if part == 2 { 8 } else { 16 };
                    let eq = Pred::EqNibbles { a: nb, b: X_OFF + 16 * part, n };
                    preds.push(self.j_gate(2 * i, vec![eq.clone()]));
                    preds.push(self.j_gate(2 * i + 1, vec![eq]));
                }
            }
            steps.push(Step::compress(&format!("s{t}"), init, data()).with_preds(preds));
        }
        steps.push(Step::compress("s_pad", Init::D, vec![Src::Const(0), Src::Const(0)]));
        steps.push(Step::copy("s_root", vec![Copy { src: D_OFF, dst: R_OFF, n: 40 }]));
    }

    fn tree_steps(&self, steps: &mut Vec<Step>) {
        let nb = 8 * N_WORDS;
        let data = || vec![Src::Data(0), Src::Data(1)];
        for l in 0..self.levels {
            let j_nib = J_OFF + J_NIBBLES - 1 - l;
            for t in 0..NODE_BLOCKS {
                let init = if t == 0 { Init::Iv } else { Init::D };
                let mut preds = Vec::new();
                let (blo, bhi) = (16 * t, 16 * t + 16);
                for v in 0..16 {
                    let (clo, chi) = (40 * v, 40 * v + 40);
                    let (lo, hi) = (blo.max(clo), bhi.min(chi));
                    if lo < hi {
                        preds.push(Pred::gate(j_nib, 1, Cmp::Eq, v as u32, vec![Pred::EqNibbles { a: nb + lo - blo, b: C_OFF + lo - clo, n: hi - lo }]));
                    }
                }
                steps.push(Step::compress(&format!("t{l}_b{t}"), init, data()).with_preds(preds));
            }
            steps.push(Step::compress(&format!("t{l}_pad"), Init::D, vec![Src::Const(0), Src::Const(0)]));
            if l + 1 < self.levels {
                // a level-specific (always true) check keeps the levels' copy
                // leaves distinct scripts: `J`'s high nibbles are zero
                let mark = Pred::EqConst { off: 8 * J_WORD + l, nibbles: vec![0] };
                steps.push(Step::Simple { name: format!("t{l}_up"), preds: vec![mark], copies: vec![Copy { src: D_OFF, dst: C_OFF, n: 40 }] });
            } else {
                let mut preds = Vec::new();
                for d in 1..self.w_max {
                    if let Some(root) = self.roots.get(d).copied().flatten() {
                        preds.push(self.dep_gate(Cmp::Eq, d, vec![Pred::EqConst { off: D_OFF, nibbles: nibbles(&root) }]));
                    }
                }
                steps.push(Step::check("t_root", preds));
            }
        }
    }

    /// The bit-binding predicates for head block `b` of a header at depth
    /// `DEP` (the gate on `DEP` is the caller's).
    fn bit_preds(&self, b: usize) -> Vec<Pred> {
        let nb = 8 * N_WORDS;
        let mut v = Vec::new();
        for (i, p) in self.places.iter().enumerate() {
            if HEAD_BLOCK + p.byte / 8 != b {
                continue;
            }
            let q = 2 * (p.byte % 8) + usize::from(p.bit < 4);
            let bit = p.bit % 4;
            let eq = Pred::EqConstBit { nib: nb + q, bit, off: J_OFF, if0: nib3(2 * i), if1: nib3(2 * i + 1) };
            v.push(self.j_gate(2 * i, vec![eq.clone()]));
            v.push(self.j_gate(2 * i + 1, vec![eq]));
        }
        v
    }

    fn header_steps(&self, steps: &mut Vec<Step>, h: usize) {
        let nb = 8 * N_WORDS;
        let data = || vec![Src::Data(0), Src::Data(1)];
        let cp = nibbles(&self.checkpoint);
        let link = |lo: usize, n: usize| -> Pred {
            if h == 1 {
                Pred::EqConst { off: nb, nibbles: cp[lo..lo + n].to_vec() }
            } else {
                self.dep_gate(Cmp::Ge, h, vec![Pred::EqNibbles { a: nb, b: P_OFF + lo, n }])
            }
        };
        let word0 = |mover: u8| nibbles(&SlotEntry::word0(self.game_id, h as u8, mover).to_be_bytes());
        for b in 0..HEADER_ABSORBS {
            let init = if b == 0 { Init::Iv } else { Init::D };
            let mut preds = Vec::new();
            match b {
                0 => preds.push(link(0, 16)),
                1 => preds.push(link(16, 16)),
                2 => {
                    preds.push(link(32, 8));
                    preds.push(self.dep_gate(Cmp::Eq, h, vec![Pred::EqNibbles { a: nb + 8, b: R_OFF, n: 8 }]));
                }
                3 => preds.push(self.dep_gate(Cmp::Eq, h, vec![Pred::EqNibbles { a: nb, b: R_OFF + 8, n: 16 }])),
                4 => preds.push(self.dep_gate(Cmp::Eq, h, vec![Pred::EqNibbles { a: nb, b: R_OFF + 24, n: 16 }])),
                _ => {}
            }
            if (HEAD_BLOCK..=10).contains(&b) {
                let mut at_d = Vec::new();
                if b == HEAD_BLOCK {
                    at_d.push(Pred::EqConst { off: nb, nibbles: word0(self.other()) });
                    if h + 1 < self.w_max {
                        preds.push(self.dep_gate(Cmp::Eq, h + 1, vec![Pred::EqConst { off: nb, nibbles: word0(self.me) }]));
                    }
                }
                at_d.extend(self.bit_preds(b));
                if !at_d.is_empty() {
                    preds.push(self.dep_gate(Cmp::Eq, h, at_d));
                }
            }
            steps.push(Step::compress(&format!("h{h}_b{b}"), init, data()).with_preds(preds));
        }
        steps.push(Step::compress(&format!("h{h}_pad"), Init::D, vec![Src::Const(0), Src::Const(0)]));
        let pow = Pred::LeTargetBe { off: D_OFF, target: nibbles(&self.target) };
        let pow = if h == 1 { pow } else { self.dep_gate(Cmp::Ge, h, vec![pow]) };
        steps.push(Step::Simple { name: format!("h{h}_end"), preds: vec![pow], copies: vec![Copy { src: D_OFF, dst: P_OFF, n: 40 }] });
    }

    pub fn spec(&self) -> ClaimSpec {
        assert!(self.w_max >= 2 && self.w_max <= 255, "w_max in 2..=255");
        assert!(2 * self.n_bits() <= 16usize.pow(self.levels as u32), "the tree holds every commitment");
        assert!(self.chunk_offset + self.n_bits() <= self.n_chunks, "the stream holds every preimage");
        let mut steps = Vec::new();
        self.preamble(&mut steps);
        assert_eq!(steps.len(), Self::PREAMBLE_STEPS);
        self.stream_steps(&mut steps);
        assert_eq!(steps.len(), self.tree_step(0));
        self.tree_steps(&mut steps);
        assert_eq!(steps.len(), self.header_step(1));
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
        ClaimSpec { n_words: N_WORDS, start: self.start(), steps, k: self.k, inner: true, hash: HashKind::N4Bit, flat_inner: true }
    }
    pub fn start(&self) -> Vec<u32> {
        vec![0u32; N_WORDS]
    }

    /// The prover's data for an exhibit at `depth` of signed bit `i` with
    /// head bit `b`: the chunk digest the stream carries, the commitment
    /// `c[i][b]`, the index and depth; the entry's stream; the tree path;
    /// the headers (zeros beyond the chain).
    pub fn data(&self, depth: usize, i: usize, b: bool, headers: &[[u8; HEADER_BYTES]], entry: &[u8], commits: &[[Digest; 2]]) -> ClaimData {
        assert!(headers.len() >= depth, "an exhibit at depth {depth} needs {depth} headers");
        let stream = entry_stream(entry);
        assert_eq!(stream.len(), stream_bytes(self.n_chunks), "the entry has {} chunks", self.n_chunks);
        let c = self.chunk_offset + i;
        let x = &stream[8 + 24 * c..8 + 24 * c + DIGEST_BYTES];
        let tree = CommitTree::new(commits, self.levels);
        let j = 2 * i + usize::from(b);
        let mut words: Vec<u32> = words_from_bytes(x);
        words.extend(words_from_bytes(&tree.leaf(j)));
        words.push(j as u32);
        words.push(depth as u32);
        let mut data: Vec<Vec<u32>> = words.chunks(2).map(|c| c.to_vec()).collect();
        data.extend(claim_blocks(&stream).iter().map(|w| w.to_vec()));
        for level in tree.path(j) {
            data.extend(claim_blocks(&level.concat()).iter().map(|w| w.to_vec()));
        }
        for h in 0..self.w_max {
            match headers.get(h) {
                Some(hdr) => data.extend(claim_blocks(hdr).iter().map(|w| w.to_vec())),
                None => data.extend(std::iter::repeat_n(vec![0u32, 0u32], HEADER_ABSORBS)),
            }
        }
        data
    }

    /// The first signed bit whose published preimage does not open the
    /// mover's commitment for the bit the head states, with that bit.
    pub fn find_garbage(&self, entry: &[u8], head_bits: &[bool], commits: &[[Digest; 2]]) -> Option<(usize, bool)> {
        let stream = entry_stream(entry);
        (0..self.n_bits()).find_map(|i| {
            let c = self.chunk_offset + i;
            let x = &stream[8 + 24 * c..8 + 24 * c + DIGEST_BYTES];
            let b = head_bits[i];
            (x != commits[i][usize::from(b)]).then_some((i, b))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slot::STATE_BITS;
    use crate::{genesis, pow_target, ChainClient, Miner, CHUNK};

    const GAME: u16 = 9;
    const W_MAX: usize = 6;

    /// Tic-tac-toe places: state bit `i` is bit `i % 8` of head byte `7 - i / 8`.
    fn ttt_places() -> Vec<Place> {
        (0..STATE_BITS).map(|i| Place { byte: 7 - i / 8, bit: (i % 8) as u8 }).collect()
    }

    fn preimage(d: u8, i: usize, b: bool) -> [u8; CHUNK] {
        let mut p = [0u8; CHUNK];
        p[0] = d;
        p[1] = i as u8;
        p[2] = u8::from(b);
        p[3] = 0xA5;
        p
    }
    fn commits(d: u8) -> Vec<[Digest; 2]> {
        (0..STATE_BITS).map(|i| [hash(&preimage(d, i, false)), hash(&preimage(d, i, true))]).collect()
    }
    fn signed_entry(d: u8, mover: u8, mv: u8, state: u32) -> Vec<u8> {
        let sigs = (0..STATE_BITS).map(|i| preimage(d, i, (state >> i) & 1 == 1)).collect();
        SlotEntry { game_id: GAME, depth: d, mover, mv, state, sigs }.encode()
    }
    fn chain(entries: &[Vec<u8>]) -> (Digest, Vec<[u8; HEADER_BYTES]>) {
        let g = genesis();
        let mut miner = Miner::new(g.header.digest(), 0);
        let mut client = ChainClient::from_checkpoint(0, g.header.digest());
        for e in entries {
            miner.submit(e.clone());
            client.verify_and_append(&miner.mine_next().unwrap()).unwrap();
        }
        (g.header.digest(), client.chain_headers().iter().map(|h| h.0).collect())
    }
    /// The victim is mover 0 (odd depths); the liar mover 1 (even depths).
    fn exhibit(cp: Digest) -> SigExhibit {
        let levels = levels_for(2 * STATE_BITS);
        let roots = (0..W_MAX).map(|d| (d >= 1 && d % 2 == 0).then(|| CommitTree::new(&commits(d as u8), levels).root())).collect();
        SigExhibit { checkpoint: cp, target: pow_target(), game_id: GAME, me: 0, w_max: W_MAX, k: 2, n_chunks: STATE_BITS, chunk_offset: 0, places: ttt_places(), roots, levels }
    }
    fn state_bits(state: u32) -> Vec<bool> {
        (0..STATE_BITS).map(|i| (state >> i) & 1 == 1).collect()
    }
    fn failing_step(spec: &ClaimSpec, data: &ClaimData) -> Option<String> {
        let mut st = spec.start.clone();
        for (i, step) in spec.steps.iter().enumerate() {
            let (next, ok) = spec.apply(i, step, &st, spec.data_for(data, i));
            if !ok {
                return Some(step.name());
            }
            st = next;
        }
        None
    }

    #[test]
    fn tree_paths_hash_to_the_root() {
        let c = commits(2);
        let levels = levels_for(2 * STATE_BITS);
        assert_eq!(levels, 2);
        let t = CommitTree::new(&c, levels);
        for j in [0, 1, 17, 41] {
            let mut cur = t.leaf(j);
            for (l, children) in t.path(j).iter().enumerate() {
                assert_eq!(children[(j >> (4 * l)) & 15], cur);
                cur = hash(&children.concat());
            }
            assert_eq!(cur, t.root());
        }
        assert_eq!(t.leaf(2 * 8 + 1), c[8][1]);
    }

    #[test]
    fn a_garbage_preimage_is_exhibited_and_a_sound_one_is_not() {
        let e1 = signed_entry(1, 0, 4, 0x000010);
        let state2 = 0x000210;
        let mut e2 = signed_entry(2, 1, 5, state2);
        // bit 9 of the state is 1; replace its preimage with garbage
        e2[8 + 9 * CHUNK] ^= 0xFF;
        let e3 = signed_entry(3, 0, 6, 0x000211);
        let (cp, headers) = chain(&[e1, e2.clone(), e3]);
        let x = exhibit(cp);
        let spec = x.spec();
        assert_eq!(spec.n_words, N_WORDS);
        let c2 = commits(2);
        assert_eq!(x.find_garbage(&e2, &state_bits(state2), &c2), Some((9, true)));
        let good = x.data(2, 9, true, &headers, &e2, &c2);
        assert_eq!(failing_step(&spec, &good), None, "the honest exhibit holds");
        assert!(spec.valid(&good));
        // a sound bit: the digest equals the commitment
        let sound = x.data(2, 3, false, &headers, &e2, &c2);
        assert_eq!(failing_step(&spec, &sound).as_deref(), Some("pre_chk"));
        // the wrong head bit for bit 9: the head says 1
        let wrong_bit = x.data(2, 9, false, &headers, &e2, &c2);
        let f = failing_step(&spec, &wrong_bit).unwrap();
        assert!(f.starts_with("h2_b"), "{f}");
        // the right bit at the wrong depth: the root and the content disagree
        let wrong_depth = x.data(3, 9, true, &headers, &e2, &c2);
        assert!(failing_step(&spec, &wrong_depth).is_some());
        // a depth where the liar does not move is refused up front
        let mut odd = good.clone();
        odd[5][1] = 3;
        assert_eq!(failing_step(&spec, &odd).as_deref(), Some("pre_chk"));
    }

    #[test]
    fn a_fabricated_stream_or_tree_fails() {
        let e1 = signed_entry(1, 0, 4, 0x000010);
        let mut e2 = signed_entry(2, 1, 5, 0x000210);
        e2[8 + 9 * CHUNK] ^= 0xFF;
        let (cp, headers) = chain(&[e1, e2.clone()]);
        let x = exhibit(cp);
        let spec = x.spec();
        let c2 = commits(2);
        let good = x.data(2, 9, true, &headers, &e2, &c2);
        // a different entry's stream: the root check at header 2 fails
        let other = signed_entry(2, 1, 5, 0x000210);
        let forged = x.data(2, 9, true, &headers, &other, &c2);
        assert_eq!(failing_step(&spec, &forged).as_deref(), Some("pre_chk"), "the sound entry has nothing to exhibit");
        let mut forged2 = forged.clone();
        forged2[..6].clone_from_slice(&good[..6]);
        let f = failing_step(&spec, &forged2).unwrap();
        assert!(f.starts_with("s"), "the stream must carry X at slot 9: {f}");
        // a tree of the wrong depth's commitments: the root check fails
        let t4 = x.data(2, 9, true, &headers, &e2, &commits(4));
        assert_eq!(failing_step(&spec, &t4).as_deref(), Some("t_root"));
        println!("MEASURE sig exhibit ttt W_max={W_MAX} k=2: {} steps -> {} padded, {} rounds, {N_WORDS} words", x.n_steps(), spec.steps.len(), spec.rounds());
    }
}
