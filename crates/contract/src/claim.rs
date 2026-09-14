//! Claims verified by bisection.
//!
//! A *claim* is a straight-line program over a register file of `n_words`
//! 32-bit words: a constant start state and a list of steps, each either a
//! SHA-256 compression (init from the IV or the digest register `D`; block
//! words from constants, registers, or the prover's *data* for that step;
//! output to `D`; optional predicates over the registers and block words,
//! and copies of block words into registers) or a *simple* step
//! (predicates over the registers, register-to-register copies). Prover
//! data (headers, Merkle siblings, transaction bytes) only ever enters as
//! block words, which the inner chain commits per word. The prover commits
//! the end state in its Move with a Winternitz key. The challenger may
//! dispute; level-1 rounds of branching factor `k` isolate one step over
//! full register-file commitments, then:
//!
//! - a compression step is searched further inside (`inner.rs`: schedule
//!   words, round-level bisection, one-round terminal leaf), with its
//!   predicates, copies and untouched registers checked by small leaves;
//! - a simple step is disproved by one leaf (`simple.rs`).
//!
//! Sizes: a state commitment is `2 (8 n_words + 3)` witness items and a
//! leaf may verify at most two of them under the 1000-item stack limit, so
//! `n_words ≤ 24`; with `n_words > 8` use `k = 2` (one state per round).
//!
//! ```text
//! C'_d ─ dispute (2-of-2, Q broadcasts) → D_0
//!   D_0     ─ p_round_1 (P commits k-1 states)          → R_1     | timeout: Q sweeps after Δ
//!   R_1     ─ q_round_1 (Q commits a segment index)     → R_1'    | timeout: P sweeps after Δ
//!   …
//!   R_R     ─ q_round_R        (compression step)       → inner chain
//!           ─ q_round_R_check  (simple step)            → check chain
//! ```
//!
//! Both chains start with the prover re-committing the isolated step's
//! input and output states under path-independent keys, so that every
//! disprove leaf is shared by all paths and only two small families of
//! "re-commitment mismatch" leaves depend on the path.

use anyhow::{ensure, Result};
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{OutPoint, TxOut};
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_channel::{CommitCtx, PresignedTx, Role};
use lngap_lamport::gadgets::LamportExt;
use lngap_lamport::winternitz::{WotsExt, WotsPublic, WotsSig};
use lngap_lamport::{PublicKey, Reveal};
use serde::{Deserialize, Serialize};

use crate::inner::InnerKeys;
use crate::instance::key_label;
use crate::script_hash::nibbles as byte_nibbles;

/// SHA-256 initial state.
pub const IV: [u32; 8] = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];

/// A word source for a compression's block.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Src {
    Const(u32),
    /// Register word `i` of the step's input state.
    Reg(usize),
    /// Word `k` of the prover's data for this step (unconstrained by any leaf).
    Data(usize),
}

/// A compression's initial state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Init {
    Iv,
    /// The digest register (words 0..8).
    D,
}

/// Copy `n` nibbles from nibble offset `src` to `dst`. Offsets index the
/// register file (`8 n_words` nibbles); in a compression step, offsets
/// from `8 n_words` on index the 128 block nibbles (sources only).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Copy {
    pub src: usize,
    pub dst: usize,
    pub n: usize,
}

/// A predicate over the step's input state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pred {
    /// Nibbles `[off, off + nibbles.len())` equal the constant.
    EqConst { off: usize, nibbles: Vec<u8> },
    /// Nibbles `[a, a+n)` equal nibbles `[b, b+n)`.
    EqNibbles { a: usize, b: usize, n: usize },
    /// `D` (words 0..8, as the 32 hash bytes) read as a 256-bit little-endian
    /// number is at most `target` (little-endian bytes).
    LeTarget { target: [u8; 32] },
    /// Nibbles `[off, off + target.len())` read as a big-endian number are
    /// at most `target` (nibbles, most significant first). The n4bit PoW
    /// check: `D` is the whole 40-nibble state and targets compare big-endian.
    LeTargetBe { off: usize, target: Vec<u8> },
    /// Nibbles `[off, off + if0.len())` equal `if1` if bit `bit` (0 = least
    /// significant) of nibble `nib` is set, else `if0`: a constant selected
    /// by a register bit, e.g. a Lamport bit's two commitments chosen by the
    /// message bit an entry states.
    EqConstBit { nib: usize, bit: u8, off: usize, if0: Vec<u8>, if1: Vec<u8> },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Step {
    /// `D = compress(init, block)`; `preds` must hold over (registers,
    /// block); `copies` move block nibbles into registers other than `D`;
    /// everything else is unchanged.
    Compress { name: String, init: Init, block: Vec<Src>, preds: Vec<Pred>, copies: Vec<Copy> },
    /// Predicates must hold on the input state; `copies` are applied
    /// (register to register); everything else is unchanged.
    Simple { name: String, preds: Vec<Pred>, copies: Vec<Copy> },
}

impl Step {
    pub fn compress(name: &str, init: Init, block: impl IntoIterator<Item = Src>) -> Step {
        Step::Compress { name: name.into(), init, block: block.into_iter().collect(), preds: vec![], copies: vec![] }
    }
    pub fn with_preds(mut self, p: Vec<Pred>) -> Step {
        match &mut self {
            Step::Compress { preds, .. } | Step::Simple { preds, .. } => *preds = p,
        }
        self
    }
    pub fn with_copies(mut self, c: Vec<Copy>) -> Step {
        match &mut self {
            Step::Compress { copies, .. } | Step::Simple { copies, .. } => *copies = c,
        }
        self
    }
    pub fn nop() -> Step {
        Step::Simple { name: "nop".into(), preds: vec![], copies: vec![] }
    }
    pub fn check(name: &str, preds: Vec<Pred>) -> Step {
        Step::Simple { name: name.into(), preds, copies: vec![] }
    }
    pub fn copy(name: &str, copies: Vec<Copy>) -> Step {
        Step::Simple { name: name.into(), preds: vec![], copies }
    }
    pub fn preds(&self) -> &[Pred] {
        match self {
            Step::Compress { preds, .. } | Step::Simple { preds, .. } => preds,
        }
    }
    pub fn copies(&self) -> &[Copy] {
        match self {
            Step::Compress { copies, .. } | Step::Simple { copies, .. } => copies,
        }
    }
    /// Does this compression take prover data?
    pub fn has_data(&self) -> bool {
        matches!(self, Step::Compress { block, .. } if block.iter().any(|s| matches!(s, Src::Data(_))))
    }
    pub fn n_data(&self) -> usize {
        match self {
            Step::Compress { block, .. } => block.iter().filter(|s| matches!(s, Src::Data(_))).count(),
            _ => 0,
        }
    }
    pub fn name(&self) -> String {
        match self {
            Step::Compress { name, .. } | Step::Simple { name, .. } => name.clone(),
        }
    }
    /// Register nibbles this step writes (besides `D` for a compression).
    pub fn copy_mask(&self, n_words: usize) -> Vec<bool> {
        let mut m = vec![false; 8 * n_words];
        for c in self.copies() {
            for i in c.dst..c.dst + c.n {
                m[i] = true;
            }
        }
        m
    }
}

/// Which hash function a claim verifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HashKind {
    /// SHA-256: 64 rounds, 8-word state, 16-word block, message schedule.
    Sha256,
    /// n4bit sponge: 20 rounds, 5-word (40-nibble) state, 3-word rate block,
    /// no message schedule, no feed-forward.
    N4Bit,
}

impl Default for HashKind {
    fn default() -> Self {
        HashKind::Sha256
    }
}

impl HashKind {
    /// D register size in words (the hash function's working state).
    pub fn d_words(self) -> usize {
        match self {
            HashKind::Sha256 => 8,
            HashKind::N4Bit => 5,
        }
    }
    /// Block size in 32-bit-equivalent words.
    pub fn block_words(self) -> usize {
        match self {
            HashKind::Sha256 => 16,
            HashKind::N4Bit => 2, // 16 nibbles per step (20-nibble rate, 4 zero-filled)
        }
    }
    /// Rounds per compression.
    pub fn n_rounds(self) -> u32 {
        match self {
            HashKind::Sha256 => 64,
            HashKind::N4Bit => 20,
        }
    }
    /// Inner bisection branching factor.
    pub fn inner_k(self) -> u32 {
        match self {
            HashKind::Sha256 => 8,
            HashKind::N4Bit => 2, // 20 rounds padded to 32, 5 inner rounds
        }
    }
    /// Whether the hash has a message schedule (SHA-256 does, n4bit doesn't).
    pub fn has_schedule(self) -> bool {
        match self {
            HashKind::Sha256 => true,
            HashKind::N4Bit => false,
        }
    }
    /// Whether the hash has a feed-forward addition (SHA-256's MD step).
    pub fn has_feed_forward(self) -> bool {
        match self {
            HashKind::Sha256 => true,
            HashKind::N4Bit => false,
        }
    }
}

/// The program a claim asserts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClaimSpec {
    pub n_words: usize,
    pub start: Vec<u32>,
    /// Length must be a power of `k`.
    pub steps: Vec<Step>,
    /// Level-1 branching factor.
    pub k: u32,
    /// Two-level search (inner round-level bisection) for compression steps;
    /// otherwise a single compression-level terminal leaf (phase 1; requires
    /// `n_words == 8` and compression-only steps with constant blocks).
    #[serde(default)]
    pub inner: bool,
    /// Which hash function the compressions use.
    #[serde(default)]
    pub hash: HashKind,
    /// Skip inner round bisection: after re-committing input/output/block,
    /// a single flat terminal leaf recomputes all rounds. Only valid when
    /// the round leaf is small enough to fit in one transaction (n4bit).
    #[serde(default)]
    pub flat_inner: bool,
}

impl Default for ClaimSpec {
    fn default() -> Self {
        ClaimSpec {
            n_words: 0,
            start: vec![],
            steps: vec![],
            k: 2,
            inner: false,
            hash: HashKind::Sha256,
            flat_inner: false,
        }
    }
}

/// Prover data: one `Vec<u32>` per compression step that has `Data` sources, in step order.
pub type ClaimData = Vec<Vec<u32>>;

/// A bisection over `n` steps with branching `k` (`n` a power of `k`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Search {
    pub n: u32,
    pub k: u32,
}

impl Search {
    pub const fn rounds(&self) -> u32 {
        let mut r = 0;
        let mut n = self.n;
        while n > 1 {
            n /= self.k;
            r += 1;
        }
        r
    }
    pub fn index_bits(&self) -> usize {
        assert!(self.k.is_power_of_two() && self.k >= 2);
        self.k.trailing_zeros() as usize
    }
    /// The step indices at which the prover commits states in the next
    /// round given the segment indices chosen so far.
    pub fn round_points(&self, path: &[u32]) -> Vec<u32> {
        let (lo, len) = self.segment(path);
        (1..self.k).map(|t| lo + t * len / self.k).collect()
    }
    /// `(lo, len)` of the segment after applying `path`.
    pub fn segment(&self, path: &[u32]) -> (u32, u32) {
        let mut lo = 0;
        let mut len = self.n;
        for j in path {
            len /= self.k;
            lo += j * len;
        }
        (lo, len)
    }
    /// Every index path of length `rounds` over `k`.
    pub fn all_paths(&self) -> Vec<Vec<u32>> {
        let mut paths = vec![vec![]];
        for _ in 0..self.rounds() {
            paths = paths.into_iter().flat_map(|p| (0..self.k).map(move |j| { let mut q = p.clone(); q.push(j); q })).collect();
        }
        paths
    }
}

// ----- native evaluation -----

/// Nibbles of a state (8 per word, most significant first).
pub fn state_nibbles(state: &[u32]) -> Vec<u8> {
    state.iter().flat_map(|w| (0..8).rev().map(move |i| ((w >> (4 * i)) & 15) as u8)).collect()
}

pub fn nibbles_state(n: &[u8]) -> Vec<u32> {
    n.chunks(8).map(|c| c.iter().fold(0u32, |acc, x| (acc << 4) | u32::from(*x))).collect()
}

/// Big-endian bytes of the words.
pub fn words_bytes(w: &[u32]) -> Vec<u8> {
    w.iter().flat_map(|x| x.to_be_bytes()).collect()
}

pub fn words_from_bytes(b: &[u8]) -> Vec<u32> {
    b.chunks(4).map(|c| { let mut a = [0u8; 4]; a[..c.len()].copy_from_slice(c); u32::from_be_bytes(a) }).collect()
}

impl Pred {
    /// Evaluate over a nibble vector (registers, then block nibbles for a compression).
    pub fn holds(&self, n: &[u8]) -> bool {
        match self {
            Pred::EqConst { off, nibbles } => n[*off..*off + nibbles.len()] == nibbles[..],
            Pred::EqNibbles { a, b, n: len } => n[*a..*a + *len] == n[*b..*b + *len],
            Pred::LeTarget { target } => {
                // NOTE: hardcoded to n[..64] (32 bytes = SHA-256's 8-word D register).
                // n4bit specs with LeTarget would need 40 nibbles (5-word D);
                // parameterize if needed.
                let d = words_bytes(&nibbles_state(&n[..64]));
                // little-endian: compare from byte 31 down
                for i in (0..32).rev() {
                    if d[i] != target[i] {
                        return d[i] < target[i];
                    }
                }
                true
            }
            Pred::LeTargetBe { off, target } => {
                for (k, t) in target.iter().enumerate() {
                    let nib = n[*off + k];
                    if nib != *t {
                        return nib < *t;
                    }
                }
                true
            }
            Pred::EqConstBit { nib, bit, off, if0, if1 } => {
                let c = if (n[*nib] >> bit) & 1 == 1 { if1 } else { if0 };
                n[*off..*off + c.len()] == c[..]
            }
        }
    }
    pub fn name(&self) -> String {
        match self {
            Pred::EqConst { off, nibbles } => format!("eq_const@{off}x{}", nibbles.len()),
            Pred::EqNibbles { a, b, n } => format!("eq@{a}={b}x{n}"),
            Pred::LeTarget { .. } => "le_target".into(),
            Pred::LeTargetBe { off, target } => format!("le_be@{off}x{}", target.len()),
            Pred::EqConstBit { nib, bit, off, if0, .. } => format!("eq_bit@{nib}.{bit}->{off}x{}", if0.len()),
        }
    }
}

impl ClaimSpec {
    pub fn search(&self) -> Search {
        let mut n = self.steps.len() as u32;
        while n > 1 {
            assert!(n % self.k == 0, "steps must be a power of k");
            n /= self.k;
        }
        Search { n: self.steps.len() as u32, k: self.k }
    }
    pub fn n_steps(&self) -> u32 {
        self.steps.len() as u32
    }
    pub fn rounds(&self) -> u32 {
        self.search().rounds()
    }
    /// D register size in words (hash-function's working state).
    pub fn d_words(&self) -> usize {
        self.hash.d_words()
    }
    /// D register size in nibbles.
    pub fn d_nibbles(&self) -> usize {
        8 * self.d_words()
    }
    /// Block size in nibbles.
    pub fn block_nibbles(&self) -> usize {
        8 * self.hash.block_words()
    }
    /// Inner bisection rounds (within one compression step).
    pub fn inner_rounds(&self) -> u32 {
        self.hash.n_rounds()
    }
    /// Inner bisection branching factor.
    pub fn inner_k(&self) -> u32 {
        self.hash.inner_k()
    }
    /// Inner search structure.
    pub fn inner_search(&self) -> Search {
        if self.flat_inner {
            return Search { n: 1, k: 1 };
        }
        let n = self.inner_rounds();
        let k = self.inner_k();
        // Pad n to the next power of k so the bisection is well-defined.
        let mut padded = 1;
        while padded < n {
            padded *= k;
        }
        Search { n: padded, k }
    }
    /// Whether the hash has a message schedule.
    pub fn has_schedule(&self) -> bool {
        self.hash.has_schedule()
    }
    /// Whether the hash has a feed-forward addition.
    pub fn has_feed_forward(&self) -> bool {
        self.hash.has_feed_forward()
    }
    pub fn index_bits(&self) -> usize {
        self.search().index_bits()
    }
    pub fn round_points(&self, path: &[u32]) -> Vec<u32> {
        self.search().round_points(path)
    }
    pub fn segment(&self, path: &[u32]) -> (u32, u32) {
        self.search().segment(path)
    }
    /// Indices of the steps that take prover data, in order.
    pub fn data_steps(&self) -> Vec<usize> {
        self.steps.iter().enumerate().filter(|(_, s)| s.has_data()).map(|(i, _)| i).collect()
    }
    /// The words of a compression's init and block for an input state and data.
    pub fn compress_inputs(step: &Step, state: &[u32], data: &[u32], hash: HashKind) -> (Vec<u32>, Vec<u8>) {
        let Step::Compress { init, block, .. } = step else { panic!("not a compression") };
        let dw = hash.d_words();
        let bw = hash.block_words();
        let init_w: Vec<u32> = match init {
            Init::Iv => match hash {
                HashKind::Sha256 => IV.to_vec(),
                HashKind::N4Bit => vec![0u32; dw],
            },
            Init::D => state[..dw].to_vec(),
        };
        let mut b = vec![0u8; 4 * bw];
        for (j, src) in block.iter().enumerate() {
            let w = match src {
                Src::Const(c) => *c,
                Src::Reg(i) => state[*i],
                Src::Data(k) => data[*k],
            };
            b[4 * j..4 * j + 4].copy_from_slice(&w.to_be_bytes());
        }
        (init_w, b)
    }
    /// The n4bit round counter of compression step `step_index`: `ROUNDS`
    /// times its block index within its message, a message starting at the
    /// nearest preceding compression with `Init::Iv` (or at step 0). This
    /// is what makes every message hash to the same digest wherever it sits
    /// in the claim, i.e. what `lngap_n4bit::hash_claim` computes.
    pub fn round_counter(&self, step_index: usize) -> usize {
        let mut start = 0;
        for i in (0..=step_index.min(self.steps.len().saturating_sub(1))).rev() {
            if matches!(self.steps[i], Step::Compress { init: Init::Iv, .. }) {
                start = i;
                break;
            }
        }
        let blocks = self.steps[start..step_index].iter().filter(|s| matches!(s, Step::Compress { .. })).count();
        blocks * self.hash.n_rounds() as usize
    }
    /// Apply one step (`data` for a compression with data sources). Returns
    /// the output state and whether the step's predicates held.
    /// `step_index` is the step's position in the spec (used for the n4bit
    /// round counter, see [`ClaimSpec::round_counter`]; ignored for SHA-256).
    pub fn apply(&self, step_index: usize, step: &Step, state: &[u32], data: &[u32]) -> (Vec<u32>, bool) {
        let mut n = state_nibbles(state);
        let (out_d, space): (Option<Vec<u32>>, Vec<u8>) = match step {
            Step::Compress { .. } => {
                let (init_w, b) = Self::compress_inputs(step, state, data, self.hash);
                let mut space = n.clone();
                space.extend(byte_nibbles(&b));
                let d = match self.hash {
                    HashKind::Sha256 => {
                        let mut s: [u32; 8] = init_w.as_slice().try_into().unwrap();
                        let block: [u8; 64] = b.as_slice().try_into().unwrap();
                        sha2::compress256(&mut s, &[block.into()]);
                        s.to_vec()
                    }
                    HashKind::N4Bit => {
                        let sn = state_nibbles(&init_w);
                        let mut st: [u8; lngap_n4bit::STATE_NIBBLES] = sn.as_slice().try_into().unwrap();
                        let bn = byte_nibbles(&b);
                        // Zero-pad block nibbles to RATE_NIBBLES (block may be
                        // shorter: 2 words = 16 nibbles, rate = 20 nibbles).
                        let mut block = [0u8; lngap_n4bit::RATE_NIBBLES];
                        let n = bn.len().min(lngap_n4bit::RATE_NIBBLES);
                        block[..n].copy_from_slice(&bn[..n]);
                        let round_counter = self.round_counter(step_index);
                        lngap_n4bit::sponge_absorb(&mut st, &block, round_counter);
                        nibbles_state(&st)
                    }
                };
                (Some(d), space)
            }
            Step::Simple { .. } => (None, n.clone()),
        };
        let ok = step.preds().iter().all(|p| p.holds(&space));
        for c in step.copies() {
            n[c.dst..c.dst + c.n].copy_from_slice(&space[c.src..c.src + c.n]);
        }
        let mut out = nibbles_state(&n);
        if let Some(d) = out_d {
            out[..d.len()].copy_from_slice(&d);
        }
        (out, ok)
    }
    /// Is `next` a correct output of `step` on `cur` with `data`?
    pub fn step_ok(&self, step_index: usize, step: &Step, cur: &[u32], next: &[u32], data: &[u32]) -> bool {
        let (expect, ok) = self.apply(step_index, step, cur, data);
        ok && expect == next
    }
    /// The data slice for step `i` (empty for steps without data).
    pub fn data_for<'a>(&self, data: &'a ClaimData, i: usize) -> &'a [u32] {
        match self.data_steps().iter().position(|x| *x == i) {
            Some(k) => &data[k],
            None => &[],
        }
    }
    /// All `n + 1` states of the chain for `data`.
    pub fn states(&self, data: &ClaimData) -> Vec<Vec<u32>> {
        let mut v = vec![self.start.clone()];
        for (i, step) in self.steps.iter().enumerate() {
            let (s, _) = self.apply(i, step, v.last().unwrap(), self.data_for(data, i));
            v.push(s);
        }
        v
    }
    /// Do all predicates hold along the chain for `data`?
    pub fn valid(&self, data: &ClaimData) -> bool {
        self.segment_reference(0, self.steps.len(), &self.start, data).1
    }
    /// The state expected at the end of steps `[lo, hi)` from `start` with
    /// `data`, and whether every predicate in the segment held.
    pub fn segment_reference(&self, lo: usize, hi: usize, start: &[u32], data: &ClaimData) -> (Vec<u32>, bool) {
        let mut s = start.to_vec();
        let mut all_ok = true;
        for i in lo..hi {
            let (next, ok) = self.apply(i, &self.steps[i], &s, self.data_for(data, i));
            all_ok &= ok;
            s = next;
        }
        (s, all_ok)
    }
    pub fn wots_bytes(&self) -> u32 {
        4 * self.n_words as u32
    }
}

// ----- sources along a level-1 path -----

/// Where a leaf gets a level-1 state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateSource {
    Const(Vec<u32>),
    /// The prover's end state from its Move.
    End,
    /// The prover's commitment `t` (0-based) in round `r` (1-based).
    Round(u32, u32),
}

impl StateSource {
    pub fn name(&self) -> String {
        match self {
            StateSource::Const(_) => "const".into(),
            StateSource::End => "end".into(),
            StateSource::Round(r, t) => format!("r{r}t{t}"),
        }
    }
}

/// Sources of the isolated step's input and claimed output for a full path, and the step index.
pub fn step_sources(spec: &ClaimSpec, path: &[u32]) -> (StateSource, StateSource, u32) {
    assert_eq!(path.len() as u32, spec.rounds());
    let mut lo_src = StateSource::Const(spec.start.clone());
    let mut hi_src = StateSource::End;
    for (r, &j) in path.iter().enumerate() {
        let r1 = r as u32 + 1;
        let new_lo = if j == 0 { lo_src.clone() } else { StateSource::Round(r1, j - 1) };
        let new_hi = if j == spec.k - 1 { hi_src.clone() } else { StateSource::Round(r1, j) };
        lo_src = new_lo;
        hi_src = new_hi;
    }
    let (lo, len) = spec.segment(path);
    assert_eq!(len, 1);
    (lo_src, hi_src, lo)
}

/// All distinct (source, role) pairs a terminal leaf may need: every
/// `Round(r, t)`, plus `Const(start)` for inputs and `End` for outputs.
pub fn cur_sources(spec: &ClaimSpec) -> Vec<StateSource> {
    let mut v = vec![StateSource::Const(spec.start.clone())];
    for r in 1..=spec.rounds() {
        for t in 0..spec.k - 1 {
            v.push(StateSource::Round(r, t));
        }
    }
    v
}
pub fn next_sources(spec: &ClaimSpec) -> Vec<StateSource> {
    let mut v = vec![StateSource::End];
    for r in 1..=spec.rounds() {
        for t in 0..spec.k - 1 {
            v.push(StateSource::Round(r, t));
        }
    }
    v
}

pub fn all_paths(spec: &ClaimSpec) -> Vec<Vec<u32>> {
    spec.search().all_paths()
}

pub fn path_name(path: &[u32]) -> String {
    path.iter().map(|j| j.to_string()).collect::<Vec<_>>().join("")
}

// ----- keys -----

/// The prover's Winternitz keys for a claim at one depth.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClaimKeys {
    pub end: WotsPublic,
    /// `rounds[r-1][t]`: round `r`, commitment `t`.
    pub rounds: Vec<Vec<WotsPublic>>,
    /// Inner-level keys (`spec.inner`).
    #[serde(default)]
    pub inner: Option<InnerKeys>,
}

/// The challenger's Lamport index keys, one per round (and per inner round).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChallengerKeys {
    pub indices: Vec<PublicKey>,
    #[serde(default)]
    pub inner_indices: Vec<PublicKey>,
}

pub fn end_label(id: u32, seq: u64, depth: u32) -> String {
    key_label(id, seq, depth, "claim/end")
}
pub fn round_label(id: u32, seq: u64, depth: u32, r: u32, t: u32) -> String {
    key_label(id, seq, depth, &format!("claim/round{r}/state{t}"))
}
pub fn index_label(id: u32, seq: u64, depth: u32, r: u32) -> String {
    key_label(id, seq, depth, &format!("claim/round{r}/index"))
}

pub fn source_key<'a>(src: &StateSource, keys: &'a ClaimKeys) -> &'a WotsPublic {
    match src {
        StateSource::End => &keys.end,
        StateSource::Round(r, t) => &keys.rounds[*r as usize - 1][*t as usize],
        StateSource::Const(_) => panic!("constant source has no key"),
    }
}

/// Words of a committed state from a verified Winternitz message.
pub fn state_from_msg(msg: &[u8]) -> Vec<u32> {
    words_from_bytes(msg)
}

// ----- shared script pieces -----

/// Verify a WOTS signature and discard the digits.
pub(crate) fn wots_verify_drop(mut b: Builder, pk: &WotsPublic) -> Builder {
    b = b.wots_verify(pk);
    for _ in 0..pk.params.message_digits / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    b
}

pub(crate) fn timeout_leaf(ctx: &CommitCtx, sweeper: Role) -> Leaf {
    Leaf::new(
        "timeout",
        Builder::new().csv(ctx.params.delta).checksig(&ctx.key(sweeper).payment).into_script(),
        Timelock::csv(ctx.params.delta),
    )
}

/// Push a state's nibbles (constant) or verify its commitment, leaving
/// `8 * n_words` nibbles (last nibble on top); then park them on the altstack.
pub(crate) fn load_source(b: Builder, src: &StateSource, keys: &ClaimKeys, n_words: usize) -> Builder {
    let b = match src {
        StateSource::Const(s) => state_nibbles(s).into_iter().fold(b, crate::script_hash::push_scriptnum),
        _ => b.wots_verify(source_key(src, keys)),
    };
    park(b, 8 * n_words)
}

pub(crate) fn park(mut b: Builder, n: usize) -> Builder {
    for _ in 0..n {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b
}

pub(crate) fn unpark(mut b: Builder, n: usize) -> Builder {
    for _ in 0..n {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    b
}

/// Fee of a pre-signed transaction spending a leaf of `script_len` bytes:
/// the fixed fee, or 0.2 sat/vB of the estimated size (the witness of a
/// signature-heavy leaf is about a third of its script) if that is more.
/// Deterministic, so both parties pre-sign the same transaction.
pub fn stage_fee(ctx: &CommitCtx, script_len: usize) -> bitcoin::Amount {
    let est_vsize = (script_len as u64 * 4 / 3) / 4 + 60;
    ctx.params.presign_fee.max(bitcoin::Amount::from_sat(est_vsize / 5))
}

// ----- level-1 trees -----

/// `D_0` / `R_{r-1}'`: waiting for the prover's round `r`.
pub fn wait_p_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, r: u32) -> Result<TapTree> {
    let mut b = ctx.two_of_two_verify(Builder::new());
    for pk in &keys.rounds[r as usize - 1] {
        b = wots_verify_drop(b, pk);
    }
    let leaf = Leaf::new(format!("p_round_{r}"), b.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE);
    TapTree::new(vec![leaf, timeout_leaf(ctx, prover.other())])
}

/// `R_r`: waiting for the challenger's index for round `r`. In the last
/// round (with `spec.inner`) a second leaf, `q_round_R_check`, carries the
/// same index into the check chain for simple steps.
pub fn wait_q_tree(ctx: &CommitCtx, prover: Role, ck: &ChallengerKeys, spec: &ClaimSpec, r: u32) -> Result<TapTree> {
    let pk = &ck.indices[r as usize - 1];
    let mut b = ctx.two_of_two_verify(Builder::new());
    for i in (0..pk.n_bits()).rev() {
        b = b.bit_decode(&pk.bits[i]).push_opcode(OP_DROP);
    }
    let mut leaves = vec![Leaf::new(format!("q_round_{r}"), b.clone().push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE)];
    if r == spec.rounds() && spec.inner {
        leaves.push(Leaf::new(format!("q_round_{r}_check"), b.push_opcode(OP_PUSHNUM_1).push_opcode(OP_NOP).into_script(), Timelock::NONE));
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// The `dispute` leaf on `C'_d`: plain 2-of-2, pre-signed; the challenger broadcasts it.
pub fn dispute_leaf(ctx: &CommitCtx) -> Leaf {
    Leaf::new("dispute", ctx.two_of_two(Builder::new()).into_script(), Timelock::NONE)
}

/// Witness args for `p_round_r` after the two channel signatures: the k-1 commitments in order.
pub fn p_round_witness(sigs: &[WotsSig]) -> Vec<Vec<u8>> {
    sigs.iter().flat_map(|s| s.consumption_order()).collect()
}

/// Witness args for `q_round_r` after the two channel signatures.
pub fn q_round_witness(index: &Reveal) -> Vec<Vec<u8>> {
    index.consumption_order()
}

/// One stage of a pre-signed chain: the leaf spent, the tree of the new output, a description.
pub struct Stage {
    pub leaf: String,
    pub next: TapTree,
    pub what: String,
}

/// Append a chain of stages to `out`, each spending the previous output by
/// size-based fee (`stage_fee`).
pub(crate) fn chain_stages(out: &mut Vec<PresignedTx>, ctx: &CommitCtx, mut op: OutPoint, mut prevout: TxOut, mut tree: TapTree, stages: Vec<Stage>) -> Result<()> {
    let mut value = prevout.value;
    for st in stages {
        let l = tree.leaf(&st.leaf)?;
        value -= stage_fee(ctx, l.script.len());
        let tx = build_spend(op, &l.timelock, vec![TxOut { value, script_pubkey: st.next.script_pubkey() }]);
        let next_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
        let next_prevout = tx.output[0].clone();
        out.push(PresignedTx::new(st.leaf.clone(), tx, vec![prevout.clone()], &tree, &st.leaf, st.what)?);
        op = next_op;
        prevout = next_prevout;
        tree = st.next;
    }
    Ok(())
}

/// Build the dispute chain hanging off `C'_d` (whose tree contains the
/// `dispute` leaf). Labels: `dispute`, `p_round_r`, `q_round_r`, then the
/// inner chain (`p_re_cur`, `p_re_next`, `p_sched`, `p_inner_r`, `q_inner_r`)
/// and the check chain (`q_round_R_check`, `c_re_cur`, `c_re_next`).
#[allow(clippy::too_many_arguments)]
pub fn dispute_graph(
    ctx: &CommitCtx,
    prover: Role,
    keys: &ClaimKeys,
    ck: &ChallengerKeys,
    spec: &ClaimSpec,
    parent_tree: &TapTree,
    parent_op: OutPoint,
    parent_prevout: &TxOut,
) -> Result<Vec<PresignedTx>> {
    let fee = ctx.params.presign_fee;
    let rounds = spec.rounds();
    ensure!(keys.rounds.len() as u32 == rounds && ck.indices.len() as u32 == rounds, "claim keys do not match the spec");
    let mut out = Vec::new();
    let mut value = parent_prevout.value;
    // dispute: C'_d -> D_0
    let d0 = wait_p_tree(ctx, prover, keys, 1)?;
    value -= fee;
    let tx = build_spend(parent_op, &parent_tree.leaf("dispute")?.timelock, vec![TxOut { value, script_pubkey: d0.script_pubkey() }]);
    let mut op = OutPoint { txid: tx.compute_txid(), vout: 0 };
    let mut prevout = tx.output[0].clone();
    out.push(PresignedTx::new("dispute", tx, vec![parent_prevout.clone()], parent_tree, "dispute", format!("{} disputes the claim", prover.other()))?);
    let mut tree = d0;
    for r in 1..=rounds {
        // p_round_r: -> R_r
        let rr = wait_q_tree(ctx, prover, ck, spec, r)?;
        value -= fee;
        let tx = build_spend(op, &tree.leaf(&format!("p_round_{r}"))?.timelock, vec![TxOut { value, script_pubkey: rr.script_pubkey() }]);
        let next_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
        let next_prevout = tx.output[0].clone();
        out.push(PresignedTx::new(format!("p_round_{r}"), tx, vec![prevout.clone()], &tree, &format!("p_round_{r}"), format!("{prover} commits round {r} states"))?);
        op = next_op;
        prevout = next_prevout;
        tree = rr;
        if r < rounds {
            // q_round_r: -> R_r' (wait_p for round r+1)
            let rq = wait_p_tree(ctx, prover, keys, r + 1)?;
            value -= fee;
            let tx = build_spend(op, &tree.leaf(&format!("q_round_{r}"))?.timelock, vec![TxOut { value, script_pubkey: rq.script_pubkey() }]);
            let next_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
            let next_prevout = tx.output[0].clone();
            out.push(PresignedTx::new(format!("q_round_{r}"), tx, vec![prevout.clone()], &tree, &format!("q_round_{r}"), format!("{} picks a segment in round {r}", prover.other()))?);
            op = next_op;
            prevout = next_prevout;
            tree = rq;
        }
    }
    // the last index: into the inner chain (compression steps), the check chain (simple steps), or the flat terminal
    if spec.inner {
        let (stages, _) = crate::inner::compress_chain(ctx, prover, keys, ck, spec)?;
        chain_stages(&mut out, ctx, op, prevout.clone(), tree.clone(), stages)?;
        let (stages, _) = crate::simple::check_chain(ctx, prover, keys, spec)?;
        chain_stages(&mut out, ctx, op, prevout, tree, stages)?;
    } else {
        let stages = vec![Stage { leaf: format!("q_round_{rounds}"), next: crate::flat::terminal_tree(ctx, prover, keys, spec)?, what: format!("{} picks a segment in round {rounds}", prover.other()) }];
        chain_stages(&mut out, ctx, op, prevout, tree, stages)?;
    }
    Ok(out)
}

/// The trees along the chains, in order: `D_0, R_1, R_1', …, R_R` (the
/// level-1 outputs), then the inner chain's outputs, then the check chain's
/// (for the party to identify which leaf spent which output).
pub fn dispute_trees(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, ck: &ChallengerKeys, spec: &ClaimSpec) -> Result<Vec<TapTree>> {
    let rounds = spec.rounds();
    let mut v = vec![wait_p_tree(ctx, prover, keys, 1)?];
    for r in 1..=rounds {
        v.push(wait_q_tree(ctx, prover, ck, spec, r)?);
        if r < rounds {
            v.push(wait_p_tree(ctx, prover, keys, r + 1)?);
        }
    }
    if spec.inner {
        v.extend(crate::inner::compress_chain(ctx, prover, keys, ck, spec)?.1);
        v.extend(crate::simple::check_chain(ctx, prover, keys, spec)?.1);
    } else {
        v.push(crate::flat::terminal_tree(ctx, prover, keys, spec)?);
    }
    Ok(v)
}

/// Number of level-1 trees (`D_0 … R_R`): the inner chain's trees follow at this offset.
pub fn level1_tree_count(spec: &ClaimSpec) -> usize {
    2 * spec.rounds() as usize
}

pub fn nibbles_of_bytes(b: &[u8]) -> Vec<u8> {
    byte_nibbles(b)
}
