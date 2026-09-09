//! Claims verified by bisection.
//!
//! A *claim* is a straight-line chain of `n` SHA-256 compression steps
//! `s_0 → s_1 → … → s_n` where `s_0` is a constant of the contract, each
//! step's 64-byte block is a constant of the contract (phase 1; later steps
//! take prover-committed inputs), and the prover commits `s_n` in its Move
//! with a Winternitz key. The challenger may dispute; rounds of branching
//! factor `k` isolate one step, and a terminal leaf recomputes it.
//!
//! Graph off `C'_d` (P = prover at depth d, Q = challenger):
//!
//! ```text
//! C'_d ─ dispute (2-of-2, Q broadcasts) → D_0
//!   D_0     ─ p_round_1 (P commits k-1 midstates)   → R_1     | timeout: Q sweeps after Δ
//!   R_1     ─ q_round_1 (Q commits a segment index) → R_1'    | timeout: P sweeps after Δ
//!   R_1'    ─ p_round_2                              → R_2     | timeout: Q
//!   …
//!   R_R'    ─ step_<path> (Q proves the isolated step is wrong; no timelock)
//!           | timeout: P sweeps after Δ (the claim stood)
//! ```

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

use crate::instance::key_label;
use crate::script_hash::{append_script, nibbles as byte_nibbles, push_scriptnum, sha256_compress_script, state_bytes};

/// The chain a claim asserts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClaimSpec {
    pub n_steps: u32,
    /// Branching factor; `n_steps` must be a power of `k`.
    pub k: u32,
    pub start: [u32; 8],
    /// One 64-byte block per step.
    #[serde(with = "blocks_serde")]
    pub blocks: Vec<[u8; 64]>,
}

mod blocks_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(v: &Vec<[u8; 64]>, s: S) -> Result<S::Ok, S::Error> {
        v.iter().map(|b| hex::encode(b)).collect::<Vec<_>>().serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<[u8; 64]>, D::Error> {
        let v: Vec<String> = Vec::deserialize(d)?;
        v.iter()
            .map(|h| {
                let bytes = hex::decode(h).map_err(serde::de::Error::custom)?;
                bytes.try_into().map_err(|_| serde::de::Error::custom("block must be 64 bytes"))
            })
            .collect()
    }
}

impl ClaimSpec {
    pub fn rounds(&self) -> u32 {
        let mut r = 0;
        let mut n = self.n_steps;
        while n > 1 {
            assert!(n % self.k == 0, "n_steps must be a power of k");
            n /= self.k;
            r += 1;
        }
        r
    }
    pub fn index_bits(&self) -> usize {
        assert!(self.k.is_power_of_two() && self.k >= 2);
        self.k.trailing_zeros() as usize
    }
    /// All `n_steps + 1` states of the honest chain.
    pub fn states(&self) -> Vec<[u32; 8]> {
        let mut v = vec![self.start];
        for b in &self.blocks {
            let mut s = *v.last().unwrap();
            sha2::compress256(&mut s, &[(*b).into()]);
            v.push(s);
        }
        v
    }
    /// The step indices at which the prover commits midstates in round `r`
    /// (1-based) given the segment indices chosen so far.
    pub fn round_points(&self, path: &[u32]) -> Vec<u32> {
        let (lo, len) = self.segment(path);
        (1..self.k).map(|t| lo + t * len / self.k).collect()
    }
    /// `(lo, len)` of the segment after applying `path` (segment indices, one per completed round).
    pub fn segment(&self, path: &[u32]) -> (u32, u32) {
        let mut lo = 0;
        let mut len = self.n_steps;
        for j in path {
            len /= self.k;
            lo += j * len;
        }
        (lo, len)
    }
}

/// Where a terminal leaf gets a midstate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateSource {
    Const([u32; 8]),
    /// The prover's `s_n` from its Move.
    End,
    /// The prover's commitment `t` (0-based) in round `r` (1-based).
    Round(u32, u32),
}

/// Sources of the isolated step's input and claimed output for a full path.
pub fn step_sources(spec: &ClaimSpec, path: &[u32]) -> (StateSource, StateSource, u32) {
    assert_eq!(path.len() as u32, spec.rounds());
    let mut lo_src = StateSource::Const(spec.start);
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

/// Every index path of length `rounds` over `k`.
pub fn all_paths(spec: &ClaimSpec) -> Vec<Vec<u32>> {
    let r = spec.rounds() as usize;
    let mut paths = vec![vec![]];
    for _ in 0..r {
        paths = paths.into_iter().flat_map(|p| (0..spec.k).map(move |j| { let mut q = p.clone(); q.push(j); q })).collect();
    }
    paths
}

pub fn path_name(path: &[u32]) -> String {
    path.iter().map(|j| j.to_string()).collect::<Vec<_>>().join("")
}

/// The prover's Winternitz keys for a claim at one depth.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClaimKeys {
    pub end: WotsPublic,
    /// `rounds[r-1][t]`: round `r`, commitment `t`.
    pub rounds: Vec<Vec<WotsPublic>>,
}

/// The challenger's Lamport index keys, one per round.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChallengerKeys {
    pub indices: Vec<PublicKey>,
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

/// Verify a WOTS signature and discard the digits.
fn wots_verify_drop(mut b: Builder, pk: &WotsPublic) -> Builder {
    b = b.wots_verify(pk);
    for _ in 0..pk.params.message_digits / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    b
}

fn timeout_leaf(ctx: &CommitCtx, sweeper: Role) -> Leaf {
    Leaf::new(
        "timeout",
        Builder::new().csv(ctx.params.delta).checksig(&ctx.key(sweeper).payment).into_script(),
        Timelock::csv(ctx.params.delta),
    )
}

/// `D_0` / `R_{r-1}'`: waiting for the prover's round `r`.
pub fn wait_p_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, r: u32) -> Result<TapTree> {
    let mut b = ctx.two_of_two_verify(Builder::new());
    for pk in &keys.rounds[r as usize - 1] {
        b = wots_verify_drop(b, pk);
    }
    let leaf = Leaf::new(format!("p_round_{r}"), b.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE);
    TapTree::new(vec![leaf, timeout_leaf(ctx, prover.other())])
}

/// `R_r`: waiting for the challenger's index for round `r`.
pub fn wait_q_tree(ctx: &CommitCtx, prover: Role, ck: &ChallengerKeys, r: u32) -> Result<TapTree> {
    let pk = &ck.indices[r as usize - 1];
    let mut b = ctx.two_of_two_verify(Builder::new());
    for i in (0..pk.n_bits()).rev() {
        b = b.bit_decode(&pk.bits[i]).push_opcode(OP_DROP);
    }
    let leaf = Leaf::new(format!("q_round_{r}"), b.push_opcode(OP_PUSHNUM_1).into_script(), Timelock::NONE);
    TapTree::new(vec![leaf, timeout_leaf(ctx, prover)])
}

/// Terminal leaf body for one path (after `<Q> OP_CHECKSIGVERIFY`).
fn step_body(mut b: Builder, cur: &StateSource, next_pk: &WotsPublic, block: &[u8; 64], keys: &ClaimKeys) -> Builder {
    // claimed next: verify, reverse, park (digit 63 ends on the altstack top)
    b = b.wots_verify(next_pk);
    for i in 1..64i64 {
        b = b.push_int(i).push_opcode(OP_ROLL);
    }
    for _ in 0..64 {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    match cur {
        StateSource::Const(s) => {
            for nib in byte_nibbles(block) {
                b = push_scriptnum(b, nib);
            }
            for nib in byte_nibbles(&state_bytes(s)) {
                b = push_scriptnum(b, nib);
            }
        }
        src => {
            let pk = source_key(src, keys);
            b = b.wots_verify(pk);
            for _ in 0..64 {
                b = b.push_opcode(OP_TOALTSTACK);
            }
            for nib in byte_nibbles(block) {
                b = push_scriptnum(b, nib);
            }
            for _ in 0..64 {
                b = b.push_opcode(OP_FROMALTSTACK);
            }
        }
    }
    b = append_script(b, &sha256_compress_script());
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_EQUAL);
    for _ in 1..64 {
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_ROT).push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
    }
    b.push_opcode(OP_NOT)
}

pub fn source_key<'a>(src: &StateSource, keys: &'a ClaimKeys) -> &'a WotsPublic {
    match src {
        StateSource::End => &keys.end,
        StateSource::Round(r, t) => &keys.rounds[*r as usize - 1][*t as usize],
        StateSource::Const(_) => panic!("constant source has no key"),
    }
}

/// The terminal leaf script for `path`, and its name. Paths whose isolated
/// step has the same sources and block produce identical scripts, so leaves
/// are named by a hash of the script and deduplicated in the tree.
pub fn terminal_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec, path: &[u32]) -> (String, bitcoin::ScriptBuf) {
    let q = ctx.key(prover.other()).payment;
    let (cur, next, step) = step_sources(spec, path);
    let next_pk = source_key(&next, keys);
    let script = step_body(Builder::new().checksigverify(&q), &cur, next_pk, &spec.blocks[step as usize], keys).into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("step_{}", hex::encode(&h[..4])), script)
}

/// `R_R'`: the challenger isolates one step and disproves it, or the prover times out.
pub fn terminal_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec) -> Result<TapTree> {
    let mut leaves: Vec<Leaf> = Vec::new();
    for path in all_paths(spec) {
        let (name, script) = terminal_leaf(ctx, prover, keys, spec, &path);
        if !leaves.iter().any(|l| l.name == name) {
            leaves.push(Leaf::new(name, script, Timelock::NONE));
        }
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// The `dispute` leaf on `C'_d`: plain 2-of-2, pre-signed; the challenger broadcasts it.
pub fn dispute_leaf(ctx: &CommitCtx) -> Leaf {
    Leaf::new("dispute", ctx.two_of_two(Builder::new()).into_script(), Timelock::NONE)
}

/// Witness args for a terminal step leaf (after Q's signature): the
/// prover's signatures for `next` then `cur` (none for a constant `cur`).
pub fn step_witness(cur: &StateSource, next_sig: &WotsSig, cur_sig: Option<&WotsSig>) -> Vec<Vec<u8>> {
    let mut v = next_sig.consumption_order();
    if !matches!(cur, StateSource::Const(_)) {
        v.extend(cur_sig.expect("cur signature").consumption_order());
    }
    v
}

/// Witness args for `p_round_r` after the two channel signatures: the k-1 commitments in order.
pub fn p_round_witness(sigs: &[WotsSig]) -> Vec<Vec<u8>> {
    sigs.iter().flat_map(|s| s.consumption_order()).collect()
}

/// Witness args for `q_round_r` after the two channel signatures.
pub fn q_round_witness(index: &Reveal) -> Vec<Vec<u8>> {
    index.consumption_order()
}

/// Build the dispute chain hanging off `C'_d` (whose tree contains the
/// `dispute` leaf). Labels: `dispute`, `p_round_r`, `q_round_r`.
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
        let rr = wait_q_tree(ctx, prover, ck, r)?;
        value -= fee;
        let tx = build_spend(op, &tree.leaf(&format!("p_round_{r}"))?.timelock, vec![TxOut { value, script_pubkey: rr.script_pubkey() }]);
        let next_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
        let next_prevout = tx.output[0].clone();
        out.push(PresignedTx::new(format!("p_round_{r}"), tx, vec![prevout.clone()], &tree, &format!("p_round_{r}"), format!("{prover} commits round {r} midstates"))?);
        op = next_op;
        prevout = next_prevout;
        tree = rr;
        // q_round_r: -> R_r' (wait_p for round r+1, or terminal)
        let rq = if r < rounds { wait_p_tree(ctx, prover, keys, r + 1)? } else { terminal_tree(ctx, prover, keys, spec)? };
        value -= fee;
        let tx = build_spend(op, &tree.leaf(&format!("q_round_{r}"))?.timelock, vec![TxOut { value, script_pubkey: rq.script_pubkey() }]);
        let next_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
        let next_prevout = tx.output[0].clone();
        out.push(PresignedTx::new(format!("q_round_{r}"), tx, vec![prevout.clone()], &tree, &format!("q_round_{r}"), format!("{} picks a segment in round {r}", prover.other()))?);
        op = next_op;
        prevout = next_prevout;
        tree = rq;
    }
    let _ = (op, prevout, tree);
    Ok(out)
}

/// The trees along the chain, in order: `D_0, R_1, R_1', …, R_R'` (for the
/// party to identify which leaf spent which output).
pub fn dispute_trees(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, ck: &ChallengerKeys, spec: &ClaimSpec) -> Result<Vec<TapTree>> {
    let rounds = spec.rounds();
    let mut v = vec![wait_p_tree(ctx, prover, keys, 1)?];
    for r in 1..=rounds {
        v.push(wait_q_tree(ctx, prover, ck, r)?);
        v.push(if r < rounds { wait_p_tree(ctx, prover, keys, r + 1)? } else { terminal_tree(ctx, prover, keys, spec)? });
    }
    Ok(v)
}
