//! A contract instance in a channel state, and its contract output:
//! the depth-0 taptree on the commitment and the pre-signed graph.

use std::sync::Arc;

use anyhow::{anyhow, ensure, Result};
use bitcoin::{Amount, OutPoint, TxOut};
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::build_spend;
use lngap_channel::{ChannelParams, CommitCtx, ContractOutput, PresignedTx, Role};
use lngap_lamport::PublicKey;
use serde::{Deserialize, Serialize};

use crate::claim::{dispute_graph, dispute_leaf, ChallengerKeys, ClaimKeys, ClaimSpec};
use crate::leaves::{move_leaf, settle_leaf, split_leaf, LeafCtx, PriorState};
use crate::{GraphShape, MoveExtras, Outcome, Program, CODE_BITS, DEPTH_BITS};

/// The prover's Lamport public keys for one depth position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DepthKeys {
    pub prover: Role,
    pub mv: PublicKey,
    pub state: PublicKey,
    pub code: PublicKey,
    /// Present iff the program has a claim.
    pub claim: Option<ClaimKeys>,
    /// Star graphs, depth ≥ 2: the prover's own re-commitment of the
    /// counterparty's state at the previous depth (the Move's prior).
    #[serde(default)]
    pub prior: Option<PublicKey>,
    /// Star graphs: claim-native commitments to the state key's preimages,
    /// `[h(p0), h(p1)]` per bit, so a claim can check a published state's
    /// signature without ever handling the preimages.
    #[serde(default)]
    pub state_n4: Vec<[[u8; 20]; 2]>,
    /// Stall graphs: the role's depth key (`DEPTH_BITS` bits).
    #[serde(default)]
    pub depth: Option<PublicKey>,
}

/// Key sets of a stall graph: `[stall_U, stall_H, lie_U, lie_H, sig_U, sig_H]`.
pub const STALL_KEY_SETS: usize = 6;

/// The claim of key set index `i` (0-based) of a stall graph.
pub fn stall_spec_at(program: &dyn Program, i: usize) -> Option<ClaimSpec> {
    let role = Role::BOTH[i % 2];
    match i / 2 {
        0 => program.stall_claim(role),
        1 => program.lie_claim(role),
        _ => program.sig_claim(role),
    }
}

/// Label under which a party generates/reveals a Lamport key.
pub fn key_label(contract_id: u32, seq: u64, depth: u32, field: &str) -> String {
    format!("c{contract_id}/s{seq}/d{depth}/{field}")
}

/// Wire form of an instance (program by name; keys may be partially filled
/// while parties exchange them).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InstanceSpec {
    pub id: u32,
    pub program: String,
    pub value: Amount,
    pub state: Vec<bool>,
    pub deadline: u32,
    /// Channel seq at which the keys were generated (part of their labels).
    pub keys_seq: u64,
    /// Index `d - 1`; `None` until that depth's prover supplied keys.
    pub keys: Vec<Option<DepthKeys>>,
    /// Index `d - 1`; the challenger's dispute keys, only for programs with a claim.
    #[serde(default)]
    pub challenger_keys: Vec<Option<ChallengerKeys>>,
}

impl InstanceSpec {
    pub fn complete(&self) -> bool {
        self.keys.iter().all(Option::is_some) && self.challenger_keys.iter().all(Option::is_some)
    }
    pub fn into_instance(self, program: Arc<dyn Program>) -> Result<ContractInstance> {
        ensure!(program.name() == self.program, "program mismatch");
        let keys = self.keys.into_iter().enumerate().map(|(i, k)| k.ok_or_else(|| anyhow!("missing keys for depth {}", i + 1))).collect::<Result<Vec<_>>>()?;
        let ck = self.challenger_keys.into_iter().enumerate().map(|(i, k)| k.ok_or_else(|| anyhow!("missing challenger keys for depth {}", i + 1))).collect::<Result<Vec<_>>>()?;
        ContractInstance::new(self.id, program, self.value, self.state, self.deadline, self.keys_seq, keys, ck)
    }
}

/// A contract output's tuple plus the Lamport keys for every depth.
#[derive(Clone, Debug)]
pub struct ContractInstance {
    pub id: u32,
    pub program: Arc<dyn Program>,
    pub value: Amount,
    pub state: Vec<bool>,
    /// Absolute height by which the party on turn must have moved (`OP_CLTV`).
    pub deadline: u32,
    /// Channel seq at which the keys were generated; the reveal labels are
    /// `key_label(id, keys_seq, depth, field)`.
    pub keys_seq: u64,
    /// Index `d - 1`.
    pub keys: Vec<DepthKeys>,
    /// Index `d - 1`; empty unless the program has a claim.
    pub challenger_keys: Vec<ChallengerKeys>,
    /// The terminal stages of each depth's dispute chain, built once and
    /// shared by both commitment versions (they do not depend on the
    /// outpoint); keyed by depth.
    terminal_cache: Arc<std::sync::Mutex<std::collections::HashMap<u32, crate::claim::TerminalStages>>>,
}

impl PartialEq for ContractInstance {
    fn eq(&self, o: &Self) -> bool {
        self.id == o.id && self.program.name() == o.program.name() && self.value == o.value
            && self.state == o.state && self.deadline == o.deadline && self.keys_seq == o.keys_seq && self.keys == o.keys
            && self.challenger_keys == o.challenger_keys
    }
}

impl ContractInstance {
    #[allow(clippy::too_many_arguments)]
    pub fn new(id: u32, program: Arc<dyn Program>, value: Amount, state: Vec<bool>, deadline: u32, keys_seq: u64, keys: Vec<DepthKeys>, challenger_keys: Vec<ChallengerKeys>) -> Result<ContractInstance> {
        ensure!(state.len() == program.n_state_bits(), "state has {} bits, program wants {}", state.len(), program.n_state_bits());
        let stall = program.graph_shape() == GraphShape::Stall;
        if stall {
            ensure!(keys.len() == STALL_KEY_SETS, "a stall graph has {STALL_KEY_SETS} key sets (stall and lie per role), got {}", keys.len());
        } else {
            let m = program.max_depth_from_bits(&state)? as usize;
            ensure!(keys.len() == m, "{} depth keys but M = {m}", keys.len());
        }
        let m = keys.len();
        let spec_at = |i: usize| if stall { stall_spec_at(&*program, i) } else { program.claim(&state, i as u32 + 1) };
        let has_claim = (0..m).any(|i| spec_at(i).is_some());
        if has_claim {
            ensure!(challenger_keys.len() == m, "{} challenger key sets but M = {m}", challenger_keys.len());
            for (i, (k, ck)) in keys.iter().zip(&challenger_keys).enumerate() {
                let d = i as u32 + 1;
                let Some(spec) = spec_at(i) else {
                    ensure!(k.claim.is_none() && ck.indices.is_empty(), "depth {d}: claim keys without a claim");
                    continue;
                };
                let rounds = spec.rounds() as usize;
                let c = k.claim.as_ref().ok_or_else(|| anyhow!("depth {d}: prover claim keys missing"))?;
                let nb = spec.wots_bytes() * 2;
                ensure!(c.end.params.message_digits == nb, "depth {d}: end key size");
                ensure!(c.rounds.len() == rounds && c.rounds.iter().all(|r| r.len() as u32 == spec.k - 1 && r.iter().all(|pk| pk.params.message_digits == nb)), "depth {d}: round keys");
                ensure!(ck.indices.len() == rounds && ck.indices.iter().all(|pk| pk.n_bits() == spec.index_bits()), "depth {d}: index keys");
                if spec.inner {
                    let ik = c.inner.as_ref().ok_or_else(|| anyhow!("depth {d}: inner keys missing"))?;
                    let ir = spec.inner_search().rounds() as usize;
                    ensure!(ik.re_cur.params.message_digits == nb && ik.re_next.params.message_digits == nb, "depth {d}: re-commitment keys");
                    ensure!(ik.block.len() == spec.hash.block_words(), "depth {d}: block keys");
                    if spec.has_schedule() {
                        ensure!(ik.sched.len() as u32 == spec.inner_rounds() - spec.hash.block_words() as u32, "depth {d}: schedule keys");
                    } else {
                        ensure!(ik.sched.is_empty(), "depth {d}: schedule keys on a hash without a schedule");
                    }
                    ensure!(ik.states.len() == ir && ik.states.iter().all(|r| r.len() as u32 == spec.inner_k() - 1), "depth {d}: inner state keys");
                    ensure!(ck.inner_indices.len() == ir && ck.inner_indices.iter().all(|pk| pk.n_bits() == spec.inner_search().index_bits()), "depth {d}: inner index keys");
                } else {
                    ensure!(c.inner.is_none() && ck.inner_indices.is_empty(), "depth {d}: inner keys on a flat claim");
                }
            }
        } else {
            ensure!(challenger_keys.is_empty() && keys.iter().all(|k| k.claim.is_none()), "claim keys on a program without a claim");
        }
        let mut prover = program.turn_bits(&state)?;
        let star = program.graph_shape() == GraphShape::Star;
        for (i, k) in keys.iter().enumerate() {
            ensure!(k.mv.n_bits() == program.n_move_bits(), "depth {}: move key size", i + 1);
            ensure!(k.state.n_bits() == program.n_state_bits(), "depth {}: state key size", i + 1);
            ensure!(k.code.n_bits() == CODE_BITS, "depth {}: code key size", i + 1);
            if stall {
                ensure!(k.prover == Role::BOTH[i % 2], "key set {i} should be {}'s", Role::BOTH[i % 2]);
                ensure!(k.prior.as_ref().map(|p| p.n_bits()) == Some(program.n_state_bits()), "{}: prior key", k.prover);
                ensure!(k.depth.as_ref().map(|p| p.n_bits()) == Some(DEPTH_BITS), "{}: depth key", k.prover);
                continue;
            }
            let p = prover.ok_or_else(|| anyhow!("keys for depth {} but the contract is terminal", i + 1))?;
            ensure!(k.prover == p, "depth {}: prover should be {p}", i + 1);
            if star {
                ensure!(k.state_n4.len() == program.n_state_bits(), "depth {}: claim-native state commitments", i + 1);
                ensure!(k.prior.as_ref().map(|p| p.n_bits()) == (i >= 1).then_some(program.n_state_bits()), "depth {}: prior key", i + 1);
            }
            prover = Some(p.other());
        }
        Ok(ContractInstance { id, program, value, state, deadline, keys_seq, keys, challenger_keys, terminal_cache: Default::default() })
    }

    /// The claim the `depth`-th move from this instance's state commits,
    /// with the keys' commitments bound in.
    pub fn claim_spec(&self, depth: u32) -> Option<ClaimSpec> {
        if self.graph_shape() == GraphShape::Stall {
            return stall_spec_at(&*self.program, depth as usize - 1);
        }
        self.program.claim_bound(&self.state, depth, &self.keys)
    }
    /// The served data for that claim.
    pub fn claim_data(&self, depth: u32) -> crate::claim::ClaimData {
        if self.graph_shape() == GraphShape::Stall {
            let i = depth as usize - 1;
            let role = Role::BOTH[i % 2];
            return match i / 2 {
                0 => self.program.stall_claim_data(role),
                1 => self.program.lie_claim_data(role),
                _ => self.program.sig_claim_data(role),
            };
        }
        self.program.claim_data(&self.state, depth)
    }
    /// Stall graphs: the index (1-based, as the depth-indexed API counts)
    /// of `role`'s stall key set.
    pub fn stall_index(role: Role) -> u32 {
        role.idx() as u32 + 1
    }
    /// Stall graphs: the index of `role`'s lie key set.
    pub fn lie_index(role: Role) -> u32 {
        role.idx() as u32 + 3
    }
    /// Stall graphs: is index `d` a lie exhibit's?
    pub fn is_lie_index(d: u32) -> bool {
        (3..=4).contains(&d)
    }
    /// Stall graphs: the index of `role`'s signature exhibit key set.
    pub fn sig_index(role: Role) -> u32 {
        role.idx() as u32 + 5
    }
    /// Stall graphs: is index `d` a signature exhibit's?
    pub fn is_sig_index(d: u32) -> bool {
        d >= 5
    }
    /// Stall graphs: is index `d` an exhibit's (a lie or a signature),
    /// judging the counterparty's entry?
    pub fn is_exhibit_index(d: u32) -> bool {
        d >= 3
    }
    /// Stall graphs: the role whose key set index `d` is.
    pub fn role_of_index(d: u32) -> Role {
        Role::BOTH[(d as usize - 1) % 2]
    }
    /// Stall graphs: the mover of the move an output at index `d` judges:
    /// the claimant for a stall proof, the counterparty for a lie exhibit.
    pub fn judged_mover(d: u32) -> Role {
        let r = Self::role_of_index(d);
        if Self::is_exhibit_index(d) { r.other() } else { r }
    }
    /// Stall graphs: the key set of `role`'s stall proof.
    pub fn role_keys(&self, role: Role) -> &DepthKeys {
        &self.keys[role.idx()]
    }
    pub fn stall_leaf_name(role: Role) -> String {
        format!("stall_{}", role.name())
    }
    pub fn lie_leaf_name(role: Role) -> String {
        format!("lie_{}", role.name())
    }
    pub fn sig_leaf_name(role: Role) -> String {
        format!("sig_{}", role.name())
    }
    /// The leaf name of key set index `d` on `C`.
    pub fn stall_graph_leaf_name(d: u32) -> String {
        let r = Self::role_of_index(d);
        if Self::is_sig_index(d) {
            Self::sig_leaf_name(r)
        } else if Self::is_lie_index(d) {
            Self::lie_leaf_name(r)
        } else {
            Self::stall_leaf_name(r)
        }
    }
    /// The key set index a stall-graph leaf name on `C` refers to.
    pub fn stall_graph_index(name: &str) -> Option<u32> {
        (1..=STALL_KEY_SETS as u32).find(|&d| Self::stall_graph_leaf_name(d) == name)
    }
    /// The graph label prefix of the spends of the output index `d` leads to.
    pub fn stall_graph_prefix(d: u32) -> String {
        format!("{}/", Self::stall_graph_leaf_name(d))
    }
    /// Stall graphs: the disprove leaves an output at index `d` carries,
    /// judging the move its reveals describe (the claimant's own for a stall
    /// proof, the counterparty's for a lie exhibit) under the index's keys.
    pub fn exhibit_specs(&self, d: u32) -> Vec<crate::DisproveSpec> {
        if Self::is_sig_index(d) {
            // a signature exhibit is judged by its claim alone
            return vec![];
        }
        let k = self.depth_keys(d);
        let lctx = LeafCtx {
            depth: d,
            prover: Self::judged_mover(d),
            prior: PriorState::Committed(k.prior.clone().expect("stall graphs carry a prior key")),
            mv: k.mv.clone(),
            new: k.state.clone(),
            code: k.code.clone(),
            outcomes: self.program.outcomes(),
            end: k.claim.as_ref().map(|c| c.end.clone()),
        };
        self.program.disprove_leaves(&lctx)
    }
    /// Does any depth carry a claim?
    pub fn has_claim(&self) -> bool {
        (1..=self.max_depth()).any(|d| self.claim_spec(d).is_some())
    }
    pub fn claim_keys(&self, depth: u32) -> Option<&ClaimKeys> {
        self.keys[depth as usize - 1].claim.as_ref()
    }
    pub fn challenger_keys(&self, depth: u32) -> Option<&ChallengerKeys> {
        self.challenger_keys.get(depth as usize - 1)
    }
    /// The terminal stages of the dispute chain at `depth`, memoised.
    fn terminal_stages(&self, ctx: &CommitCtx, depth: u32, spec: &ClaimSpec) -> Result<crate::claim::TerminalStages> {
        ensure!(spec.inner, "no terminal stages for a flat claim");
        if let Some(t) = self.terminal_cache.lock().unwrap().get(&depth) {
            return Ok(t.clone());
        }
        let t = crate::claim::terminal_stages(ctx, self.prover_at(depth), self.claim_keys(depth).unwrap(), self.challenger_keys(depth).unwrap(), spec)?;
        self.terminal_cache.lock().unwrap().insert(depth, t.clone());
        Ok(t)
    }
    /// The trees of the dispute chain at `depth`: `D_0, R_1, R_1', …, R_R'`.
    pub fn dispute_trees(&self, ctx: &CommitCtx, depth: u32) -> Result<Vec<TapTree>> {
        let spec = self.claim_spec(depth).ok_or_else(|| anyhow!("no claim at depth {depth}"))?;
        crate::claim::dispute_trees(ctx, self.prover_at(depth), self.claim_keys(depth).unwrap(), self.challenger_keys(depth).unwrap(), &spec)
    }

    pub fn spec(&self) -> InstanceSpec {
        InstanceSpec {
            id: self.id,
            program: self.program.name().to_string(),
            value: self.value,
            state: self.state.clone(),
            deadline: self.deadline,
            keys_seq: self.keys_seq,
            keys: self.keys.iter().cloned().map(Some).collect(),
            challenger_keys: self.challenger_keys.iter().cloned().map(Some).collect(),
        }
    }

    /// `M`: number of pre-signed move depths.
    pub fn max_depth(&self) -> u32 {
        self.keys.len() as u32
    }
    pub fn turn(&self) -> Option<Role> {
        self.program.turn_bits(&self.state).expect("valid state")
    }
    pub fn resolution(&self) -> Outcome {
        self.program.resolution_bits(&self.state).expect("valid state")
    }
    pub fn prover_at(&self, depth: u32) -> Role {
        self.keys[depth as usize - 1].prover
    }
    pub fn depth_keys(&self, depth: u32) -> &DepthKeys {
        &self.keys[depth as usize - 1]
    }
    /// Value of `C'_d` (`C` at depth 0).
    pub fn value_at_depth(&self, params: &ChannelParams, depth: u32) -> Amount {
        self.value - params.presign_fee * u64::from(depth)
    }
    /// Challenge window on `C'_d` for a claimed outcome (`Delta`, plus
    /// `Delta'` if the outcome favours the prover).
    pub fn window(&self, params: &ChannelParams, depth: u32, o: &Outcome) -> u16 {
        if self.graph_shape() == GraphShape::Stall && Self::is_lie_index(depth) {
            // the victim's disproof waits `delta`; the split waits longer
            return params.delta + params.delta_prime;
        }
        if self.graph_shape() == GraphShape::Stall && Self::is_sig_index(depth) {
            // the liar disputes within `delta`; then the split pays by the code
            return params.delta;
        }
        if o.payout.favours(self.prover_at(depth)) {
            params.delta + params.delta_prime
        } else {
            params.delta
        }
    }
    pub fn leaf_ctx(&self, depth: u32) -> LeafCtx {
        let k = self.depth_keys(depth);
        let prior = match self.prior_key(depth) {
            Some(pk) => PriorState::Committed(pk.clone()),
            None if depth == 1 => PriorState::Constant(self.state.clone()),
            None => PriorState::Committed(self.depth_keys(depth - 1).state.clone()),
        };
        LeafCtx { depth, prover: k.prover, prior, mv: k.mv.clone(), new: k.state.clone(), code: k.code.clone(), outcomes: self.program.outcomes(), end: None }
    }

    /// Payout outputs for `payout` of `v` to the parties' payout scripts.
    fn dist_outputs(&self, ctx: &CommitCtx, payout: crate::Payout, v: Amount) -> Vec<TxOut> {
        payout
            .dist(v)
            .iter()
            .zip(Role::BOTH)
            .filter(|(a, _)| **a >= ctx.params.dust)
            .map(|(a, r)| TxOut { value: *a, script_pubkey: ctx.key(r).payout_spk.clone() })
            .collect()
    }

    pub fn graph_shape(&self) -> GraphShape {
        self.program.graph_shape()
    }
    /// The key of the state a depth-`d` Move leaf must reveal as its prior
    /// (star graphs, `d ≥ 2`: the prover's own re-commitment of the
    /// counterparty's state, bound to the claim's copy of the venue entry).
    pub fn prior_key(&self, depth: u32) -> Option<&PublicKey> {
        match self.graph_shape() {
            GraphShape::Star if depth >= 2 => self.depth_keys(depth).prior.as_ref(),
            GraphShape::Stall => self.depth_keys(depth).prior.as_ref(),
            _ => None,
        }
    }
    /// Does the depth-`d` Move leaf carry a prior reveal?
    pub fn prior_bits(&self, depth: u32) -> Option<usize> {
        self.prior_key(depth).map(|k| k.n_bits())
    }
    fn move_leaf_at(&self, ctx: &CommitCtx, depth: u32, from_root: bool) -> Leaf {
        let k = self.depth_keys(depth);
        let ex = self.move_extras(depth);
        let name = if self.graph_shape() == GraphShape::Stall { Self::stall_graph_leaf_name(depth) } else { format!("move_{depth}") };
        move_leaf(ctx, &name, k.prover, self.prior_key(depth), &k.mv, &k.state, &k.code, k.depth.as_ref(), &ex, k.claim.as_ref().map(|c| &c.end), from_root)
    }

    /// Stall graphs: the tree of the output that key set index `d`'s leaf
    /// on `C` creates. A stall output (`d` in 1..=2): the dispute leaf, the
    /// splits, and the disprove leaves against the claimant's move, spent
    /// by the counterparty at once. A lie output (`d` in 3..=4): the
    /// dispute leaf (the liar), the disprove leaves against the exhibited
    /// move spent by the victim after `delta`, and the splits after
    /// `delta + delta'` (the liar's, by the code the victim revealed). A
    /// signature output (`d` in 5..=6): the dispute leaf (the liar) and the
    /// splits after `delta` (by the code the victim revealed).
    pub fn stall_graph_tree(&self, ctx: &CommitCtx, d: u32) -> Result<TapTree> {
        let k = self.depth_keys(d);
        let lie = Self::is_lie_index(d);
        let challenger = ctx.key(Self::judged_mover(d).other()).payment;
        let csv = if lie { ctx.params.delta } else { 0 };
        let mut leaves: Vec<Leaf> = self.exhibit_specs(d).iter().map(|s| s.leaf_after(&challenger, csv)).collect();
        leaves.push(dispute_leaf(ctx));
        for o in self.program.outcomes() {
            leaves.push(split_leaf(ctx, &o, self.window(ctx.params, d, &o), &k.code));
        }
        TapTree::new(leaves)
    }
    /// The tree of `role`'s stall output.
    pub fn stall_tree(&self, ctx: &CommitCtx, role: Role) -> Result<TapTree> {
        self.stall_graph_tree(ctx, Self::stall_index(role))
    }
    /// The tree of `role`'s lie output.
    pub fn lie_tree(&self, ctx: &CommitCtx, role: Role) -> Result<TapTree> {
        self.stall_graph_tree(ctx, Self::lie_index(role))
    }

    /// Stall graph: `settle`; per role the stall proof `stall_r` and the
    /// lie exhibit `lie_r` off `C`, each with its splits and dispute chain
    /// (labels prefixed `stall_r/` and `lie_r/`).
    fn graph_stall(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>> {
        let fee = ctx.params.presign_fee;
        let mut out = Vec::new();
        let tree0 = self.tree(ctx)?;
        let r = self.resolution();
        let settle_tx = build_spend(outpoint, &tree0.leaf("settle")?.timelock, self.dist_outputs(ctx, r.payout, self.value - fee));
        out.push(PresignedTx::new("settle", settle_tx, vec![prevout.clone()], &tree0, "settle", format!("settle: R(s) = {}", r.name))?);
        for d in 1..=STALL_KEY_SETS as u32 {
            let tree_d = self.stall_graph_tree(ctx, d)?;
            let leaf = Self::stall_graph_leaf_name(d);
            let tx = build_spend(outpoint, &tree0.leaf(&leaf)?.timelock, vec![TxOut { value: self.value - fee, script_pubkey: tree_d.script_pubkey() }]);
            let c_d = OutPoint { txid: tx.compute_txid(), vout: 0 };
            let c_d_prevout = tx.output[0].clone();
            let r = Self::role_of_index(d);
            let what = if Self::is_sig_index(d) {
                format!("signature exhibit by {r}")
            } else if Self::is_lie_index(d) {
                format!("lie exhibit by {r}")
            } else {
                format!("stall proof by {r}")
            };
            out.push(PresignedTx::new(leaf.clone(), tx, vec![prevout.clone()], &tree0, &leaf, what)?);
            self.push_splits_and_dispute(&mut out, ctx, d, &tree_d, c_d, &c_d_prevout, &Self::stall_graph_prefix(d))?;
        }
        Ok(out)
    }

    /// The tree of `C'_d` (`d ≥ 1`): disprove leaves, the next Move, the Splits.
    /// In a star graph this is the output of a claim; the next Move is the
    /// refutation (see [`ContractInstance::refuted_tree`]).
    pub fn depth_tree(&self, ctx: &CommitCtx, depth: u32) -> Result<TapTree> {
        self.depth_tree_with(ctx, depth, depth < self.max_depth())
    }
    /// The tree of the output of a refutation at `depth` (star graphs): as
    /// [`ContractInstance::depth_tree`] but with no further Move.
    pub fn refuted_tree(&self, ctx: &CommitCtx, depth: u32) -> Result<TapTree> {
        self.depth_tree_with(ctx, depth, false)
    }
    fn depth_tree_with(&self, ctx: &CommitCtx, depth: u32, next_move: bool) -> Result<TapTree> {
        ensure!(depth >= 1 && depth <= self.max_depth(), "depth {depth} out of range");
        let lctx = self.leaf_ctx(depth);
        let challenger = ctx.key(lctx.challenger()).payment;
        let mut leaves: Vec<Leaf> = self.disprove_specs(depth).iter().map(|d| d.leaf(&challenger)).collect();
        if next_move {
            leaves.push(self.move_leaf_at(ctx, depth + 1, false));
        }
        if self.claim_spec(depth).is_some() {
            leaves.push(dispute_leaf(ctx));
        }
        for o in self.program.outcomes() {
            leaves.push(split_leaf(ctx, &o, self.window(ctx.params, depth, &o), &lctx.code));
        }
        TapTree::new(leaves)
    }

    /// The Splits off a `C'_d`-shaped output and, if depth `d` carries a
    /// claim, its dispute chain; labels prefixed with `prefix`.
    #[allow(clippy::too_many_arguments)]
    fn push_splits_and_dispute(&self, out: &mut Vec<PresignedTx>, ctx: &CommitCtx, d: u32, tree_d: &TapTree, c_d: OutPoint, c_d_prevout: &TxOut, prefix: &str) -> Result<()> {
        let fee = ctx.params.presign_fee;
        for o in self.program.outcomes() {
            let leaf = format!("split_{}", o.name);
            let split_tx = build_spend(c_d, &tree_d.leaf(&leaf)?.timelock, self.dist_outputs(ctx, o.payout, c_d_prevout.value - fee));
            out.push(PresignedTx::new(format!("{prefix}split_{d}_{}", o.name), split_tx, vec![c_d_prevout.clone()], tree_d, &leaf, format!("split at depth {d}: {}", o.name))?);
        }
        if let Some(spec) = self.claim_spec(d) {
            let terminal = spec.inner.then(|| self.terminal_stages(ctx, d, &spec)).transpose()?;
            let chain = dispute_graph(ctx, self.prover_at(d), self.claim_keys(d).unwrap(), self.challenger_keys(d).unwrap(), &spec, tree_d, c_d, c_d_prevout, terminal.as_ref())?;
            for mut p in chain {
                p.label = format!("{prefix}d{d}/{}", p.label);
                out.push(p);
            }
        }
        Ok(())
    }

    /// Star graph: `settle`; for each depth `d` the claim `move_d` off `C`
    /// with its Splits and dispute chain, and (for `d < M`) the refutation
    /// `r{d}/move_{d+1}` off `C'_d` with `r{d}/split_{d+1}_X` and
    /// `r{d}/d{d+1}/…`.
    fn graph_star(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>> {
        let fee = ctx.params.presign_fee;
        let mut out = Vec::new();
        let tree0 = self.tree(ctx)?;
        let r = self.resolution();
        let settle_tx = build_spend(outpoint, &tree0.leaf("settle")?.timelock, self.dist_outputs(ctx, r.payout, self.value - fee));
        out.push(PresignedTx::new("settle", settle_tx, vec![prevout.clone()], &tree0, "settle", format!("settle: R(s) = {}", r.name))?);
        for d in 1..=self.max_depth() {
            let tree_d = self.depth_tree(ctx, d)?;
            let leaf = format!("move_{d}");
            let move_tx = build_spend(outpoint, &tree0.leaf(&leaf)?.timelock, vec![TxOut { value: self.value - fee, script_pubkey: tree_d.script_pubkey() }]);
            let c_d = OutPoint { txid: move_tx.compute_txid(), vout: 0 };
            let c_d_prevout = move_tx.output[0].clone();
            out.push(PresignedTx::new(leaf.clone(), move_tx, vec![prevout.clone()], &tree0, &leaf, format!("claim at depth {d} by {}", self.prover_at(d)))?);
            self.push_splits_and_dispute(&mut out, ctx, d, &tree_d, c_d, &c_d_prevout, "")?;
            if d < self.max_depth() {
                let tree_r = self.refuted_tree(ctx, d + 1)?;
                let leaf = format!("move_{}", d + 1);
                let ref_tx = build_spend(c_d, &tree_d.leaf(&leaf)?.timelock, vec![TxOut { value: c_d_prevout.value - fee, script_pubkey: tree_r.script_pubkey() }]);
                let c_r = OutPoint { txid: ref_tx.compute_txid(), vout: 0 };
                let c_r_prevout = ref_tx.output[0].clone();
                let prefix = format!("r{d}/");
                out.push(PresignedTx::new(format!("{prefix}{leaf}"), ref_tx, vec![c_d_prevout.clone()], &tree_d, &leaf, format!("refutation at depth {} by {}", d + 1, self.prover_at(d + 1)))?);
                self.push_splits_and_dispute(&mut out, ctx, d + 1, &tree_r, c_r, &c_r_prevout, &prefix)?;
            }
        }
        Ok(out)
    }

    /// Extras the Move at `depth` must reveal. A signature exhibit reveals
    /// only its outcome code and the claim's end state, whatever the game.
    pub fn move_extras(&self, depth: u32) -> MoveExtras {
        if self.graph_shape() == GraphShape::Stall && Self::is_sig_index(depth) {
            return MoveExtras { wots_only: true, ..MoveExtras::default() };
        }
        self.program.move_extras(depth, self.prover_at(depth))
    }

    /// The disprove specs at `depth` (for choosing which leaf to use).
    /// At depth 1 the prior state is a constant, so a leaf that reads only
    /// prior fields has a constant verdict; those that can never accept are
    /// dropped (they would also collide as identical scripts).
    pub fn disprove_specs(&self, depth: u32) -> Vec<crate::DisproveSpec> {
        if self.graph_shape() == GraphShape::Stall {
            return self.exhibit_specs(depth);
        }
        let lctx = self.leaf_ctx(depth);
        let specs = self.program.disprove_leaves(&lctx);
        match &lctx.prior {
            PriorState::Committed(_) => specs,
            PriorState::Constant(prior) => specs
                .into_iter()
                .filter(|s| {
                    let prior_only = s.consumes.iter().all(|f| matches!(f, crate::leaves::Field::Prior(_)));
                    if !prior_only {
                        return true;
                    }
                    let dummy = crate::Claim { prior: prior.clone(), mv: vec![false; self.program.n_move_bits()], new: vec![false; self.program.n_state_bits()], code: 0, mover: lctx.prover };
                    (s.detects)(&dummy)
                })
                .collect(),
        }
    }
}

impl ContractOutput for ContractInstance {
    fn id(&self) -> u32 {
        self.id
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn value(&self) -> Amount {
        self.value
    }
    /// Depth-0 tree: `revoke`, `settle`, and `move_1` if the contract is open
    /// (a star graph: `move_d` for every depth).
    fn tree(&self, ctx: &CommitCtx) -> Result<TapTree> {
        let mut leaves = vec![ctx.revoke_leaf(), settle_leaf(ctx, self.deadline)];
        match self.graph_shape() {
            GraphShape::Chain => {
                if self.max_depth() >= 1 {
                    leaves.push(self.move_leaf_at(ctx, 1, true));
                }
            }
            GraphShape::Star => {
                for d in 1..=self.max_depth() {
                    leaves.push(self.move_leaf_at(ctx, d, true));
                }
            }
            GraphShape::Stall => {
                for d in 1..=STALL_KEY_SETS as u32 {
                    leaves.push(self.move_leaf_at(ctx, d, true));
                }
            }
        }
        TapTree::new(leaves)
    }
    /// `settle`, then for each depth `move_d` and its `split_d_X`s.
    fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>> {
        match self.graph_shape() {
            GraphShape::Star => return self.graph_star(ctx, outpoint, prevout),
            GraphShape::Stall => return self.graph_stall(ctx, outpoint, prevout),
            GraphShape::Chain => {}
        }
        let fee = ctx.params.presign_fee;
        let mut out = Vec::new();
        let tree0 = self.tree(ctx)?;
        // Settle
        let r = self.resolution();
        let settle_tx = build_spend(outpoint, &tree0.leaf("settle")?.timelock, self.dist_outputs(ctx, r.payout, self.value - fee));
        out.push(PresignedTx::new("settle", settle_tx, vec![prevout.clone()], &tree0, "settle", format!("settle: R(s) = {}", r.name))?);
        // Move chain
        let mut parent_op = outpoint;
        let mut parent_prevout = prevout.clone();
        let mut parent_tree = tree0;
        for d in 1..=self.max_depth() {
            let tree_d = self.depth_tree(ctx, d)?;
            let v_d = self.value_at_depth(ctx.params, d);
            let leaf = format!("move_{d}");
            let move_tx = build_spend(parent_op, &parent_tree.leaf(&leaf)?.timelock, vec![TxOut { value: v_d, script_pubkey: tree_d.script_pubkey() }]);
            let ptx = PresignedTx::new(leaf.clone(), move_tx.clone(), vec![parent_prevout.clone()], &parent_tree, &leaf, format!("move_{d} by {}", self.prover_at(d)))?;
            let c_d = OutPoint { txid: move_tx.compute_txid(), vout: 0 };
            let c_d_prevout = move_tx.output[0].clone();
            out.push(ptx);
            for o in self.program.outcomes() {
                let leaf = format!("split_{}", o.name);
                let split_tx = build_spend(c_d, &tree_d.leaf(&leaf)?.timelock, self.dist_outputs(ctx, o.payout, v_d - fee));
                out.push(PresignedTx::new(format!("split_{d}_{}", o.name), split_tx, vec![c_d_prevout.clone()], &tree_d, &leaf, format!("split at depth {d}: {}", o.name))?);
            }
            if let Some(spec) = self.claim_spec(d) {
                let terminal = spec.inner.then(|| self.terminal_stages(ctx, d, &spec)).transpose()?;
                let chain = dispute_graph(ctx, self.prover_at(d), self.claim_keys(d).unwrap(), self.challenger_keys(d).unwrap(), &spec, &tree_d, c_d, &c_d_prevout, terminal.as_ref())?;
                for mut p in chain {
                    p.label = format!("d{d}/{}", p.label);
                    out.push(p);
                }
            }
            parent_op = c_d;
            parent_prevout = c_d_prevout;
            parent_tree = tree_d;
        }
        Ok(out)
    }
}
