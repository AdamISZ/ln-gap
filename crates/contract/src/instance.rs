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

use crate::leaves::{move_leaf, settle_leaf, split_leaf, LeafCtx, PriorState};
use crate::{MoveExtras, Outcome, Program, CODE_BITS};

/// The prover's Lamport public keys for one depth position.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DepthKeys {
    pub prover: Role,
    pub mv: PublicKey,
    pub state: PublicKey,
    pub code: PublicKey,
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
}

impl InstanceSpec {
    pub fn complete(&self) -> bool {
        self.keys.iter().all(Option::is_some)
    }
    pub fn into_instance(self, program: Arc<dyn Program>) -> Result<ContractInstance> {
        ensure!(program.name() == self.program, "program mismatch");
        let keys = self.keys.into_iter().enumerate().map(|(i, k)| k.ok_or_else(|| anyhow!("missing keys for depth {}", i + 1))).collect::<Result<Vec<_>>>()?;
        ContractInstance::new(self.id, program, self.value, self.state, self.deadline, self.keys_seq, keys)
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
}

impl PartialEq for ContractInstance {
    fn eq(&self, o: &Self) -> bool {
        self.id == o.id && self.program.name() == o.program.name() && self.value == o.value
            && self.state == o.state && self.deadline == o.deadline && self.keys_seq == o.keys_seq && self.keys == o.keys
    }
}

impl ContractInstance {
    pub fn new(id: u32, program: Arc<dyn Program>, value: Amount, state: Vec<bool>, deadline: u32, keys_seq: u64, keys: Vec<DepthKeys>) -> Result<ContractInstance> {
        ensure!(state.len() == program.n_state_bits(), "state has {} bits, program wants {}", state.len(), program.n_state_bits());
        let m = program.max_depth_from_bits(&state)? as usize;
        ensure!(keys.len() == m, "{} depth keys but M = {m}", keys.len());
        let mut prover = program.turn_bits(&state)?;
        for (i, k) in keys.iter().enumerate() {
            let p = prover.ok_or_else(|| anyhow!("keys for depth {} but the contract is terminal", i + 1))?;
            ensure!(k.prover == p, "depth {}: prover should be {p}", i + 1);
            ensure!(k.mv.n_bits() == program.n_move_bits(), "depth {}: move key size", i + 1);
            ensure!(k.state.n_bits() == program.n_state_bits(), "depth {}: state key size", i + 1);
            ensure!(k.code.n_bits() == CODE_BITS, "depth {}: code key size", i + 1);
            prover = Some(p.other());
        }
        Ok(ContractInstance { id, program, value, state, deadline, keys_seq, keys })
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
        if o.payout.favours(self.prover_at(depth)) {
            params.delta + params.delta_prime
        } else {
            params.delta
        }
    }
    pub fn leaf_ctx(&self, depth: u32) -> LeafCtx {
        let k = self.depth_keys(depth);
        let prior = if depth == 1 {
            PriorState::Constant(self.state.clone())
        } else {
            PriorState::Committed(self.depth_keys(depth - 1).state.clone())
        };
        LeafCtx { depth, prover: k.prover, prior, mv: k.mv.clone(), new: k.state.clone(), code: k.code.clone(), outcomes: self.program.outcomes() }
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

    /// The tree of `C'_d` (`d ≥ 1`): disprove leaves, the next Move, the Splits.
    pub fn depth_tree(&self, ctx: &CommitCtx, depth: u32) -> Result<TapTree> {
        ensure!(depth >= 1 && depth <= self.max_depth(), "depth {depth} out of range");
        let lctx = self.leaf_ctx(depth);
        let challenger = ctx.key(lctx.challenger()).payment;
        let mut leaves: Vec<Leaf> = self.disprove_specs(depth).iter().map(|d| d.leaf(&challenger)).collect();
        if depth < self.max_depth() {
            let nk = self.depth_keys(depth + 1);
            let ex = self.program.move_extras(depth + 1, nk.prover);
            leaves.push(move_leaf(ctx, depth + 1, nk.prover, &nk.mv, &nk.state, &nk.code, &ex));
        }
        for o in self.program.outcomes() {
            leaves.push(split_leaf(ctx, &o, self.window(ctx.params, depth, &o), &lctx.code));
        }
        TapTree::new(leaves)
    }

    /// Extras the Move at `depth` must reveal.
    pub fn move_extras(&self, depth: u32) -> MoveExtras {
        self.program.move_extras(depth, self.prover_at(depth))
    }

    /// The disprove specs at `depth` (for choosing which leaf to use).
    /// At depth 1 the prior state is a constant, so a leaf that reads only
    /// prior fields has a constant verdict; those that can never accept are
    /// dropped (they would also collide as identical scripts).
    pub fn disprove_specs(&self, depth: u32) -> Vec<crate::DisproveSpec> {
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
    /// Depth-0 tree: `revoke`, `settle`, and `move_1` if the contract is open.
    fn tree(&self, ctx: &CommitCtx) -> Result<TapTree> {
        let mut leaves = vec![ctx.revoke_leaf(), settle_leaf(ctx, self.deadline)];
        if self.max_depth() >= 1 {
            let k = self.depth_keys(1);
            let ex = self.program.move_extras(1, k.prover);
            leaves.push(move_leaf(ctx, 1, k.prover, &k.mv, &k.state, &k.code, &ex));
        }
        TapTree::new(leaves)
    }
    /// `settle`, then for each depth `move_d` and its `split_d_X`s.
    fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>> {
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
            parent_op = c_d;
            parent_prevout = c_d_prevout;
            parent_tree = tree_d;
        }
        Ok(out)
    }
}
