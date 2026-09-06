//! Off-chain state changes: how a proposed change turns into the next
//! channel state, and how the counterparty validates it.

use std::sync::Arc;

use anyhow::{anyhow, bail, ensure, Result};
use bitcoin::Amount;
use lngap_channel::{ChannelState, ContractOutput, Role};
use lngap_contract::instance::key_label;
use lngap_contract::{ContractInstance, DepthKeys, InstanceSpec, ProgramRegistry, CODE_BITS};
use lngap_lamport::keystore::KeyStore;
use serde::{Deserialize, Serialize};

/// What a party wants to change, in application terms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Change {
    Pay { from: Role, amount: Amount },
    /// Open a contract; each side stakes `stakes[role]`; `V = sum(stakes)`.
    Open { id: u32, program: String, stakes: [Amount; 2], deadline: u32 },
    /// The party on turn plays `mv`; the new deadline is for the next turn.
    Move { id: u32, mv: Vec<bool>, deadline: u32 },
    /// Fold a terminal contract's `R(s)` into the balances.
    Resolve { id: u32 },
    /// Fold a *non-terminal* contract's `R(s)` into the balances by mutual
    /// agreement (e.g. the party on turn has missed its deadline, or a bond
    /// is released). The responder's policy decides.
    Cancel { id: u32 },
}

impl Change {
    pub fn contract_id(&self) -> Option<u32> {
        match self {
            Change::Pay { .. } => None,
            Change::Open { id, .. } | Change::Move { id, .. } | Change::Resolve { id } | Change::Cancel { id } => Some(*id),
        }
    }
}

/// A channel state on the wire, with contracts as specs (keys may be partial).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateSpec {
    pub seq: u64,
    pub balances: [Amount; 2],
    pub contracts: Vec<InstanceSpec>,
}

impl StateSpec {
    pub fn from_state(st: &ChannelState) -> StateSpec {
        StateSpec {
            seq: st.seq,
            balances: st.balances,
            contracts: st.contracts.iter().map(|c| downcast(c).spec()).collect(),
        }
    }
    /// Equal ignoring Lamport keys (for validating a counterparty's draft).
    pub fn same_modulo_keys(&self, o: &StateSpec) -> bool {
        self.seq == o.seq
            && self.balances == o.balances
            && self.contracts.len() == o.contracts.len()
            && self.contracts.iter().zip(&o.contracts).all(|(a, b)| {
                a.id == b.id && a.program == b.program && a.value == b.value && a.state == b.state
                    && a.deadline == b.deadline && a.keys_seq == b.keys_seq && a.keys.len() == b.keys.len()
            })
    }
    pub fn into_state(self, programs: &ProgramRegistry) -> Result<ChannelState> {
        let mut contracts: Vec<Arc<dyn ContractOutput>> = Vec::new();
        for c in self.contracts {
            let p = programs.resolve(&c.program)?;
            contracts.push(Arc::new(c.into_instance(p)?));
        }
        Ok(ChannelState { seq: self.seq, balances: self.balances, contracts })
    }
}

pub fn downcast(c: &Arc<dyn ContractOutput>) -> &ContractInstance {
    c.as_any().downcast_ref::<ContractInstance>().expect("contract outputs are ContractInstances")
}

/// Do two channel states describe the same thing?
pub fn same_state(a: &ChannelState, b: &ChannelState) -> bool {
    a.seq == b.seq
        && a.balances == b.balances
        && a.contracts.len() == b.contracts.len()
        && a.contracts.iter().zip(&b.contracts).all(|(x, y)| downcast(x) == downcast(y))
}

/// Apply `change` to `current`, producing the next state's spec with every
/// key slot empty. Validates the change against the program.
pub fn apply_change(current: &ChannelState, change: &Change, programs: &ProgramRegistry) -> Result<StateSpec> {
    let mut spec = StateSpec::from_state(current);
    spec.seq += 1;
    let seq = spec.seq;
    match change {
        Change::Pay { from, amount } => {
            let f = from.idx();
            ensure!(spec.balances[f] >= *amount, "{from} cannot pay {amount}");
            spec.balances[f] -= *amount;
            spec.balances[from.other().idx()] += *amount;
        }
        Change::Open { id, program, stakes, deadline } => {
            ensure!(spec.contracts.iter().all(|c| c.id != *id), "contract {id} already exists");
            let p = programs.resolve(program)?;
            for r in Role::BOTH {
                ensure!(spec.balances[r.idx()] >= stakes[r.idx()], "{r} cannot stake {}", stakes[r.idx()]);
                spec.balances[r.idx()] -= stakes[r.idx()];
            }
            let state = p.initial_bits();
            let m = p.max_depth_from_bits(&state)?;
            spec.contracts.push(InstanceSpec {
                id: *id,
                program: program.clone(),
                value: stakes[0] + stakes[1],
                state,
                deadline: *deadline,
                keys_seq: seq,
                keys: vec![None; m as usize],
            });
        }
        Change::Move { id, mv, deadline } => {
            let c = spec.contracts.iter_mut().find(|c| c.id == *id).ok_or_else(|| anyhow!("no contract {id}"))?;
            let p = programs.resolve(&c.program)?;
            let mover = p.turn_bits(&c.state)?.ok_or_else(|| anyhow!("contract {id} is terminal"))?;
            let new = p.transition_bits(&c.state, mv, mover)?;
            let m = p.max_depth_from_bits(&new)?;
            c.state = new;
            c.deadline = *deadline;
            c.keys_seq = seq;
            c.keys = vec![None; m as usize];
        }
        Change::Resolve { id } | Change::Cancel { id } => {
            let pos = spec.contracts.iter().position(|c| c.id == *id).ok_or_else(|| anyhow!("no contract {id}"))?;
            let c = spec.contracts.remove(pos);
            let p = programs.resolve(&c.program)?;
            if matches!(change, Change::Resolve { .. }) {
                ensure!(p.turn_bits(&c.state)?.is_none(), "contract {id} is not terminal");
            }
            let r = p.resolution_bits(&c.state)?;
            let d = r.payout.dist(c.value);
            spec.balances[0] += d[0];
            spec.balances[1] += d[1];
        }
    }
    Ok(spec)
}

/// Fill in `me`'s keys for every depth where `me` is the prover and the
/// slot is empty. Returns what was filled (to send to the counterparty).
pub fn fill_my_keys(spec: &mut StateSpec, me: Role, ks: &mut KeyStore, programs: &ProgramRegistry) -> Result<Vec<(u32, u32, DepthKeys)>> {
    let mut filled = Vec::new();
    for c in &mut spec.contracts {
        let p = programs.resolve(&c.program)?;
        let mut prover = p.turn_bits(&c.state)?;
        for (i, slot) in c.keys.iter_mut().enumerate() {
            let d = i as u32 + 1;
            let pr = prover.ok_or_else(|| anyhow!("depth {d} beyond terminal"))?;
            if pr == me && slot.is_none() {
                let k = DepthKeys {
                    prover: me,
                    mv: ks.generate(&key_label(c.id, c.keys_seq, d, "move"), p.n_move_bits())?,
                    state: ks.generate(&key_label(c.id, c.keys_seq, d, "state"), p.n_state_bits())?,
                    code: ks.generate(&key_label(c.id, c.keys_seq, d, "code"), CODE_BITS)?,
                };
                filled.push((c.id, d, k.clone()));
                *slot = Some(k);
            }
            prover = Some(pr.other());
        }
    }
    Ok(filled)
}

/// Merge the counterparty's keys into the spec, checking they land in
/// slots that belong to the counterparty.
pub fn merge_keys(spec: &mut StateSpec, from: Role, keys: Vec<(u32, u32, DepthKeys)>) -> Result<()> {
    for (id, d, k) in keys {
        let c = spec.contracts.iter_mut().find(|c| c.id == id).ok_or_else(|| anyhow!("keys for unknown contract {id}"))?;
        ensure!(k.prover == from, "{from} sent keys claiming prover {}", k.prover);
        let slot = c.keys.get_mut(d as usize - 1).ok_or_else(|| anyhow!("keys for depth {d} out of range"))?;
        ensure!(slot.is_none(), "keys for contract {id} depth {d} already present");
        *slot = Some(k);
    }
    if !spec.contracts.iter().all(InstanceSpec::complete) {
        bail!("state spec still has empty key slots after merge");
    }
    Ok(())
}
