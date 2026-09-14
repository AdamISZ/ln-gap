//! Off-chain state changes: how a proposed change turns into the next
//! channel state, and how the counterparty validates it.

use std::sync::Arc;

use anyhow::{anyhow, bail, ensure, Result};
use bitcoin::Amount;
use lngap_channel::{ChannelState, ContractOutput, Role};
use lngap_contract::claim::{end_label, index_label, round_label};
use lngap_contract::inner::{self, InnerKeys};
use lngap_contract::instance::key_label;
use lngap_contract::{ChallengerKeys, ClaimKeys, ContractInstance, DepthKeys, GraphShape, InstanceSpec, ProgramRegistry, CODE_BITS};
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
    /// Fold a contract with an agreed distribution of its value (a game
    /// whose result lives elsewhere than the contract's state). The
    /// responder's policy must accept it explicitly.
    Fold { id: u32, dist: [Amount; 2] },
}

impl Change {
    pub fn contract_id(&self) -> Option<u32> {
        match self {
            Change::Pay { .. } => None,
            Change::Open { id, .. } | Change::Move { id, .. } | Change::Resolve { id } | Change::Cancel { id } | Change::Fold { id, .. } => Some(*id),
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
                    && a.challenger_keys.len() == b.challenger_keys.len()
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
            let has_claim = (1..=m).any(|d| p.claim(&state, d).is_some());
            spec.contracts.push(InstanceSpec {
                id: *id,
                program: program.clone(),
                value: stakes[0] + stakes[1],
                state,
                deadline: *deadline,
                keys_seq: seq,
                keys: vec![None; m as usize],
                challenger_keys: if has_claim { vec![None; m as usize] } else { vec![] },
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
            c.challenger_keys = if (1..=m).any(|d| p.claim(&c.state, d).is_some()) { vec![None; m as usize] } else { vec![] };
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
        Change::Fold { id, dist } => {
            let pos = spec.contracts.iter().position(|c| c.id == *id).ok_or_else(|| anyhow!("no contract {id}"))?;
            let c = spec.contracts.remove(pos);
            ensure!(dist[0] + dist[1] == c.value, "fold of contract {id} distributes {} + {} but it holds {}", dist[0], dist[1], c.value);
            spec.balances[0] += dist[0];
            spec.balances[1] += dist[1];
        }
    }
    Ok(spec)
}

/// Keys one party contributes to a draft: its prover keys per depth, and
/// its challenger (dispute index) keys per depth for programs with a claim.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct MyKeys {
    pub prover: Vec<(u32, u32, DepthKeys)>,
    pub challenger: Vec<(u32, u32, ChallengerKeys)>,
}

/// Fill in `me`'s keys for every depth and empty slot. Returns what was
/// filled (to send to the counterparty).
pub fn fill_my_keys(spec: &mut StateSpec, me: Role, ks: &mut KeyStore, programs: &ProgramRegistry) -> Result<MyKeys> {
    let mut filled = MyKeys::default();
    for c in &mut spec.contracts {
        let p = programs.resolve(&c.program)?;
        let has_claim = (1..=c.keys.len() as u32).any(|d| p.claim(&c.state, d).is_some());
        let mut prover = p.turn_bits(&c.state)?;
        for i in 0..c.keys.len() {
            let d = i as u32 + 1;
            let pr = prover.ok_or_else(|| anyhow!("depth {d} beyond terminal"))?;
            let claim = p.claim(&c.state, d);
            if pr == me && c.keys[i].is_none() {
                let claim_keys = match &claim {
                    Some(spec) => {
                        let nb = spec.wots_bytes();
                        Some(ClaimKeys {
                            end: ks.generate_wots(&end_label(c.id, c.keys_seq, d), nb)?,
                            rounds: (1..=spec.rounds())
                                .map(|r| (0..spec.k - 1).map(|t| ks.generate_wots(&round_label(c.id, c.keys_seq, d, r, t), nb)).collect::<Result<Vec<_>>>())
                                .collect::<Result<Vec<_>>>()?,
                            inner: if spec.inner {
                                Some(InnerKeys {
                                    re_cur: ks.generate_wots(&inner::re_cur_label(c.id, c.keys_seq, d), nb)?,
                                    re_next: ks.generate_wots(&inner::re_next_label(c.id, c.keys_seq, d), nb)?,
                                    block: (0..spec.hash.block_words()).map(|j| ks.generate_wots(&inner::block_label(c.id, c.keys_seq, d, j as u32), 4)).collect::<Result<Vec<_>>>()?,
                                    sched: if spec.has_schedule() {
                                        ((spec.hash.block_words() as u32)..spec.inner_rounds()).map(|i| ks.generate_wots(&inner::sched_label(c.id, c.keys_seq, d, i), 4)).collect::<Result<Vec<_>>>()?
                                    } else {
                                        vec![]
                                    },
                                    states: (1..=spec.inner_search().rounds())
                                        .map(|r| (0..spec.inner_k() - 1).map(|t| ks.generate_wots(&inner::inner_state_label(c.id, c.keys_seq, d, r, t), (spec.d_words() * 4) as u32)).collect::<Result<Vec<_>>>())
                                        .collect::<Result<Vec<_>>>()?,
                                })
                            } else {
                                None
                            },
                        })
                    }
                    None => None,
                };
                let star = p.graph_shape() == GraphShape::Star;
                let state_label = key_label(c.id, c.keys_seq, d, "state");
                let state = ks.generate(&state_label, p.n_state_bits())?;
                let k = DepthKeys {
                    prover: me,
                    mv: ks.generate(&key_label(c.id, c.keys_seq, d, "move"), p.n_move_bits())?,
                    state,
                    code: ks.generate(&key_label(c.id, c.keys_seq, d, "code"), CODE_BITS)?,
                    claim: claim_keys,
                    prior: if star && d >= 2 { Some(ks.generate(&key_label(c.id, c.keys_seq, d, "prior"), p.n_state_bits())?) } else { None },
                    state_n4: if star { ks.commit_with(&state_label, |p| lngap_n4bit::hash_claim(p))? } else { vec![] },
                };
                filled.prover.push((c.id, d, k.clone()));
                c.keys[i] = Some(k);
            }
            if has_claim && pr != me && c.challenger_keys[i].is_none() {
                let ck = match &claim {
                    Some(spec) => ChallengerKeys {
                        indices: (1..=spec.rounds()).map(|r| ks.generate(&index_label(c.id, c.keys_seq, d, r), spec.index_bits())).collect::<Result<Vec<_>>>()?,
                        inner_indices: if spec.inner {
                            (1..=spec.inner_search().rounds()).map(|r| ks.generate(&inner::inner_index_label(c.id, c.keys_seq, d, r), spec.inner_search().index_bits())).collect::<Result<Vec<_>>>()?
                        } else {
                            vec![]
                        },
                    },
                    None => ChallengerKeys { indices: vec![], inner_indices: vec![] },
                };
                filled.challenger.push((c.id, d, ck.clone()));
                c.challenger_keys[i] = Some(ck);
            }
            prover = Some(pr.other());
        }
    }
    Ok(filled)
}

/// Merge the counterparty's keys into the spec, checking they land in
/// slots that belong to the counterparty.
pub fn merge_keys(spec: &mut StateSpec, from: Role, keys: MyKeys) -> Result<()> {
    for (id, d, k) in keys.prover {
        let c = spec.contracts.iter_mut().find(|c| c.id == id).ok_or_else(|| anyhow!("keys for unknown contract {id}"))?;
        ensure!(k.prover == from, "{from} sent keys claiming prover {}", k.prover);
        let slot = c.keys.get_mut(d as usize - 1).ok_or_else(|| anyhow!("keys for depth {d} out of range"))?;
        ensure!(slot.is_none(), "keys for contract {id} depth {d} already present");
        *slot = Some(k);
    }
    for (id, d, ck) in keys.challenger {
        let c = spec.contracts.iter_mut().find(|c| c.id == id).ok_or_else(|| anyhow!("keys for unknown contract {id}"))?;
        let prover_here = c.keys.get(d as usize - 1).and_then(|k| k.as_ref().map(|k| k.prover));
        ensure!(prover_here != Some(from), "{from} sent challenger keys for a depth where it is the prover");
        let slot = c.challenger_keys.get_mut(d as usize - 1).ok_or_else(|| anyhow!("challenger keys for depth {d} out of range"))?;
        ensure!(slot.is_none(), "challenger keys for contract {id} depth {d} already present");
        *slot = Some(ck);
    }
    if !spec.contracts.iter().all(InstanceSpec::complete) {
        bail!("state spec still has empty key slots after merge");
    }
    Ok(())
}
