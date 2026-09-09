//! Party behaviour for bisection disputes over a contract's claim.
//!
//! The challenger disputes a Move whose claimed end state disagrees with its
//! own computation; the prover answers rounds with committed midstates; the
//! challenger narrows to one step and disproves it with the terminal leaf;
//! whoever fails to respond within Δ loses by the timeout leaf.

use std::collections::HashMap;

use anyhow::{anyhow, ensure, Result};
use bitcoin::{OutPoint, Transaction, TxOut};
use lngap_btc::taptree::TapTree;
use lngap_btc::witness::witness_args_consumption_order;
use lngap_channel::Role;
use lngap_contract::claim::{index_label, round_label, step_sources, step_witness, ClaimSpec, StateSource};
use lngap_contract::script_hash::state_bytes;
use lngap_lamport::winternitz::WotsSig;
use lngap_lamport::{bits_to_uint, Reveal};

/// The stage a dispute is in: whose response the current output waits for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stage {
    /// `D_0` or `R_{r-1}'`: waiting for the prover's round `r`.
    WaitP(u32),
    /// `R_r`: waiting for the challenger's segment index for round `r`.
    WaitQ(u32),
    /// `R_R'`: the challenger may disprove the isolated step; else the prover times out.
    Terminal,
    Resolved,
}

#[derive(Clone, Debug)]
pub struct DisputeLive {
    pub depth: u32,
    pub prover: Role,
    pub spec: ClaimSpec,
    pub stage: Stage,
    /// Prover commitments seen on-chain: step index → (state, signature).
    pub known: HashMap<u32, ([u32; 8], WotsSig)>,
    pub path: Vec<u32>,
    pub outpoint: OutPoint,
    pub prevout: TxOut,
    pub tree: TapTree,
    pub confirmed_at: u32,
    /// `D_0, R_1, R_1', …, R_R'` for leaf identification along the chain.
    pub trees: Vec<TapTree>,
    /// This party's own computation of the chain (with a cheating prover's alterations).
    pub my_states: Vec<[u32; 8]>,
    pub responded: bool,
}

impl DisputeLive {
    /// Which tree along the chain the current stage's output uses.
    pub fn tree_index(&self) -> usize {
        match self.stage {
            Stage::WaitP(r) => 2 * (r as usize - 1),
            Stage::WaitQ(r) => 2 * r as usize - 1,
            Stage::Terminal => self.trees.len() - 1,
            Stage::Resolved => self.trees.len() - 1,
        }
    }
    /// Who must act at the current stage (the other party can time them out).
    pub fn waiting_for(&self) -> Option<Role> {
        match self.stage {
            Stage::WaitP(_) => Some(self.prover),
            Stage::WaitQ(_) | Stage::Terminal => Some(self.prover.other()),
            Stage::Resolved => None,
        }
    }
    /// The challenger's index for round `r`, given the prover's commitments
    /// for that round: the first segment whose end state the prover got
    /// wrong, or the last segment if all commitments match.
    pub fn choose_index(&self) -> u32 {
        let points = self.spec.round_points(&self.path);
        for (t, idx) in points.iter().enumerate() {
            match self.known.get(idx) {
                Some((st, _)) if *st == self.my_states[*idx as usize] => continue,
                _ => return t as u32,
            }
        }
        self.spec.k - 1
    }
}

/// Parse the prover's `p_round_r` witness into `(index, state, sig)` triples.
pub fn parse_p_round(tx: &Transaction, keys: &lngap_contract::ClaimKeys, spec: &ClaimSpec, path: &[u32], r: u32) -> Result<Vec<(u32, [u32; 8], WotsSig)>> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let pks = &keys.rounds[r as usize - 1];
    let per = 2 * pks[0].params.total_digits() as usize;
    ensure!(args.len() == 2 + per * pks.len(), "p_round_{r}: witness has {} args", args.len());
    let points = spec.round_points(path);
    let mut out = Vec::new();
    for (t, pk) in pks.iter().enumerate() {
        let sig = WotsSig::from_consumption_order(pk.params, &args[2 + t * per..2 + (t + 1) * per])?;
        let msg = pk.verify(&sig)?;
        let mut st = [0u32; 8];
        for (i, w) in st.iter_mut().enumerate() {
            *w = u32::from_be_bytes(msg[4 * i..4 * i + 4].try_into().unwrap());
        }
        out.push((points[t], st, sig));
    }
    Ok(out)
}

/// Parse the challenger's `q_round_r` witness into its segment index.
pub fn parse_q_round(tx: &Transaction, ck: &lngap_contract::ChallengerKeys, r: u32) -> Result<u32> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let pk = &ck.indices[r as usize - 1];
    ensure!(args.len() == 2 + pk.n_bits(), "q_round_{r}: witness has {} args", args.len());
    let reveal = Reveal::from_consumption_order(&args[2..])?;
    Ok(bits_to_uint(&pk.decode_bits(&reveal)?))
}

/// The terminal leaf's witness args for the dispute's path (after Q's signature).
pub fn terminal_witness(d: &DisputeLive) -> Result<Vec<Vec<u8>>> {
    let (cur, _next, step) = step_sources(&d.spec, &d.path);
    let n = d.spec.n_steps;
    let sig_for = |src: &StateSource| -> Result<Option<WotsSig>> {
        Ok(match src {
            StateSource::Const(_) => None,
            StateSource::End => Some(d.known.get(&n).ok_or_else(|| anyhow!("end state unknown"))?.1.clone()),
            StateSource::Round(_, _) => {
                // the state at the segment boundary: index = step (for cur) or step + 1 (for next)
                None
            }
        })
    };
    let _ = sig_for;
    let cur_sig = match &cur {
        StateSource::Const(_) => None,
        _ => Some(d.known.get(&step).ok_or_else(|| anyhow!("state {step} unknown"))?.1.clone()),
    };
    let next_sig = d.known.get(&(step + 1)).ok_or_else(|| anyhow!("state {} unknown", step + 1))?.1.clone();
    Ok(step_witness(&cur, &next_sig, cur_sig.as_ref()))
}

/// Labels of the keys a prover reveals in round `r`.
pub fn round_labels(id: u32, keys_seq: u64, depth: u32, k: u32, r: u32) -> Vec<String> {
    (0..k - 1).map(|t| round_label(id, keys_seq, depth, r, t)).collect()
}
pub fn my_index_label(id: u32, keys_seq: u64, depth: u32, r: u32) -> String {
    index_label(id, keys_seq, depth, r)
}

pub fn state_msg(s: &[u32; 8]) -> [u8; 32] {
    state_bytes(s)
}
