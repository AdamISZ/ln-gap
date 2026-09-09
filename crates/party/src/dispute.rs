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
use lngap_contract::inner::{self, round_sources, round_witness, sched_inputs, sched_witness, InnerSource};
use lngap_contract::script_hash::state_bytes;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_lamport::{bits_to_uint, Reveal};
use lngap_script32::sha::{round_native, K};

/// The stage a dispute is in: whose response the current output waits for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stage {
    /// `D_0` or `R_{r-1}'`: waiting for the prover's round `r`.
    WaitP(u32),
    /// `R_r`: waiting for the challenger's segment index for round `r`.
    WaitQ(u32),
    /// `R_R'` (flat claims): the challenger may disprove the isolated step; else the prover times out.
    Terminal,
    /// `R_R'` (two-level claims): waiting for the prover's schedule words.
    WaitSched,
    /// `S_r`: waiting for the prover's inner round `r` states.
    WaitInnerP(u32),
    /// `I_r`: waiting for the challenger's inner index `r` (or, in round 1, a schedule disproof).
    WaitInnerQ(u32),
    /// `T`: the challenger may disprove the isolated round; else the prover times out.
    RoundTerminal,
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
    // ----- inner level -----
    /// Prover's schedule words seen on-chain: index → (word, signature).
    pub sched: HashMap<u32, (u32, WotsSig)>,
    /// Prover's inner states seen on-chain: round index (1..64) → (state, signature).
    pub inner_known: HashMap<u32, ([u32; 8], WotsSig)>,
    pub inner_path: Vec<u32>,
    /// This party's own schedule and round states for the isolated step
    /// (with a cheating prover's alterations); set on entering the inner level.
    pub my_sched: Option<[u32; 64]>,
    pub my_inner: Option<Vec<[u32; 8]>>,
}

impl DisputeLive {
    /// Which tree along the chain the current stage's output uses.
    pub fn tree_index(&self) -> usize {
        let outer = 2 * self.spec.rounds() as usize;
        match self.stage {
            Stage::WaitP(r) => 2 * (r as usize - 1),
            Stage::WaitQ(r) => 2 * r as usize - 1,
            Stage::Terminal => self.trees.len() - 1,
            Stage::WaitSched => outer,
            Stage::WaitInnerP(r) => outer + 2 * r as usize - 1,
            Stage::WaitInnerQ(r) => outer + 2 * r as usize,
            Stage::RoundTerminal => self.trees.len() - 1,
            Stage::Resolved => self.trees.len() - 1,
        }
    }
    /// Who must act at the current stage (the other party can time them out).
    pub fn waiting_for(&self) -> Option<Role> {
        match self.stage {
            Stage::WaitP(_) | Stage::WaitSched | Stage::WaitInnerP(_) => Some(self.prover),
            Stage::WaitQ(_) | Stage::Terminal | Stage::WaitInnerQ(_) | Stage::RoundTerminal => Some(self.prover.other()),
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
    /// The isolated compression step after the level-1 rounds: `(cur source, next source, step)`.
    pub fn isolated_step(&self) -> (StateSource, StateSource, u32) {
        step_sources(&self.spec, &self.path)
    }
    /// The prover's committed (or constant) value of an inner state, `0 ↔ cur`, `64 ↔ next`.
    pub fn inner_state(&self, i: u32) -> Option<[u32; 8]> {
        let (cur_src, _, step) = self.isolated_step();
        match i {
            0 => match cur_src {
                StateSource::Const(s) => Some(s),
                _ => self.known.get(&step).map(|k| k.0),
            },
            64 => self.known.get(&(step + 1)).map(|k| k.0),
            _ => self.inner_known.get(&i).map(|k| k.0),
        }
    }
    /// The signature behind an inner state (None for a constant `cur`).
    pub fn inner_sig(&self, i: u32) -> Result<Option<WotsSig>> {
        let (cur_src, _, step) = self.isolated_step();
        Ok(match i {
            0 => match cur_src {
                StateSource::Const(_) => None,
                _ => Some(self.known.get(&step).ok_or_else(|| anyhow!("state {step} unknown"))?.1.clone()),
            },
            64 => Some(self.known.get(&(step + 1)).ok_or_else(|| anyhow!("state {} unknown", step + 1))?.1.clone()),
            _ => Some(self.inner_known.get(&i).ok_or_else(|| anyhow!("inner state {i} unknown"))?.1.clone()),
        })
    }
    /// The block of the isolated step.
    pub fn block(&self) -> [u8; 64] {
        self.spec.blocks[self.isolated_step().2 as usize]
    }
    /// The challenger's inner index: the first segment whose end state the
    /// prover got wrong, or the last segment.
    pub fn choose_inner_index(&self) -> u32 {
        let mine = self.my_inner.as_ref().expect("inner computation");
        let points = inner::SEARCH.round_points(&self.inner_path);
        for (t, i) in points.iter().enumerate() {
            match self.inner_state(*i) {
                Some(st) if st == mine[*i as usize] => continue,
                _ => return t as u32,
            }
        }
        inner::INNER_K - 1
    }
    /// The first schedule word the prover got wrong, if any.
    pub fn first_bad_sched(&self) -> Option<u32> {
        let mine = self.my_sched.as_ref().expect("inner computation");
        (16..inner::ROUNDS).find(|i| self.sched.get(i).map(|s| s.0) != Some(mine[*i as usize]))
    }
    /// The prover's schedule word `i` (a block constant below 16).
    pub fn sched_word(&self, i: u32) -> Option<u32> {
        if i < 16 {
            let b = self.block();
            Some(u32::from_be_bytes(b[4 * i as usize..4 * i as usize + 4].try_into().unwrap()))
        } else {
            self.sched.get(&i).map(|s| s.0)
        }
    }
    /// Recompute the isolated round `r` natively from the prover's commitments:
    /// `(expected s_{r+1}, claimed s_{r+1})`.
    pub fn check_round(&self, r: u32) -> Result<([u32; 8], [u32; 8])> {
        let s_in = self.inner_state(r).ok_or_else(|| anyhow!("no inner state {r}"))?;
        let w = self.sched_word(r).ok_or_else(|| anyhow!("no schedule word {r}"))?;
        let mut expect = round_native(&s_in, w, K[r as usize]);
        if r == 63 {
            let cur = self.inner_state(0).ok_or_else(|| anyhow!("no cur"))?;
            for i in 0..8 {
                expect[i] = expect[i].wrapping_add(cur[i]);
            }
        }
        let claimed = self.inner_state(r + 1).ok_or_else(|| anyhow!("no inner state {}", r + 1))?;
        Ok((expect, claimed))
    }
    /// Witness args (after Q's signature) and leaf name for disproving round `r`.
    pub fn round_disproof(&self, ctx: &lngap_channel::CommitCtx, keys: &lngap_contract::ClaimKeys, r: u32) -> Result<(String, Vec<Vec<u8>>)> {
        let (cur_src, next_src, _) = self.isolated_step();
        let (name, _) = inner::round_leaf(ctx, self.prover, keys, &cur_src, &next_src, &self.block(), r);
        let (in_src, _, _) = round_sources(&cur_src, &next_src, &[r / inner::INNER_K, r % inner::INNER_K]);
        let w_sig = if r >= 16 { Some(self.sched.get(&r).ok_or_else(|| anyhow!("no schedule word {r}"))?.1.clone()) } else { None };
        let in_sig = match in_src {
            InnerSource::Outer(StateSource::Const(_)) => None,
            _ => self.inner_sig(r)?,
        };
        let cur_sig = if r == 63 { self.inner_sig(0)? } else { None };
        let out_sig = self.inner_sig(r + 1)?.expect("the output is always committed");
        Ok((name, round_witness(w_sig.as_ref(), in_sig.as_ref(), cur_sig.as_ref(), &out_sig)))
    }
    /// Witness args and leaf name for disproving schedule word `i`.
    pub fn sched_disproof(&self, ctx: &lngap_channel::CommitCtx, keys: &lngap_contract::ClaimKeys, i: u32) -> Result<(String, Vec<Vec<u8>>)> {
        let (name, _) = inner::sched_leaf(ctx, self.prover, keys, &self.block(), i);
        let mut inputs = Vec::new();
        for j in sched_inputs(i) {
            if j >= 16 {
                inputs.push(self.sched.get(&j).ok_or_else(|| anyhow!("no schedule word {j}"))?.1.clone());
            }
        }
        let refs: Vec<&WotsSig> = inputs.iter().collect();
        let w_sig = &self.sched.get(&i).ok_or_else(|| anyhow!("no schedule word {i}"))?.1;
        Ok((name, sched_witness(&refs, w_sig)))
    }
}

/// Split witness args into one signature per key and verify each; returns the messages.
fn parse_wots_list(args: &[Vec<u8>], pks: &[WotsPublic], what: &str) -> Result<Vec<(Vec<u8>, WotsSig)>> {
    let mut out = Vec::new();
    let mut at = 0;
    for pk in pks {
        let per = 2 * pk.params.total_digits() as usize;
        ensure!(args.len() >= at + per, "{what}: witness too short");
        let sig = WotsSig::from_consumption_order(pk.params, &args[at..at + per])?;
        let msg = pk.verify(&sig)?;
        out.push((msg, sig));
        at += per;
    }
    ensure!(at == args.len(), "{what}: {} trailing witness args", args.len() - at);
    Ok(out)
}

fn state_from_msg(msg: &[u8]) -> [u32; 8] {
    let mut st = [0u32; 8];
    for (i, w) in st.iter_mut().enumerate() {
        *w = u32::from_be_bytes(msg[4 * i..4 * i + 4].try_into().unwrap());
    }
    st
}

/// Parse the prover's `p_sched` witness into `(index, word, sig)` triples.
pub fn parse_p_sched(tx: &Transaction, keys: &lngap_contract::ClaimKeys) -> Result<Vec<(u32, u32, WotsSig)>> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let ik = keys.inner.as_ref().ok_or_else(|| anyhow!("no inner keys"))?;
    let list = parse_wots_list(&args[2..], &ik.sched, "p_sched")?;
    Ok(list.into_iter().enumerate().map(|(k, (msg, sig))| (16 + k as u32, u32::from_be_bytes(msg[..4].try_into().unwrap()), sig)).collect())
}

/// Parse the prover's `p_inner_r` witness into `(round index, state, sig)` triples.
pub fn parse_p_inner(tx: &Transaction, keys: &lngap_contract::ClaimKeys, inner_path: &[u32], r: u32) -> Result<Vec<(u32, [u32; 8], WotsSig)>> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let ik = keys.inner.as_ref().ok_or_else(|| anyhow!("no inner keys"))?;
    let list = parse_wots_list(&args[2..], &ik.states[r as usize - 1], "p_inner")?;
    let points = inner::SEARCH.round_points(inner_path);
    Ok(list.into_iter().zip(points).map(|((msg, sig), i)| (i, state_from_msg(&msg), sig)).collect())
}

/// Parse the challenger's `q_inner_r` witness into its index.
pub fn parse_q_inner(tx: &Transaction, ck: &lngap_contract::ChallengerKeys, r: u32) -> Result<u32> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let pk = &ck.inner_indices[r as usize - 1];
    ensure!(args.len() == 2 + pk.n_bits(), "q_inner_{r}: witness has {} args", args.len());
    let reveal = Reveal::from_consumption_order(&args[2..])?;
    Ok(bits_to_uint(&pk.decode_bits(&reveal)?))
}

/// Labels of the inner-state keys a prover reveals in inner round `r`.
pub fn inner_round_labels(id: u32, keys_seq: u64, depth: u32, r: u32) -> Vec<String> {
    (0..inner::INNER_K - 1).map(|t| inner::inner_state_label(id, keys_seq, depth, r, t)).collect()
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
