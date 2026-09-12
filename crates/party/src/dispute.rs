//! Party behaviour for bisection disputes over a contract's claim.
//!
//! The challenger disputes a Move whose claimed end state disagrees with its
//! own computation; the prover answers rounds with committed register-file
//! states; the challenger narrows to one step; the step is then either
//! searched further (a compression: re-commitments, schedule words, inner
//! rounds, one-round leaf) or disproved directly (a simple step). Whoever
//! fails to respond within Δ loses by the timeout leaf.

use std::collections::HashMap;

use anyhow::{anyhow, ensure, Result};
use bitcoin::{OutPoint, Transaction, TxOut};
use lngap_btc::taptree::TapTree;
use lngap_btc::witness::witness_args_consumption_order;
use lngap_channel::{CommitCtx, Role};
use lngap_contract::claim::{state_from_msg, step_sources, ClaimData, ClaimKeys, ClaimSpec, Init, Search, StateSource, Step};
use lngap_contract::inner::{self, round_sources, round_witness, sched_inputs, sched_witness, InnerSource};
use lngap_contract::ChallengerKeys;
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
    /// Flat claims: the challenger may disprove the isolated compression; else the prover times out.
    Terminal,
    /// Inner chain: waiting for the prover's re-commitment of cur (+ block words) / next.
    ReCur,
    ReNext,
    /// Waiting for the prover's schedule words.
    WaitSched,
    /// `S_2` / `S_3`: waiting for the prover's inner round `r` states.
    WaitInnerP(u32),
    /// `I_r`: waiting for the challenger's inner index `r` (or, in round 1, a disproof).
    WaitInnerQ(u32),
    /// `T`: the challenger may disprove the isolated round; else the prover times out.
    RoundTerminal,
    /// Check chain: waiting for the prover's re-commitments.
    CheckReCur,
    CheckReNext,
    /// `C_1`: the challenger may disprove the isolated simple step; else the prover times out.
    CheckTerminal,
    Resolved,
}

#[derive(Clone, Debug)]
pub struct DisputeLive {
    pub depth: u32,
    pub prover: Role,
    pub spec: ClaimSpec,
    /// The honest prover data (as this party knows it).
    pub data: ClaimData,
    pub stage: Stage,
    /// Prover's level-1 commitments seen on-chain: step index → (state, signature).
    pub known: HashMap<u32, (Vec<u32>, WotsSig)>,
    pub path: Vec<u32>,
    pub outpoint: OutPoint,
    pub prevout: TxOut,
    pub tree: TapTree,
    pub confirmed_at: u32,
    /// All output trees along the chains (`claim::dispute_trees`).
    pub trees: Vec<TapTree>,
    /// This party's own computation of the chain (with a cheating prover's alterations).
    pub my_states: Vec<Vec<u32>>,
    pub responded: bool,
    // ----- after the last level-1 index -----
    pub re_cur: Option<(Vec<u32>, WotsSig)>,
    pub re_next: Option<(Vec<u32>, WotsSig)>,
    /// Committed block words: index → (word, signature).
    pub blocks: HashMap<usize, (u32, WotsSig)>,
    /// Prover's schedule words seen on-chain: index → (word, signature).
    pub sched: HashMap<u32, (u32, WotsSig)>,
    /// Prover's inner states seen on-chain: round index (1..64) → (state, signature).
    pub inner_known: HashMap<u32, ([u32; 8], WotsSig)>,
    pub inner_path: Vec<u32>,
    /// This party's own schedule and round states for the isolated
    /// compression (from the committed block words and init); set once the
    /// block words are known.
    pub my_sched: Option<[u32; 64]>,
    pub my_inner: Option<Vec<[u32; 8]>>,
}

impl DisputeLive {
    /// Which tree along the chains the current stage's output uses.
    pub fn tree_index(&self) -> usize {
        let l1 = lngap_contract::claim::level1_tree_count(&self.spec);
        let sched_off = if self.spec.has_schedule() { 1 } else { 0 };
        let inner_off = l1 + 2 + sched_off;
        let inner_rounds = self.spec.inner_search().rounds() as usize;
        match self.stage {
            Stage::WaitP(r) => 2 * (r as usize - 1),
            Stage::WaitQ(r) => 2 * r as usize - 1,
            Stage::Terminal => l1,
            Stage::ReCur => l1,
            Stage::ReNext => l1 + 1,
            Stage::WaitSched => l1 + 2,
            Stage::WaitInnerP(r) => inner_off + 2 * (r as usize - 1),
            Stage::WaitInnerQ(r) => inner_off + 2 * (r as usize - 1) + 1,
            Stage::RoundTerminal => inner_off + 2 * inner_rounds,
            Stage::CheckReCur => inner_off + 2 * inner_rounds + 1,
            Stage::CheckReNext => inner_off + 2 * inner_rounds + 2,
            Stage::CheckTerminal => inner_off + 2 * inner_rounds + 3,
            Stage::Resolved => self.trees.len() - 1,
        }
    }
    /// Who must act at the current stage (the other party can time them out).
    pub fn waiting_for(&self) -> Option<Role> {
        match self.stage {
            Stage::WaitP(_) | Stage::ReCur | Stage::ReNext | Stage::WaitSched | Stage::WaitInnerP(_) | Stage::CheckReCur | Stage::CheckReNext => Some(self.prover),
            Stage::WaitQ(_) | Stage::Terminal | Stage::WaitInnerQ(_) | Stage::RoundTerminal | Stage::CheckTerminal => Some(self.prover.other()),
            Stage::Resolved => None,
        }
    }
    /// The prover's committed state at step boundary `i` (the constant start at 0).
    pub fn state_at(&self, i: u32) -> Option<Vec<u32>> {
        if i == 0 {
            return Some(self.spec.start.clone());
        }
        self.known.get(&i).map(|k| k.0.clone())
    }
    /// The challenger's index for the next level-1 round: the first
    /// sub-segment whose end state the prover got wrong (a commitment that
    /// is missing, or that the honest steps do not reach from the
    /// sub-segment's start — loads take the prover's visible data), or the
    /// last sub-segment.
    pub fn choose_index(&self) -> u32 {
        let (lo, len) = self.spec.segment(&self.path);
        let k = self.spec.k;
        let sub = len / k;
        for t in 0..k - 1 {
            let a = lo + t * sub;
            let b = a + sub;
            let (Some(start), Some(end)) = (self.state_at(a), self.state_at(b)) else { return t };
            let ok = if sub == 1 {
                self.spec.step_ok(a as usize, &self.spec.steps[a as usize], &start, &end, self.spec.data_for(&self.data, a as usize))
            } else {
                let (reference, preds_ok) = self.spec.segment_reference(a as usize, b as usize, &start, &self.data);
                preds_ok && reference == end
            };
            if !ok {
                return t;
            }
        }
        k - 1
    }
    /// The isolated step after the level-1 rounds: `(cur source, next source, step index)`.
    pub fn isolated_step(&self) -> (StateSource, StateSource, u32) {
        step_sources(&self.spec, &self.path)
    }
    pub fn isolated(&self) -> &Step {
        &self.spec.steps[self.isolated_step().2 as usize]
    }
    /// The isolated compression's init kind.
    pub fn init_kind(&self) -> Init {
        match self.isolated() {
            Step::Compress { init, .. } => *init,
            _ => panic!("not a compression"),
        }
    }
    /// The value the path's source stands for, from this party's view of
    /// the prover's commitments (the constant start, or a level-1 commitment).
    pub fn source_value(&self, src: &StateSource) -> Option<Vec<u32>> {
        let (_, _, step) = self.isolated_step();
        match src {
            StateSource::Const(s) => Some(s.clone()),
            StateSource::End => self.known.get(&self.spec.n_steps()).map(|k| k.0.clone()),
            StateSource::Round(..) => {
                // the source is whichever commitment sits at the boundary
                let i = if *src == self.isolated_step().0 { step } else { step + 1 };
                self.known.get(&i).map(|k| k.0.clone())
            }
        }
    }
    pub fn source_sig(&self, src: &StateSource) -> Option<WotsSig> {
        let (_, _, step) = self.isolated_step();
        match src {
            StateSource::Const(_) => None,
            StateSource::End => self.known.get(&self.spec.n_steps()).map(|k| k.1.clone()),
            StateSource::Round(..) => {
                let i = if *src == self.isolated_step().0 { step } else { step + 1 };
                self.known.get(&i).map(|k| k.1.clone())
            }
        }
    }
    /// The committed init of the isolated compression (IV or `D` of re_cur).
    pub fn committed_init(&self) -> Option<[u32; 8]> {
        match self.init_kind() {
            Init::Iv => Some(lngap_contract::claim::IV),
            Init::D => self.re_cur.as_ref().map(|c| c.0[..8].try_into().unwrap()),
        }
    }
    /// The committed block (from the 16 block-word commitments).
    pub fn committed_block(&self) -> Option<[u8; 64]> {
        let mut b = [0u8; 64];
        for j in 0..16 {
            let w = self.blocks.get(&j)?.0;
            b[4 * j..4 * j + 4].copy_from_slice(&w.to_be_bytes());
        }
        Some(b)
    }
    /// Recompute the inner chain from the committed init and block words.
    pub fn compute_inner(&mut self, cheat: Option<&dyn Fn(u32, &[u32; 8]) -> [u32; 8]>) -> Result<()> {
        let init = self.committed_init().ok_or_else(|| anyhow!("no re-committed cur"))?;
        let block = self.committed_block().ok_or_else(|| anyhow!("no committed block"))?;
        let sched = inner::schedule(&block);
        self.my_sched = Some(sched);
        self.my_inner = Some(inner::round_states(&init, &sched, cheat));
        Ok(())
    }
    /// The prover's committed (or constant) value of an inner state, `0 ↔ init`, `64 ↔ D of re_next`.
    pub fn inner_state(&self, i: u32) -> Option<[u32; 8]> {
        match i {
            0 => self.committed_init(),
            64 => self.re_next.as_ref().map(|n| n.0[..8].try_into().unwrap()),
            _ => self.inner_known.get(&i).map(|k| k.0),
        }
    }
    /// The signature behind an inner state (None for a constant init).
    pub fn inner_sig(&self, i: u32) -> Result<Option<WotsSig>> {
        Ok(match i {
            0 => match self.init_kind() {
                Init::Iv => None,
                Init::D => Some(self.re_cur.as_ref().ok_or_else(|| anyhow!("no re_cur"))?.1.clone()),
            },
            64 => Some(self.re_next.as_ref().ok_or_else(|| anyhow!("no re_next"))?.1.clone()),
            _ => Some(self.inner_known.get(&i).ok_or_else(|| anyhow!("inner state {i} unknown"))?.1.clone()),
        })
    }
    /// The challenger's inner index: the first segment whose end state the
    /// prover got wrong, or the last segment.
    pub fn choose_inner_index(&self) -> u32 {
        let mine = self.my_inner.as_ref().expect("inner computation");
        let search = self.spec.inner_search();
        let points = search.round_points(&self.inner_path);
        for (t, i) in points.iter().enumerate() {
            match self.inner_state(*i) {
                Some(st) if st == mine[*i as usize] => continue,
                _ => return t as u32,
            }
        }
        search.k - 1
    }
    /// The first schedule word the prover got wrong, if any.
    pub fn first_bad_sched(&self) -> Option<u32> {
        let mine = self.my_sched.as_ref().expect("inner computation");
        let bw = self.spec.hash.block_words() as u32;
        (bw..self.spec.inner_rounds()).find(|i| self.sched.get(i).map(|s| s.0) != Some(mine[*i as usize]))
    }
    /// The first committed block word that differs from its constant or
    /// register source in re_cur, if any (data words are unconstrained).
    pub fn first_bad_block(&self) -> Option<usize> {
        let cur = &self.re_cur.as_ref()?.0;
        let Step::Compress { block, .. } = self.isolated() else { return None };
        let bw = self.spec.hash.block_words();
        let data: Vec<u32> = (0..bw).map(|j| self.blocks.get(&j).map(|b| b.0).unwrap_or(0)).collect();
        let (_, expected) = ClaimSpec::compress_inputs(self.isolated(), cur, &data, self.spec.hash);
        (0..bw).find(|j| !matches!(block[*j], lngap_contract::claim::Src::Data(_)) && self.blocks.get(j).map(|b| b.0) != Some(u32::from_be_bytes(expected[4 * j..4 * j + 4].try_into().unwrap())))
    }
    /// The isolated compression's committed block nibbles appended to re_cur's (the predicate space).
    pub fn pred_space(&self) -> Option<Vec<u8>> {
        let mut n = lngap_contract::claim::state_nibbles(&self.re_cur.as_ref()?.0);
        n.extend(lngap_contract::script_hash::nibbles(&self.committed_block()?));
        Some(n)
    }
    /// Does a predicate of the isolated compression fail on the committed values?
    pub fn cpred_violated(&self) -> bool {
        match self.pred_space() {
            Some(space) => self.isolated().preds().iter().any(|p| !p.holds(&space)),
            None => false,
        }
    }
    /// Does re_next differ from the committed block nibbles at a copy destination?
    pub fn ccopy_violated(&self) -> bool {
        let (Some(space), Some(next)) = (self.pred_space(), self.re_next.as_ref()) else { return false };
        let nn = lngap_contract::claim::state_nibbles(&next.0);
        self.isolated().copies().iter().any(|c| nn[c.dst..c.dst + c.n] != space[c.src..c.src + c.n])
    }
    /// Did the compression change a register other than `D` and its copy destinations?
    pub fn ckeep_violated(&self) -> bool {
        let (Some(c), Some(n)) = (&self.re_cur, &self.re_next) else { return false };
        let mask = self.isolated().copy_mask(self.spec.n_words);
        let cn = lngap_contract::claim::state_nibbles(&c.0);
        let nn = lngap_contract::claim::state_nibbles(&n.0);
        (self.spec.d_nibbles()..cn.len()).any(|i| !mask[i] && cn[i] != nn[i])
    }
    /// Witness args for the leaves verifying the 16 block words (15 first) then re_cur (or re_next).
    pub fn state_and_block_args(&self, which_next: bool) -> Result<Vec<Vec<u8>>> {
        let st = if which_next { &self.re_next } else { &self.re_cur };
        let mut v = Vec::new();
        for j in (0..16).rev() {
            v.extend(self.blocks.get(&j).ok_or_else(|| anyhow!("no block word {j}"))?.1.consumption_order());
        }
        v.extend(st.as_ref().ok_or_else(|| anyhow!("no re-commitment"))?.1.consumption_order());
        Ok(v)
    }
    /// Did the prover's re-commitments match the path's sources? Returns the offending leaf name.
    pub fn recommit_mismatch(&self, ctx: &CommitCtx, keys: &ClaimKeys) -> Option<(String, Vec<Vec<u8>>)> {
        let (cur_src, next_src, _) = self.isolated_step();
        for (which_next, src, re) in [(false, &cur_src, &self.re_cur), (true, &next_src, &self.re_next)] {
            let Some((val, sig)) = re else { continue };
            if self.source_value(src).as_ref() != Some(val) {
                let (name, _) = inner::mismatch_leaf(ctx, self.prover, keys, self.spec.n_words, which_next, src);
                let mut args = sig.consumption_order();
                if let Some(s) = self.source_sig(src) {
                    args.extend(s.consumption_order());
                }
                return Some((name, args));
            }
        }
        None
    }
    pub fn sched_word(&self, i: u32) -> Option<u32> {
        if i < 16 {
            self.blocks.get(&(i as usize)).map(|b| b.0)
        } else {
            self.sched.get(&i).map(|s| s.0)
        }
    }
    pub fn word_sig(&self, i: u32) -> Result<WotsSig> {
        Ok(if i < 16 {
            self.blocks.get(&(i as usize)).ok_or_else(|| anyhow!("no block word {i}"))?.1.clone()
        } else {
            self.sched.get(&i).ok_or_else(|| anyhow!("no schedule word {i}"))?.1.clone()
        })
    }
    /// Recompute the isolated round `r` natively from the prover's commitments:
    /// `(expected s_{r+1}, claimed s_{r+1})`.
    pub fn check_round(&self, r: u32) -> Result<([u32; 8], [u32; 8])> {
        let s_in = self.inner_state(r).ok_or_else(|| anyhow!("no inner state {r}"))?;
        let w = self.sched_word(r).ok_or_else(|| anyhow!("no schedule word {r}"))?;
        let mut expect = round_native(&s_in, w, K[r as usize]);
        if r == 63 {
            let init = self.committed_init().ok_or_else(|| anyhow!("no init"))?;
            for i in 0..8 {
                expect[i] = expect[i].wrapping_add(init[i]);
            }
        }
        let claimed = self.inner_state(r + 1).ok_or_else(|| anyhow!("no inner state {}", r + 1))?;
        Ok((expect, claimed))
    }
    /// Witness args (after Q's signature) and leaf name for disproving round `r`.
    pub fn round_disproof(&self, ctx: &CommitCtx, keys: &ClaimKeys, r: u32) -> Result<(String, Vec<Vec<u8>>)> {
        let init = self.init_kind();
        let (name, _) = inner::round_leaf(ctx, self.prover, keys, &self.spec, init, r);
        let search = self.spec.inner_search();
        // Compute the inner path for round r (most-significant digit first).
        let inner_path: Vec<u32> = {
            let rounds = search.rounds();
            let mut path = Vec::with_capacity(rounds as usize);
            let mut divisor = search.n / search.k;
            let mut idx = r;
            for _ in 0..rounds {
                path.push(idx / divisor);
                idx %= divisor;
                divisor /= search.k;
            }
            path
        };
        let (in_src, _, _) = round_sources(init, &inner_path, search);
        let w_sig = self.word_sig(r)?;
        let in_sig = match in_src {
            InnerSource::Init(Init::Iv) => None,
            _ => self.inner_sig(r)?,
        };
        let init_sig = if r == 63 { self.inner_sig(0)? } else { None };
        let out_sig = self.inner_sig(r + 1)?.expect("the output is always committed");
        Ok((name, round_witness(&w_sig, in_sig.as_ref(), init_sig.as_ref(), &out_sig)))
    }
    /// Witness args and leaf name for disproving schedule word `i`.
    pub fn sched_disproof(&self, ctx: &CommitCtx, keys: &ClaimKeys, i: u32) -> Result<(String, Vec<Vec<u8>>)> {
        let (name, _) = inner::sched_leaf(ctx, self.prover, keys, i);
        let inputs: Vec<WotsSig> = sched_inputs(i).iter().map(|j| self.word_sig(*j)).collect::<Result<_>>()?;
        let refs: Vec<&WotsSig> = inputs.iter().collect();
        Ok((name, sched_witness(&refs, &self.word_sig(i)?)))
    }
    /// Witness args and leaf name for disproving block word `j`.
    pub fn block_disproof(&self, ctx: &CommitCtx, keys: &ClaimKeys, j: usize) -> Result<(String, Vec<Vec<u8>>)> {
        let Step::Compress { block, .. } = self.isolated() else { unreachable!() };
        let (name, _) = inner::block_leaf(ctx, self.prover, keys, self.spec.n_words, j, block[j]);
        let mut args = self.blocks.get(&j).ok_or_else(|| anyhow!("no block word {j}"))?.1.consumption_order();
        if matches!(block[j], lngap_contract::claim::Src::Reg(_)) {
            args.extend(self.re_cur.as_ref().ok_or_else(|| anyhow!("no re_cur"))?.1.consumption_order());
        }
        Ok((name, args))
    }
    /// Witness args for the leaves that verify re_cur then re_next.
    pub fn re_pair_args(&self) -> Result<Vec<Vec<u8>>> {
        let mut v = self.re_cur.as_ref().ok_or_else(|| anyhow!("no re_cur"))?.1.consumption_order();
        v.extend(self.re_next.as_ref().ok_or_else(|| anyhow!("no re_next"))?.1.consumption_order());
        Ok(v)
    }
}

/// Split witness args into one signature per key and verify each; returns the messages.
pub fn parse_wots_list(args: &[Vec<u8>], pks: &[WotsPublic], what: &str) -> Result<Vec<(Vec<u8>, WotsSig)>> {
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

fn state8(msg: &[u8]) -> [u32; 8] {
    state_from_msg(msg)[..8].try_into().unwrap()
}

/// Parse the prover's `p_round_r` witness into `(index, state, sig)` triples.
pub fn parse_p_round(tx: &Transaction, keys: &ClaimKeys, spec: &ClaimSpec, path: &[u32], r: u32) -> Result<Vec<(u32, Vec<u32>, WotsSig)>> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let list = parse_wots_list(&args[2..], &keys.rounds[r as usize - 1], "p_round")?;
    let points = spec.round_points(path);
    Ok(list.into_iter().zip(points).map(|((msg, sig), i)| (i, state_from_msg(&msg), sig)).collect())
}

/// Parse an index reveal (`q_round_r`, `q_round_r_check`, `q_inner_r`).
pub fn parse_index(tx: &Transaction, pk: &lngap_lamport::PublicKey, what: &str) -> Result<u32> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    ensure!(args.len() == 2 + pk.n_bits(), "{what}: witness has {} args", args.len());
    let reveal = Reveal::from_consumption_order(&args[2..])?;
    Ok(bits_to_uint(&pk.decode_bits(&reveal)?))
}

pub fn parse_q_round(tx: &Transaction, ck: &ChallengerKeys, r: u32) -> Result<u32> {
    parse_index(tx, &ck.indices[r as usize - 1], "q_round")
}

pub fn parse_q_inner(tx: &Transaction, ck: &ChallengerKeys, r: u32) -> Result<u32> {
    parse_index(tx, &ck.inner_indices[r as usize - 1], "q_inner")
}

/// Parse `p_re_cur` / `c_re_cur`: the state, and (with blocks) the 16 block words.
pub fn parse_re_cur(tx: &Transaction, keys: &ClaimKeys, with_blocks: bool) -> Result<((Vec<u32>, WotsSig), Vec<(u32, WotsSig)>)> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let ik = keys.inner.as_ref().ok_or_else(|| anyhow!("no inner keys"))?;
    let mut pks = vec![ik.re_cur.clone()];
    if with_blocks {
        pks.extend(ik.block.iter().cloned());
    }
    let mut list = parse_wots_list(&args[2..], &pks, "re_cur")?;
    let (msg, sig) = list.remove(0);
    let blocks = list.into_iter().map(|(m, s)| (u32::from_be_bytes(m[..4].try_into().unwrap()), s)).collect();
    Ok(((state_from_msg(&msg), sig), blocks))
}

pub fn parse_re_next(tx: &Transaction, keys: &ClaimKeys) -> Result<(Vec<u32>, WotsSig)> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let ik = keys.inner.as_ref().ok_or_else(|| anyhow!("no inner keys"))?;
    let mut list = parse_wots_list(&args[2..], std::slice::from_ref(&ik.re_next), "re_next")?;
    let (msg, sig) = list.remove(0);
    Ok((state_from_msg(&msg), sig))
}

/// Parse the prover's `p_sched` witness into `(index, word, sig)` triples.
pub fn parse_p_sched(tx: &Transaction, keys: &ClaimKeys) -> Result<Vec<(u32, u32, WotsSig)>> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let ik = keys.inner.as_ref().ok_or_else(|| anyhow!("no inner keys"))?;
    let list = parse_wots_list(&args[2..], &ik.sched, "p_sched")?;
    Ok(list.into_iter().enumerate().map(|(k, (msg, sig))| (16 + k as u32, u32::from_be_bytes(msg[..4].try_into().unwrap()), sig)).collect())
}

/// Parse the prover's `p_inner_r` witness into `(round index, state, sig)` triples.
pub fn parse_p_inner(tx: &Transaction, keys: &ClaimKeys, inner_path: &[u32], r: u32, search: Search) -> Result<Vec<(u32, [u32; 8], WotsSig)>> {
    let args = witness_args_consumption_order(&tx.input[0].witness);
    let ik = keys.inner.as_ref().ok_or_else(|| anyhow!("no inner keys"))?;
    let list = parse_wots_list(&args[2..], &ik.states[r as usize - 1], "p_inner")?;
    let points = search.round_points(inner_path);
    Ok(list.into_iter().zip(points).map(|((msg, sig), i)| (i, state8(&msg), sig)).collect())
}

/// The flat terminal leaf's witness args (after Q's signature).
pub fn terminal_witness(d: &DisputeLive) -> Result<Vec<Vec<u8>>> {
    let (cur, _next, step) = d.isolated_step();
    let cur_sig = match &cur {
        StateSource::Const(_) => None,
        _ => Some(d.known.get(&step).ok_or_else(|| anyhow!("state {step} unknown"))?.1.clone()),
    };
    let next_sig = d.known.get(&(step + 1)).ok_or_else(|| anyhow!("state {} unknown", step + 1))?.1.clone();
    Ok(lngap_contract::flat::step_witness(&cur, &next_sig, cur_sig.as_ref()))
}
