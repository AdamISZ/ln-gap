//! Tic-tac-toe played on the fact chain, settled in a channel: the venue
//! design (docs/planning/VENUE.md).
//!
//! The game itself never touches the channel: every move is a fact-chain
//! entry in its own slot (block `d` after the checkpoint carries move `d`),
//! signed by the mover's per-depth Lamport key. The channel contract is
//! opened once at the empty board and folded once with the result. Bitcoin
//! sees a game only when someone stalls or lies, and then at most:
//!
//! - a *claim* at depth `d` by the mover of move `d`: the counterparty's
//!   state at `d - 1` (its reveal, read off the venue), move `d`, the new
//!   state, the outcome code (`R(s_d)`: the result if terminal, else the
//!   party on turn forfeits — a *timeout claim*), and a [`SlotShape`]
//!   inclusion claim that move `d` sits in slot `d`; only after slot
//!   `d + 1` has passed (`CLTV`), so a timeout claim gives the counterparty
//!   its slot first;
//! - the *refutation*: the counterparty's move `d + 1` with its own
//!   inclusion claim for slot `d + 1`, after which nothing continues: a
//!   claimant whose timeout claim is refuted forfeits (`R(s_{d+1})`);
//! - the tic-tac-toe disprove leaves against either move, and the
//!   bisection against either inclusion claim.
//!
//! The program is [`lngap_tictactoe::TicTacToe`]'s rules with a star graph
//! ([`GraphShape::Star`]), slot claims, and the end-state bind that ties the
//! venue entry's `(move, state)` word to the Lamport reveals.

use anyhow::Result;
use lngap_contract::claim::{words_bytes, words_from_bytes, ClaimData, ClaimSpec};
use lngap_contract::prelude::*;
use lngap_contract::{Program, ProgramRegistry};
#[allow(unused_imports)]
use lngap_contract::Contract as _;
use lngap_contract::instance::DepthKeys;
use lngap_factchain::slot::{SlotClaim, SlotEntry, SlotSpec, E2_WORD, E_WORD, STATE_BITS};
use lngap_factchain::sig::{levels_for, Place, SigExhibit};
use lngap_factchain::stall::{self, StallClaim};
use lngap_n4bit::Digest;
use lngap_lamport::Reveal;
use lngap_names::ServedData;
use lngap_tictactoe::{Board, TicTacToe};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

pub use lngap_factchain::slot;
pub use lngap_tictactoe::{DRAW, OPEN, O_WON, X_WON};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TttFcParams {
    pub game_id: u16,
    /// The fact-chain digest the slots count from (slot `d` is `d` headers on).
    pub checkpoint: [u8; 20],
    /// The Bitcoin height at which the checkpoint was the tip: slot `d` is
    /// mined at Bitcoin height `btc_open + d` (the PoC mines one fact-chain
    /// block per Bitcoin block).
    pub btc_open: u32,
    /// Blocks after slot `d + 1` before a depth-`d` claim may be made.
    pub grace: u32,
    /// The depth-independent graph (VENUE.md §10c): one stall leaf per
    /// role, the stall claim of [`lngap_factchain::stall`], no CLTV.
    #[serde(default)]
    pub stall: bool,
    /// Header slots a stall claim covers (a claim at depth `d` needs
    /// `d + 1 < w_max`... precisely `d < w_max`).
    #[serde(default = "default_w_max")]
    pub w_max: usize,
}

fn default_w_max() -> usize {
    10
}

#[derive(Debug)]
pub struct TicTacToeFc {
    pub params: TttFcParams,
    name: String,
    store: ServedData,
    rules: TicTacToe,
}

impl TicTacToeFc {
    pub const PREFIX: &'static str = "ttt-fc";
    pub fn new(params: TttFcParams, store: ServedData) -> TicTacToeFc {
        let name = format!("{}:{}", Self::PREFIX, serde_json::to_string(&params).expect("serializable"));
        TicTacToeFc { params, name, store, rules: TicTacToe }
    }
    pub fn from_str(params: &str, store: ServedData) -> Result<TicTacToeFc> {
        Ok(TicTacToeFc::new(serde_json::from_str(params)?, store))
    }
    /// The served-data key for slot `depth` of this game.
    pub fn slot_key(game_id: u16, depth: u32) -> String {
        format!("g{game_id}/slot{depth}")
    }
    /// Who moves at depth `d` from the empty board: the user at odd depths.
    pub fn mover_at(depth: u32) -> Role {
        if depth % 2 == 1 {
            Role::User
        } else {
            Role::Hub
        }
    }
    /// The Bitcoin height from which a depth-`d` claim may be made.
    pub fn claim_from(&self, depth: u32) -> u32 {
        self.params.btc_open + depth + 1 + self.params.grace
    }
    /// The slot claim at `depth`: my slot `depth` and the counterparty's
    /// `depth - 1`, under the given commitments to each depth's state key
    /// (all zero when only the shape matters).
    pub fn slot_claim(&self, depth: u32, commits: impl Fn(u32) -> Vec<[Digest; 2]>) -> SlotClaim {
        let spec = |d: u32| SlotSpec { depth: d as u8, mover: Self::mover_at(d).idx() as u8, commits: commits(d) };
        SlotClaim {
            checkpoint: self.params.checkpoint,
            target: lngap_factchain::pow_target(),
            game_id: self.params.game_id,
            depth: depth as usize,
            prev: (depth >= 2).then(|| spec(depth - 1)),
            own: spec(depth),
        }
    }
    /// The served-data key for `role`'s stall claim.
    pub fn stall_key(game_id: u16, role: Role) -> String {
        format!("g{game_id}/stall/{}", role.name())
    }
    /// `role`'s stall claim (stall graphs): the same program at every depth.
    pub fn stall_claim_for(&self, role: Role) -> StallClaim {
        StallClaim {
            layout: lngap_factchain::stall::Layout::tictactoe(),
            checkpoint: self.params.checkpoint,
            target: lngap_factchain::pow_target(),
            game_id: self.params.game_id,
            me: role.idx() as u8,
            w_max: self.params.w_max,
            initial_e2: SlotEntry::word1(0, bits_to_uint(&self.rules.state_bits(&self.rules.initial()))).to_be_bytes().to_vec(),
            k: 4,
            check_next: true,
        }
    }
    /// The served-data key for `role`'s lie exhibit.
    pub fn lie_key(game_id: u16, role: Role) -> String {
        format!("g{game_id}/lie/{}", role.name())
    }
    pub fn sig_key(game_id: u16, role: Role) -> String {
        format!("g{game_id}/sig/{}", role.name())
    }
    /// The store key of `role`'s per-depth venue commitment tree roots.
    pub fn roots_key(game_id: u16, role: Role) -> String {
        format!("g{game_id}/roots/{}", role.name())
    }
    /// Serve `role`'s commitment tree roots (index `d`; `None` where `role`
    /// does not move), which the counterparty's signature exhibit pins.
    pub fn put_roots(store: &ServedData, game_id: u16, role: Role, roots: &[Option<Digest>]) {
        store.put(&Self::roots_key(game_id, role), roots.iter().map(|r| words_from_bytes(&r.unwrap_or([0u8; 20]))).collect());
    }
    fn roots_of(&self, role: Role) -> Option<Vec<Option<Digest>>> {
        let data = self.store.get(&Self::roots_key(self.params.game_id, role))?;
        Some(data.iter().map(|w| { let b = words_bytes(w); (b.iter().any(|x| *x != 0)).then(|| b.as_slice().try_into().unwrap()) }).collect())
    }
    /// Where signed state bit `i` sits in the entry's head: bit `i % 8` of
    /// byte `7 - i / 8` (the `(move, state)` word, big-endian).
    pub fn places() -> Vec<Place> {
        (0..STATE_BITS).map(|i| Place { byte: 7 - i / 8, bit: (i % 8) as u8 }).collect()
    }
    /// `role`'s signature exhibit against the counterparty's entries (stall
    /// graphs), once the counterparty's commitment roots are served.
    pub fn sig_claim_for(&self, role: Role) -> Option<SigExhibit> {
        let roots = self.roots_of(role.other())?;
        Some(SigExhibit {
            checkpoint: self.params.checkpoint,
            target: lngap_factchain::pow_target(),
            game_id: self.params.game_id,
            me: role.idx() as u8,
            w_max: self.params.w_max,
            k: 2,
            n_chunks: STATE_BITS,
            chunk_offset: 0,
            places: Self::places(),
            roots,
            levels: levels_for(2 * STATE_BITS),
        })
    }
    /// `role`'s lie exhibit: the stall claim without the next-slot check,
    /// slot `d` the counterparty's move.
    pub fn lie_claim_for(&self, role: Role) -> StallClaim {
        StallClaim { check_next: false, ..self.stall_claim_for(role) }
    }
    /// The venue entry for move `depth` leaving the board at `new`, signed
    /// with the mover's reveal of the new state.
    pub fn entry(&self, depth: u32, mv: u8, new: &Board, state_reveal: &Reveal) -> SlotEntry {
        assert_eq!(state_reveal.preimages.len(), STATE_BITS);
        SlotEntry {
            game_id: self.params.game_id,
            depth: depth as u8,
            mover: Self::mover_at(depth).idx() as u8,
            mv,
            state: bits_to_uint(&self.rules.state_bits(new)),
            sigs: state_reveal.preimages.clone(),
        }
    }
}

impl Contract for TicTacToeFc {
    type State = Board;
    type Move = u8;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        Contract::outcomes(&self.rules)
    }
    fn initial(&self) -> Board {
        self.rules.initial()
    }
    fn turn(&self, s: &Board) -> Option<Role> {
        self.rules.turn(s)
    }
    fn transition(&self, s: &Board, m: &u8, mover: Role) -> Result<Board, Invalid> {
        self.rules.transition(s, m, mover)
    }
    fn resolution(&self, s: &Board) -> Outcome {
        self.rules.resolution(s)
    }
    fn max_depth_from(&self, s: &Board) -> u32 {
        self.rules.max_depth_from(s)
    }
    fn n_state_bits(&self) -> usize {
        Contract::n_state_bits(&self.rules)
    }
    fn n_move_bits(&self) -> usize {
        Contract::n_move_bits(&self.rules)
    }
    fn state_bits(&self, s: &Board) -> Vec<bool> {
        self.rules.state_bits(s)
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<Board> {
        self.rules.state_from_bits(b)
    }
    fn move_bits(&self, m: &u8) -> Vec<bool> {
        self.rules.move_bits(m)
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<u8> {
        self.rules.move_from_bits(b)
    }
    fn describe_state(&self, s: &Board) -> String {
        self.rules.describe_state(s)
    }
    fn describe_move(&self, m: &u8) -> String {
        self.rules.describe_move(m)
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        Contract::disprove_leaves(&self.rules, ctx)
    }
    fn graph_shape(&self) -> GraphShape {
        if self.params.stall { GraphShape::Stall } else { GraphShape::Star }
    }
    /// Star: a depth-`d` claim waits for slot `d + 1` to pass, binds my
    /// entry's word to the move and state reveals, and (from depth 2) the
    /// counterparty's entry's word to my re-commitment of its state.
    /// Stall: no CLTV (the claim proves the next slot's block exists), the
    /// same two binds at fixed registers, and the depth bound as well.
    fn move_extras(&self, depth: u32, _prover: Role) -> MoveExtras {
        if self.params.stall {
            let l = stall::Layout::tictactoe();
            return MoveExtras {
                cltv: None,
                expects: vec![],
                bind_end: Some(EndBind { word: l.e_off / 8 }),
                bind_prior: Some(EndBind { word: l.e2_off / 8 }),
                bind_depth: Some(DepthBind { word: l.dep_word_index(), nibbles: stall::DEP_NIBBLES }),
                wots_only: false,
            };
        }
        MoveExtras { cltv: Some(self.claim_from(depth)), expects: vec![], bind_end: Some(EndBind { word: E_WORD }), bind_prior: (depth >= 2).then_some(EndBind { word: E2_WORD }), bind_depth: None, wots_only: false }
    }
    /// Star: every depth carries the slot claim for moves `depth - 1` and
    /// `depth` (the contract's state is always the empty board, so depth
    /// counts from move 1). Without keys the commitments are zero: the
    /// shape only. Stall graphs have no per-depth claim.
    fn claim(&self, _from: &[bool], depth: u32) -> Option<ClaimSpec> {
        if self.params.stall {
            return None;
        }
        Some(self.slot_claim(depth, |_| vec![[[0u8; 20]; 2]; STATE_BITS]).spec())
    }
    /// With the keys: each depth's state commitments come from that
    /// depth's `DepthKeys::state_n4`.
    fn claim_bound(&self, _from: &[bool], depth: u32, keys: &[DepthKeys]) -> Option<ClaimSpec> {
        if self.params.stall {
            return None;
        }
        let commits = |d: u32| {
            let k = &keys[d as usize - 1].state_n4;
            if k.len() == STATE_BITS { k.clone() } else { vec![[[0u8; 20]; 2]; STATE_BITS] }
        };
        Some(self.slot_claim(depth, commits).spec())
    }
    fn claim_data(&self, _from: &[bool], depth: u32) -> ClaimData {
        self.store.get(&Self::slot_key(self.params.game_id, depth)).unwrap_or_default()
    }
    fn stall_claim(&self, role: Role) -> Option<ClaimSpec> {
        self.params.stall.then(|| self.stall_claim_for(role).spec())
    }
    fn stall_claim_data(&self, role: Role) -> ClaimData {
        self.store.get(&Self::stall_key(self.params.game_id, role)).unwrap_or_default()
    }
    fn lie_claim(&self, role: Role) -> Option<ClaimSpec> {
        self.params.stall.then(|| self.lie_claim_for(role).spec())
    }
    fn lie_claim_data(&self, role: Role) -> ClaimData {
        self.store.get(&Self::lie_key(self.params.game_id, role)).unwrap_or_default()
    }
    fn sig_claim(&self, role: Role) -> Option<ClaimSpec> {
        if !self.params.stall {
            return None;
        }
        Some(self.sig_claim_for(role)?.spec())
    }
    fn sig_claim_data(&self, role: Role) -> ClaimData {
        self.store.get(&Self::sig_key(self.params.game_id, role)).unwrap_or_default()
    }
}

/// A registry knowing `ttt-fc:{params}`.
pub fn registry(store: ServedData) -> ProgramRegistry {
    let mut r = ProgramRegistry::new();
    r.register_factory(TicTacToeFc::PREFIX, move |p| Ok(Arc::new(TicTacToeFc::from_str(p, store.clone())?) as Arc<dyn Program>));
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    fn params(stall: bool) -> TttFcParams {
        TttFcParams { game_id: 1, checkpoint: [0; 20], btc_open: 100, grace: 1, stall, w_max: 10 }
    }

    #[test]
    fn claim_specs_grow_with_depth() {
        let t = TicTacToeFc::new(params(false), ServedData::default());
        let init = t.initial_bits();
        for d in 1..=9 {
            let spec = Contract::claim(&t, &init, d).unwrap();
            assert_eq!(spec.n_words, slot::N_WORDS);
            assert_eq!(spec.steps.len(), (14 * d as usize + 66 * if d >= 2 { 2 } else { 1 }).next_power_of_two());
        }
        assert_eq!(t.claim_from(3), 105);
        assert_eq!(TicTacToeFc::mover_at(1), Role::User);
        assert_eq!(TicTacToeFc::mover_at(2), Role::Hub);
    }

    #[test]
    fn stall_claim_is_one_spec_per_role() {
        let t = TicTacToeFc::new(params(true), ServedData::default());
        let init = t.initial_bits();
        assert!(Contract::claim(&t, &init, 1).is_none());
        for r in Role::BOTH {
            let spec = Contract::stall_claim(&t, r).unwrap();
            assert_eq!(spec.n_words, stall::Layout::tictactoe().n_words);
            assert_eq!(spec.steps.len(), 256);
            assert_eq!(spec.rounds(), 4);
        }
        assert_eq!(Program::graph_shape(&t), GraphShape::Stall);
    }
}

/// The stall graph's size: two stall leaves off `C`, per role the splits
/// and one dispute chain, whatever the game's length.
#[cfg(test)]
mod stall_sizes {
    use super::*;
    use bitcoin::Amount;
    use lngap_btc::keys::Seed;
    use lngap_channel::{ChannelParams, CommitCtx, ContractOutput, PartyKeys};
    use lngap_contract::claim::{ChallengerKeys, ClaimKeys, ClaimSpec};
    use lngap_contract::inner::InnerKeys;
    use lngap_contract::{ContractInstance, Program, CODE_BITS, DEPTH_BITS};
    use lngap_lamport::keystore::KeyStore;

    fn role_keys(ks: &mut KeyStore, role: Role, spec: &ClaimSpec, prog: &dyn Program) -> DepthKeys {
        let tag = format!("{}/{}", role.name(), spec.steps.len() + spec.steps.iter().filter(|s| !s.preds().is_empty()).count());
        let l = |f: &str| format!("{tag}/{f}");
        let nb = spec.wots_bytes();
        DepthKeys {
            prover: role,
            mv: ks.generate(&l("move"), prog.n_move_bits()).unwrap(),
            state: ks.generate(&l("state"), prog.n_state_bits()).unwrap(),
            code: ks.generate(&l("code"), CODE_BITS).unwrap(),
            claim: Some(ClaimKeys {
                end: ks.generate_wots(&l("end"), nb).unwrap(),
                rounds: (1..=spec.rounds()).map(|r| (0..spec.k - 1).map(|t| ks.generate_wots(&l(&format!("r{r}t{t}")), nb).unwrap()).collect()).collect(),
                inner: Some(InnerKeys {
                    re_cur: ks.generate_wots(&l("re_cur"), nb).unwrap(),
                    re_next: ks.generate_wots(&l("re_next"), nb).unwrap(),
                    block: (0..spec.hash.block_words()).map(|j| ks.generate_wots(&l(&format!("block{j}")), 4).unwrap()).collect(),
                    sched: vec![],
                    states: vec![],
                }),
            }),
            prior: Some(ks.generate(&l("prior"), prog.n_state_bits()).unwrap()),
            state_n4: vec![],
            depth: Some(ks.generate(&l("depth"), DEPTH_BITS).unwrap()),
        }
    }

    #[test]
    fn print_stall_graph_sizes() {
        // a checkpoint whose halves differ, as a real digest's do (the first
        // header's link checks would otherwise be identical scripts)
        let checkpoint: [u8; 20] = std::array::from_fn(|i| (i * 13 + 7) as u8);
        let store = ServedData::default();
        // the signature exhibits pin the other role's commitment tree roots
        for r in Role::BOTH {
            let roots: Vec<Option<Digest>> = (0..10).map(|d| (d >= 1 && TicTacToeFc::mover_at(d as u32) == r).then(|| [(d * 17 + r.idx() * 5) as u8; 20])).collect();
            TicTacToeFc::put_roots(&store, 1, r, &roots);
        }
        let prog: Arc<dyn Program> = Arc::new(TicTacToeFc::new(TttFcParams { game_id: 1, checkpoint, btc_open: 100, grace: 1, stall: true, w_max: 10 }, store));
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
        let pubs = [user.public(), hub.public()];
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
        let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
        let spec = prog.stall_claim(Role::User).unwrap();
        let mut ks = KeyStore::new(Seed::from_label("stall-keys"));
        let mut cks = KeyStore::new(Seed::from_label("challenger-keys"));
        let mut keys: Vec<DepthKeys> = Vec::new();
        let mut challenger: Vec<ChallengerKeys> = Vec::new();
        for (i, kind) in ["stall", "stall", "lie", "lie", "sig", "sig"].iter().enumerate() {
            let r = Role::BOTH[i % 2];
            let sp = lngap_contract::instance::stall_spec_at(&*prog, i).unwrap();
            let mut k = role_keys(&mut ks, r, &sp, &*prog);
            // distinct labels per kind
            let l = |f: &str| format!("{kind}/{}/{f}", r.name());
            k.mv = ks.generate(&l("move"), prog.n_move_bits()).unwrap();
            k.state = ks.generate(&l("state"), prog.n_state_bits()).unwrap();
            k.code = ks.generate(&l("code"), CODE_BITS).unwrap();
            k.prior = Some(ks.generate(&l("prior"), prog.n_state_bits()).unwrap());
            k.depth = Some(ks.generate(&l("depth"), DEPTH_BITS).unwrap());
            keys.push(k);
            challenger.push(ChallengerKeys { indices: (1..=sp.rounds()).map(|j| cks.generate(&format!("{kind}/{}/idx{j}", r.name()), sp.index_bits()).unwrap()).collect(), inner_indices: vec![] });
        }
        let inst = ContractInstance::new(1, prog.clone(), Amount::from_sat(200_000), prog.initial_bits(), 300, 1, keys, challenger).unwrap();
        let t0 = inst.tree(&ctx).unwrap();
        for (n, s, cb) in t0.sizes() {
            println!("SIZE C: {n}: script {s} B, control block {cb} B");
        }
        for d in 1..=6u32 {
            let t = inst.stall_graph_tree(&ctx, d).unwrap();
            let total: usize = t.leaves().iter().map(|l| l.script.len()).sum();
            println!("SIZE {}: {} leaves, {total} B of script total", ContractInstance::stall_graph_leaf_name(d), t.leaves().len());
        }
        let graph = inst.graph(&ctx, bitcoin::OutPoint::null(), &bitcoin::TxOut { value: inst.value, script_pubkey: t0.script_pubkey() }).unwrap();
        println!("SIZE stall graph: {} pre-signed transactions (W_max = 10, k = 4, {} claim steps, {} rounds; six claim sets, D31)", graph.len(), spec.steps.len(), spec.rounds());
        let mut by_kind: std::collections::BTreeMap<String, usize> = Default::default();
        for p in &graph {
            let k = p.label.split('/').next_back().unwrap().trim_end_matches(char::is_numeric).to_string();
            *by_kind.entry(k).or_default() += 1;
        }
        println!("SIZE stall graph by label: {by_kind:?}");
        assert!(graph.len() < 130, "{} transactions", graph.len());
    }
}
