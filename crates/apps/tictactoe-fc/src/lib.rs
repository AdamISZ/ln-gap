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
use lngap_contract::claim::{ClaimData, ClaimSpec};
use lngap_contract::prelude::*;
use lngap_contract::{Program, ProgramRegistry};
#[allow(unused_imports)]
use lngap_contract::Contract as _;
use lngap_contract::instance::DepthKeys;
use lngap_factchain::slot::{SlotClaim, SlotEntry, SlotSpec, E2_WORD, E_WORD, STATE_BITS};
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
        GraphShape::Star
    }
    /// A depth-`d` claim waits for slot `d + 1` to pass, binds my entry's
    /// word to the move and state reveals, and (from depth 2) the
    /// counterparty's entry's word to my re-commitment of its state.
    fn move_extras(&self, depth: u32, _prover: Role) -> MoveExtras {
        MoveExtras { cltv: Some(self.claim_from(depth)), expects: vec![], bind_end: Some(EndBind { word: E_WORD }), bind_prior: (depth >= 2).then_some(EndBind { word: E2_WORD }) }
    }
    /// Every depth carries the slot claim for moves `depth - 1` and `depth`
    /// (the contract's state is always the empty board, so depth counts
    /// from move 1). Without keys the commitments are zero: the shape only.
    fn claim(&self, _from: &[bool], depth: u32) -> Option<ClaimSpec> {
        Some(self.slot_claim(depth, |_| vec![[[0u8; 20]; 2]; STATE_BITS]).spec())
    }
    /// With the keys: each depth's state commitments come from that
    /// depth's `DepthKeys::state_n4`.
    fn claim_bound(&self, _from: &[bool], depth: u32, keys: &[DepthKeys]) -> Option<ClaimSpec> {
        let commits = |d: u32| {
            let k = &keys[d as usize - 1].state_n4;
            if k.len() == STATE_BITS { k.clone() } else { vec![[[0u8; 20]; 2]; STATE_BITS] }
        };
        Some(self.slot_claim(depth, commits).spec())
    }
    fn claim_data(&self, _from: &[bool], depth: u32) -> ClaimData {
        self.store.get(&Self::slot_key(self.params.game_id, depth)).unwrap_or_default()
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

    #[test]
    fn claim_specs_grow_with_depth() {
        let t = TicTacToeFc::new(TttFcParams { game_id: 1, checkpoint: [0; 20], btc_open: 100, grace: 1 }, ServedData::default());
        let init = t.initial_bits();
        for d in 1..=9 {
            let spec = Contract::claim(&t, &init, d).unwrap();
            assert_eq!(spec.n_words, slot::N_WORDS);
            assert_eq!(spec.steps.len(), (8 * d as usize + 66 * if d >= 2 { 2 } else { 1 }).next_power_of_two());
        }
        assert_eq!(t.claim_from(3), 105);
        assert_eq!(TicTacToeFc::mover_at(1), Role::User);
        assert_eq!(TicTacToeFc::mover_at(2), Role::Hub);
    }
}
