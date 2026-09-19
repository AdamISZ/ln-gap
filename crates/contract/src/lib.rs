//! The contract framework: programs, contract outputs on commitments, the
//! pre-signed graph (Settle / Move / Split), disprove leaves, and parsing of
//! on-chain moves.
//!
//! A contract output `C` holds `V` sats under `(program, state, turn, deadline)`.
//! Off-chain both parties run the program natively; on-chain, the party on
//! turn commits its move with Lamport preimages and the counterparty may
//! disprove any inconsistency in one transaction.

pub mod claim;
pub mod flat;
pub mod inner;
pub mod instance;
pub mod simple;
pub mod leaves;
pub mod onchain;
pub mod testing;
pub mod toy;

use std::fmt::Debug;

use anyhow::{bail, Result};
use bitcoin::Amount;
use lngap_channel::Role;
use serde::{Deserialize, Serialize};

pub use claim::{ChallengerKeys, ClaimData, ClaimKeys, ClaimSpec, HashKind};
pub use instance::{ContractInstance, DepthKeys, InstanceSpec};
pub use leaves::{Claim, DisproveSpec, LeafBuilder, LeafCtx, PriorState};
pub use registry::ProgramRegistry;
pub mod registry;
pub mod script_hash;

/// A statement someone else committed to with a Lamport key: the leaf checks
/// `expect_uint(pk, value)`, and whoever spends supplies the preimages,
/// which they hold because the key's owner handed them over (a statement, an
/// attestation) or revealed them on-chain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Extra {
    /// Where the spender looks the preimages up (e.g. `attest/<name>/<key>`).
    pub label: String,
    pub pk: lngap_lamport::PublicKey,
    pub value: u32,
}

/// A Move's claim registers bound to its Lamport-revealed fields: end-state
/// word `word` must equal `move << 24 | state` (the move in the top byte,
/// the state in the low 24 bits). This is what ties a venue entry's content
/// to the move the leaf's disproofs judge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndBind {
    pub word: usize,
}

/// A Move's depth reveal bound to a claim register: the low `nibbles`
/// nibbles of end-state word `word`, read as a number, must equal the
/// revealed depth (the depth-independent stall leaf, VENUE.md §10c).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepthBind {
    pub word: usize,
    pub nibbles: usize,
}

/// Bits of the depth field a stall leaf reveals.
pub const DEPTH_BITS: usize = 8;

/// What a Move leaf requires beyond the prover's own commitments.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MoveExtras {
    /// The move is only valid at or after this height (`OP_CLTV`).
    pub cltv: Option<u32>,
    pub expects: Vec<Extra>,
    /// Bind the claim's end state to the move and state reveals.
    pub bind_end: Option<EndBind>,
    /// Bind the state nibbles of an end-state word to the prior reveal.
    pub bind_prior: Option<EndBind>,
    /// Bind an end-state word to the depth reveal (stall graphs).
    pub bind_depth: Option<DepthBind>,
    /// The leaf reveals only the outcome code and the claim's end state:
    /// the prior, the move and the state live in the end state's registers
    /// and the disprove leaves read them from there (chess).
    pub wots_only: bool,
}

/// The shape of a contract's pre-signed graph.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum GraphShape {
    /// `C → move_1 → C'_1 → move_2 → …`: the game is played on-chain move
    /// by move once escalated.
    #[default]
    Chain,
    /// `C → move_d → C'_d` for every depth `d` (a claim from the doubly
    /// signed initial state, revealing the counterparty's prior state), and
    /// off each `C'_d` one `move_{d+1}` (the refutation) after which no
    /// further move exists. Moves are played elsewhere (a venue); Bitcoin
    /// sees one claim and at most one answer.
    Star,
    /// `C → stall_r → S_r` and `C → lie_r → L_r` for each role `r`: a
    /// stall proof and a lie exhibit per role with fixed keys, the depth a
    /// revealed field bound to a depth-independent claim
    /// ([`Contract::stall_claim`], [`Contract::lie_claim`]). Off a stall
    /// output: the splits, the dispute chain, and the disprove leaves
    /// against the claimant's move (the counterparty spends them). Off a
    /// lie output: the dispute chain (the liar), the disprove leaves
    /// against the exhibited move (the victim, after one window), and the
    /// splits (the liar, after a longer one). The keys vector holds four
    /// entries: `[stall_U, stall_H, lie_U, lie_H]` (`Role::BOTH` order).
    Stall,
}

/// How `V` is divided for an outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Payout {
    UserAll,
    HubAll,
    Even,
}

impl Payout {
    /// `(user, hub)` shares of `v`.
    pub fn dist(&self, v: Amount) -> [Amount; 2] {
        match self {
            Payout::UserAll => [v, Amount::ZERO],
            Payout::HubAll => [Amount::ZERO, v],
            Payout::Even => {
                let half = v / 2;
                [half, v - half]
            }
        }
    }
    /// Does this payout give `r` strictly more than the other side?
    pub fn favours(&self, r: Role) -> bool {
        matches!((self, r), (Payout::UserAll, Role::User) | (Payout::HubAll, Role::Hub))
    }
}

/// One of a program's (≤ 4) outcomes. `code` is its 2-bit on-chain code.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Outcome {
    pub code: u8,
    pub name: String,
    pub payout: Payout,
}

impl Outcome {
    pub fn new(code: u8, name: &str, payout: Payout) -> Outcome {
        assert!(code < 4);
        Outcome { code, name: name.to_string(), payout }
    }
}

/// Number of bits of the outcome code.
pub const CODE_BITS: usize = 2;

#[derive(Debug, thiserror::Error)]
#[error("invalid move: {0}")]
pub struct Invalid(pub String);

/// The typed contract interface (plan §7.1).
pub trait Contract: Send + Sync + Debug + 'static {
    type State: Clone + Debug + PartialEq + Send + Sync;
    type Move: Clone + Debug + Send + Sync;

    fn name(&self) -> &str;
    fn outcomes(&self) -> Vec<Outcome>;
    fn initial(&self) -> Self::State;
    fn transition(&self, s: &Self::State, m: &Self::Move, mover: Role) -> Result<Self::State, Invalid>;
    /// `R(s)`, including the forfeit rule for non-terminal states.
    fn resolution(&self, s: &Self::State) -> Outcome;
    /// Who moves next; `None` if terminal.
    fn turn(&self, s: &Self::State) -> Option<Role>;
    /// Bound on the number of further on-chain moves from `s` (`M`).
    fn max_depth_from(&self, s: &Self::State) -> u32;

    fn n_state_bits(&self) -> usize;
    fn n_move_bits(&self) -> usize;
    fn state_bits(&self, s: &Self::State) -> Vec<bool>;
    fn state_from_bits(&self, bits: &[bool]) -> Result<Self::State>;
    fn move_bits(&self, m: &Self::Move) -> Vec<bool>;
    fn move_from_bits(&self, bits: &[bool]) -> Result<Self::Move>;

    /// The disprove leaves for a Move at one depth. See [`LeafBuilder`].
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec>;

    /// Extra requirements on the Move leaf at `depth` (fixed at signing, so
    /// they may depend on the contract's parameters and the depth only).
    fn move_extras(&self, depth: u32, prover: Role) -> MoveExtras {
        let _ = (depth, prover);
        MoveExtras::default()
    }

    /// A bisection-verified claim committed by the `depth`-th Move counted
    /// from state `from` (depth 1 = the next move from `from`). Claims are
    /// state-relative because an off-chain accepted move re-instantiates the
    /// contract at its new state, where the next move is depth 1 again.
    fn claim(&self, from: &[bool], depth: u32) -> Option<claim::ClaimSpec> {
        let _ = (from, depth);
        None
    }
    /// The served prover data for that claim.
    fn claim_data(&self, from: &[bool], depth: u32) -> claim::ClaimData {
        let _ = (from, depth);
        vec![]
    }
    /// The pre-signed graph's shape (see [`GraphShape`]).
    fn graph_shape(&self) -> GraphShape {
        GraphShape::Chain
    }
    /// The claim with the instance's keys bound in (commitments a claim
    /// checks published data against). Same shape as [`Contract::claim`].
    fn claim_bound(&self, from: &[bool], depth: u32, keys: &[instance::DepthKeys]) -> Option<claim::ClaimSpec> {
        let _ = keys;
        self.claim(from, depth)
    }
    /// Stall graphs: `role`'s depth-independent stall claim.
    fn stall_claim(&self, role: Role) -> Option<claim::ClaimSpec> {
        let _ = role;
        None
    }
    /// The served prover data for that claim.
    fn stall_claim_data(&self, role: Role) -> claim::ClaimData {
        let _ = role;
        vec![]
    }
    /// Stall graphs: `role`'s lie exhibit, a claim proving the
    /// counterparty's move at slot `d` and `role`'s own at `d - 1`.
    fn lie_claim(&self, role: Role) -> Option<claim::ClaimSpec> {
        let _ = role;
        None
    }
    fn lie_claim_data(&self, role: Role) -> claim::ClaimData {
        let _ = role;
        vec![]
    }
    /// Stall graphs: `role`'s signature exhibit, a claim proving that the
    /// counterparty's entry at slot `d` publishes, for one signed bit, a
    /// preimage that does not open its commitment (D31).
    fn sig_claim(&self, role: Role) -> Option<claim::ClaimSpec> {
        let _ = role;
        None
    }
    fn sig_claim_data(&self, role: Role) -> claim::ClaimData {
        let _ = role;
        vec![]
    }
    /// `wots_only` programs: the `(prior, move, state)` bits a claim's end
    /// state registers hold.
    fn state_from_end(&self, end: &[u32]) -> Option<(Vec<bool>, Vec<bool>, Vec<bool>)> {
        let _ = end;
        None
    }

    fn describe_state(&self, s: &Self::State) -> String {
        format!("{s:?}")
    }
    fn describe_move(&self, m: &Self::Move) -> String {
        format!("{m:?}")
    }
}

/// The bit-level, object-safe view of a contract used by the framework.
pub trait Program: Send + Sync + Debug {
    fn name(&self) -> &str;
    fn outcomes(&self) -> Vec<Outcome>;
    fn n_state_bits(&self) -> usize;
    fn n_move_bits(&self) -> usize;
    fn initial_bits(&self) -> Vec<bool>;
    fn transition_bits(&self, s: &[bool], m: &[bool], mover: Role) -> Result<Vec<bool>>;
    fn resolution_bits(&self, s: &[bool]) -> Result<Outcome>;
    fn turn_bits(&self, s: &[bool]) -> Result<Option<Role>>;
    fn max_depth_from_bits(&self, s: &[bool]) -> Result<u32>;
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec>;
    fn move_extras(&self, depth: u32, prover: Role) -> MoveExtras;
    fn claim(&self, from: &[bool], depth: u32) -> Option<claim::ClaimSpec>;
    fn claim_data(&self, from: &[bool], depth: u32) -> claim::ClaimData;
    fn graph_shape(&self) -> GraphShape;
    fn claim_bound(&self, from: &[bool], depth: u32, keys: &[instance::DepthKeys]) -> Option<claim::ClaimSpec>;
    fn stall_claim(&self, role: Role) -> Option<claim::ClaimSpec>;
    fn stall_claim_data(&self, role: Role) -> claim::ClaimData;
    fn lie_claim(&self, role: Role) -> Option<claim::ClaimSpec>;
    fn lie_claim_data(&self, role: Role) -> claim::ClaimData;
    fn sig_claim(&self, role: Role) -> Option<claim::ClaimSpec>;
    fn sig_claim_data(&self, role: Role) -> claim::ClaimData;
    fn state_from_end(&self, end: &[u32]) -> Option<(Vec<bool>, Vec<bool>, Vec<bool>)>;
    fn describe_state_bits(&self, s: &[bool]) -> String;
    fn describe_move_bits(&self, m: &[bool]) -> String;

    fn outcome_by_code(&self, code: u8) -> Result<Outcome> {
        match self.outcomes().into_iter().find(|o| o.code == code) {
            Some(o) => Ok(o),
            None => bail!("{}: no outcome with code {code}", self.name()),
        }
    }
}

impl<C: Contract> Program for C {
    fn name(&self) -> &str {
        Contract::name(self)
    }
    fn outcomes(&self) -> Vec<Outcome> {
        Contract::outcomes(self)
    }
    fn n_state_bits(&self) -> usize {
        Contract::n_state_bits(self)
    }
    fn n_move_bits(&self) -> usize {
        Contract::n_move_bits(self)
    }
    fn initial_bits(&self) -> Vec<bool> {
        self.state_bits(&self.initial())
    }
    fn transition_bits(&self, s: &[bool], m: &[bool], mover: Role) -> Result<Vec<bool>> {
        let s = self.state_from_bits(s)?;
        let m = self.move_from_bits(m)?;
        let s2 = self.transition(&s, &m, mover)?;
        Ok(self.state_bits(&s2))
    }
    fn resolution_bits(&self, s: &[bool]) -> Result<Outcome> {
        Ok(self.resolution(&self.state_from_bits(s)?))
    }
    fn turn_bits(&self, s: &[bool]) -> Result<Option<Role>> {
        Ok(self.turn(&self.state_from_bits(s)?))
    }
    fn max_depth_from_bits(&self, s: &[bool]) -> Result<u32> {
        Ok(self.max_depth_from(&self.state_from_bits(s)?))
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        Contract::disprove_leaves(self, ctx)
    }
    fn move_extras(&self, depth: u32, prover: Role) -> MoveExtras {
        Contract::move_extras(self, depth, prover)
    }
    fn claim(&self, from: &[bool], depth: u32) -> Option<claim::ClaimSpec> {
        Contract::claim(self, from, depth)
    }
    fn claim_data(&self, from: &[bool], depth: u32) -> claim::ClaimData {
        Contract::claim_data(self, from, depth)
    }
    fn graph_shape(&self) -> GraphShape {
        Contract::graph_shape(self)
    }
    fn claim_bound(&self, from: &[bool], depth: u32, keys: &[instance::DepthKeys]) -> Option<claim::ClaimSpec> {
        Contract::claim_bound(self, from, depth, keys)
    }
    fn stall_claim(&self, role: Role) -> Option<claim::ClaimSpec> {
        Contract::stall_claim(self, role)
    }
    fn stall_claim_data(&self, role: Role) -> claim::ClaimData {
        Contract::stall_claim_data(self, role)
    }
    fn lie_claim(&self, role: Role) -> Option<claim::ClaimSpec> {
        Contract::lie_claim(self, role)
    }
    fn lie_claim_data(&self, role: Role) -> claim::ClaimData {
        Contract::lie_claim_data(self, role)
    }
    fn sig_claim(&self, role: Role) -> Option<claim::ClaimSpec> {
        Contract::sig_claim(self, role)
    }
    fn sig_claim_data(&self, role: Role) -> claim::ClaimData {
        Contract::sig_claim_data(self, role)
    }
    fn state_from_end(&self, end: &[u32]) -> Option<(Vec<bool>, Vec<bool>, Vec<bool>)> {
        Contract::state_from_end(self, end)
    }
    fn describe_state_bits(&self, s: &[bool]) -> String {
        match self.state_from_bits(s) {
            Ok(st) => self.describe_state(&st),
            Err(_) => format!("<undecodable state {}>", bits_str(s)),
        }
    }
    fn describe_move_bits(&self, m: &[bool]) -> String {
        match self.move_from_bits(m) {
            Ok(mv) => self.describe_move(&mv),
            Err(_) => format!("<undecodable move {}>", bits_str(m)),
        }
    }
}

pub fn bits_str(b: &[bool]) -> String {
    b.iter().rev().map(|&x| if x { '1' } else { '0' }).collect()
}

/// Re-exports used by contract authors.
pub mod prelude {
    pub use crate::leaves::{Claim, DisproveSpec, LeafBuilder, LeafCtx};
    pub use crate::{Contract, DepthBind, EndBind, Extra, GraphShape, Invalid, MoveExtras, Outcome, Payout, DEPTH_BITS};
    pub use bitcoin::opcodes::all::*;
    pub use lngap_channel::Role;
    pub use lngap_lamport::{bits_to_uint, uint_to_bits};
}
