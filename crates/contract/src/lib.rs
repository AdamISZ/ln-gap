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

/// What a Move leaf requires beyond the prover's own commitments.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MoveExtras {
    /// The move is only valid at or after this height (`OP_CLTV`).
    pub cltv: Option<u32>,
    pub expects: Vec<Extra>,
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
    pub use crate::{Contract, Extra, Invalid, MoveExtras, Outcome, Payout};
    pub use bitcoin::opcodes::all::*;
    pub use lngap_channel::Role;
    pub use lngap_lamport::{bits_to_uint, uint_to_bits};
}
