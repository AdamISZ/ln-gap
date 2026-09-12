//! Contract programs for the fact-chain names registry.
//!
//! `nreg-fc:{params}` — bonded registration. Same state machine as `nreg`
//! (Init → Claimed → Refuted → Reinstated) but the facts come from the fact
//! chain. Stage 1: no ClaimSpec (the bisection is deferred). The proof is
//! verified natively off-chain; the on-chain contract is the state machine.
//!
//! `anchorpay-fc:{params}` — payment gated on fact-chain inclusion. Same as
//! `anchorpay` but with the fact chain as the fact source.

use anyhow::{ensure, Result};
use lngap_contract::prelude::*;
use lngap_contract::{Program, ProgramRegistry};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

// ----- nreg-fc -----

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NRegFcParams {
    pub req_id: u32,
    /// Claims are allowed from this fact-chain height (h_max + grace).
    pub claim_from: u32,
    /// The fact-chain checkpoint digest when the bond opened.
    pub checkpoint: [u8; 20],
    /// The fact-chain checkpoint height.
    pub checkpoint_height: u32,
    /// The entry will be in a block at height <= h_max.
    pub h_max: u32,
}

#[derive(Debug)]
pub struct NRegFc {
    pub params: NRegFcParams,
    name: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NRegFcState {
    Init,
    Claimed,
    Refuted,
    Reinstated,
}

impl NRegFc {
    pub const PREFIX: &'static str = "nreg-fc";
    pub const BOND_TO_HUB: u8 = 0;
    pub const BOND_TO_USER: u8 = 1;
    pub fn new(params: NRegFcParams) -> NRegFc {
        let name = format!(
            "{}:{}",
            Self::PREFIX,
            serde_json::to_string(&params).expect("serializable")
        );
        NRegFc { params, name }
    }
    pub fn from_str(params: &str) -> Result<NRegFc> {
        Ok(NRegFc::new(serde_json::from_str(params)?))
    }
}

impl Contract for NRegFc {
    type State = NRegFcState;
    type Move = bool;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![
            Outcome::new(Self::BOND_TO_HUB, "BondToHub", Payout::HubAll),
            Outcome::new(Self::BOND_TO_USER, "BondToUser", Payout::UserAll),
        ]
    }
    fn initial(&self) -> NRegFcState {
        NRegFcState::Init
    }
    fn turn(&self, s: &NRegFcState) -> Option<Role> {
        match s {
            NRegFcState::Init => Some(Role::User),
            NRegFcState::Claimed => Some(Role::Hub),
            NRegFcState::Refuted => Some(Role::User),
            NRegFcState::Reinstated => None,
        }
    }
    fn transition(&self, s: &NRegFcState, m: &bool, mover: Role) -> Result<NRegFcState, Invalid> {
        match (s, mover, m) {
            (NRegFcState::Init, Role::User, true) => Ok(NRegFcState::Claimed),
            (NRegFcState::Claimed, Role::Hub, true) => Ok(NRegFcState::Refuted),
            (NRegFcState::Refuted, Role::User, true) => Ok(NRegFcState::Reinstated),
            _ => Err(Invalid("not this party's move".into())),
        }
    }
    fn resolution(&self, s: &NRegFcState) -> Outcome {
        let o = Contract::outcomes(self);
        match s {
            NRegFcState::Init | NRegFcState::Refuted => o[Self::BOND_TO_HUB as usize].clone(),
            NRegFcState::Claimed | NRegFcState::Reinstated => o[Self::BOND_TO_USER as usize].clone(),
        }
    }
    fn max_depth_from(&self, s: &NRegFcState) -> u32 {
        match s {
            NRegFcState::Init => 3,
            NRegFcState::Claimed => 2,
            NRegFcState::Refuted => 1,
            NRegFcState::Reinstated => 0,
        }
    }
    fn n_state_bits(&self) -> usize {
        2
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &NRegFcState) -> Vec<bool> {
        uint_to_bits(*s as u32, 2)
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<NRegFcState> {
        ensure!(b.len() == 2);
        Ok(match bits_to_uint(b) {
            0 => NRegFcState::Init,
            1 => NRegFcState::Claimed,
            2 => NRegFcState::Refuted,
            _ => NRegFcState::Reinstated,
        })
    }
    fn move_bits(&self, m: &bool) -> Vec<bool> {
        vec![*m]
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1);
        Ok(b[0])
    }
    /// CLTV at claim_from for the user's initial claim (depth 1).
    fn move_extras(&self, depth: u32, _prover: Role) -> MoveExtras {
        if depth == 1 {
            MoveExtras {
                cltv: Some(self.params.claim_from),
                expects: vec![],
            }
        } else {
            MoveExtras::default()
        }
    }
    /// Stage 1: no ClaimSpec. The proof is verified natively off-chain.
    fn claim(&self, _from: &[bool], _depth: u32) -> Option<lngap_contract::claim::ClaimSpec> {
        None
    }
    fn claim_data(&self, _from: &[bool], _depth: u32) -> lngap_contract::claim::ClaimData {
        vec![]
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        // Same as nreg: every move advances state by 1; code is BondToHub iff new state is Refuted (2)
        vec![
            LeafBuilder::new(ctx)
                .prior_uint(0..2)
                .new_uint(0..2)
                .op(OP_SWAP)
                .int(1)
                .op(OP_ADD)
                .op(OP_NUMNOTEQUAL)
                .finish("state_mismatch", |c| {
                    bits_to_uint(&c.new) != bits_to_uint(&c.prior) + 1
                }),
            LeafBuilder::new(ctx)
                .new_uint(0..2)
                .code_uint()
                .op(OP_SWAP)
                .int(2)
                .op(OP_NUMNOTEQUAL)
                .op(OP_NUMNOTEQUAL)
                .finish("code_mismatch", |c| {
                    u32::from(c.code) != u32::from(bits_to_uint(&c.new) != 2)
                }),
        ]
    }
    fn describe_state(&self, s: &NRegFcState) -> String {
        match s {
            NRegFcState::Init => "unclaimed".into(),
            NRegFcState::Claimed => "claimed (not included by h_max)".into(),
            NRegFcState::Refuted => "hub proved inclusion".into(),
            NRegFcState::Reinstated => "user refuted with heavier chain".into(),
        }
    }
    fn describe_move(&self, _m: &bool) -> String {
        format!("claim request {} / prove inclusion / refute chain", self.params.req_id)
    }
}

// ----- anchorpay-fc -----

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnchorPayFcParams {
    pub prover: Role,
    pub checkpoint: [u8; 20],
    pub checkpoint_height: u32,
    pub h_max: u32,
}

#[derive(Debug)]
pub struct AnchorPayFc {
    pub params: AnchorPayFcParams,
    name: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PayFcState {
    Init,
    Paid,
    Refuted,
}

impl AnchorPayFc {
    pub const PREFIX: &'static str = "anchorpay-fc";
    pub const REFUND: u8 = 0;
    pub const PAID: u8 = 1;
    pub fn new(params: AnchorPayFcParams) -> AnchorPayFc {
        let name = format!(
            "{}:{}",
            Self::PREFIX,
            serde_json::to_string(&params).expect("serializable")
        );
        AnchorPayFc { params, name }
    }
    pub fn from_str(params: &str) -> Result<AnchorPayFc> {
        Ok(AnchorPayFc::new(serde_json::from_str(params)?))
    }
}

fn all_to(r: Role) -> Payout {
    match r {
        Role::User => Payout::UserAll,
        Role::Hub => Payout::HubAll,
    }
}

impl Contract for AnchorPayFc {
    type State = PayFcState;
    type Move = bool;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![
            Outcome::new(Self::REFUND, "Refund", all_to(self.params.prover.other())),
            Outcome::new(Self::PAID, "Paid", all_to(self.params.prover)),
        ]
    }
    fn initial(&self) -> PayFcState {
        PayFcState::Init
    }
    fn turn(&self, s: &PayFcState) -> Option<Role> {
        match s {
            PayFcState::Init => Some(self.params.prover),
            PayFcState::Paid => Some(self.params.prover.other()),
            PayFcState::Refuted => None,
        }
    }
    fn transition(&self, s: &PayFcState, m: &bool, mover: Role) -> Result<PayFcState, Invalid> {
        match (s, m) {
            (PayFcState::Init, true) if mover == self.params.prover => Ok(PayFcState::Paid),
            (PayFcState::Paid, true) if mover != self.params.prover => Ok(PayFcState::Refuted),
            _ => Err(Invalid("not this party's move".into())),
        }
    }
    fn resolution(&self, s: &PayFcState) -> Outcome {
        let o = Contract::outcomes(self);
        match s {
            PayFcState::Paid => o[Self::PAID as usize].clone(),
            _ => o[Self::REFUND as usize].clone(),
        }
    }
    fn max_depth_from(&self, s: &PayFcState) -> u32 {
        match s {
            PayFcState::Init => 2,
            PayFcState::Paid => 1,
            PayFcState::Refuted => 0,
        }
    }
    fn n_state_bits(&self) -> usize {
        2
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &PayFcState) -> Vec<bool> {
        uint_to_bits(*s as u32, 2)
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<PayFcState> {
        ensure!(b.len() == 2);
        Ok(match bits_to_uint(b) {
            0 => PayFcState::Init,
            1 => PayFcState::Paid,
            2 => PayFcState::Refuted,
            x => anyhow::bail!("bad state {x}"),
        })
    }
    fn move_bits(&self, m: &bool) -> Vec<bool> {
        vec![*m]
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1);
        Ok(b[0])
    }
    fn claim(&self, _from: &[bool], _depth: u32) -> Option<lngap_contract::claim::ClaimSpec> {
        None
    }
    fn claim_data(&self, _from: &[bool], _depth: u32) -> lngap_contract::claim::ClaimData {
        vec![]
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        vec![
            LeafBuilder::new(ctx)
                .prior_uint(0..2)
                .new_uint(0..2)
                .op(OP_SWAP)
                .int(1)
                .op(OP_ADD)
                .op(OP_NUMNOTEQUAL)
                .finish("state_mismatch", |c| {
                    bits_to_uint(&c.new) != bits_to_uint(&c.prior) + 1
                }),
            LeafBuilder::new(ctx)
                .new_uint(0..2)
                .code_uint()
                .op(OP_SWAP)
                .int(1)
                .op(OP_NUMEQUAL)
                .op(OP_NUMNOTEQUAL)
                .finish("code_mismatch", |c| {
                    u32::from(c.code) != u32::from(bits_to_uint(&c.new) == 1)
                }),
        ]
    }
    fn describe_state(&self, s: &PayFcState) -> String {
        format!("{s:?}")
    }
    fn describe_move(&self, _m: &bool) -> String {
        "prove inclusion on fact chain / refute chain".into()
    }
}

/// Registry with both factories.
pub fn registry_programs() -> ProgramRegistry {
    let mut r = ProgramRegistry::new();
    r.register_factory(NRegFc::PREFIX, move |p| {
        Ok(Arc::new(NRegFc::from_str(p)?) as Arc<dyn Program>)
    });
    r.register_factory(AnchorPayFc::PREFIX, move |p| {
        Ok(Arc::new(AnchorPayFc::from_str(p)?) as Arc<dyn Program>)
    });
    r
}
