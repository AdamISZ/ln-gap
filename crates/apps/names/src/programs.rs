//! The contract programs of the names demo, on SPV facts.
//!
//! * `nreg:{params}` — bonded registration. The hub locks a bond. From
//!   `d_receipt` the user may claim "receipted, not anchored" by revealing
//!   the hub's receipt (depth 1). The hub's only answer is an inclusion
//!   proof: a bisection claim that the entry is in the ledger anchored at
//!   the promised height in the chain from the checkpoint (depth 2). The
//!   user may refute that chain with a heavier one (depth 3).
//! * `anchorpay:{params}` — a payment gated on an inclusion proof by the
//!   prover (depth 1), refutable by a heavier chain (depth 2).
//!
//! Proof data (headers, the anchor transaction, siblings) is served
//! off-chain; the harness models this with a shared [`ServedData`] store
//! both parties read.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use anyhow::{ensure, Result};
use lngap_contract::claim::{ClaimData, ClaimSpec};
use lngap_contract::prelude::*;
use lngap_contract::{Program, ProgramRegistry};
use lngap_lamport::PublicKey;
use lngap_spv::AnchorShape;
use serde::{Deserialize, Serialize};

/// Proof data by slot: `"{slot}/incl"` for the inclusion proof, `"{slot}/refute"` for a heavier chain.
#[derive(Clone, Default)]
pub struct ServedData(Arc<Mutex<HashMap<String, ClaimData>>>);

impl std::fmt::Debug for ServedData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ServedData({} slots)", self.0.lock().unwrap().len())
    }
}

impl ServedData {
    pub fn put(&self, key: &str, data: ClaimData) {
        self.0.lock().unwrap().insert(key.to_string(), data);
    }
    pub fn get(&self, key: &str) -> Option<ClaimData> {
        self.0.lock().unwrap().get(key).cloned()
    }
    pub fn has(&self, key: &str) -> bool {
        self.0.lock().unwrap().contains_key(key)
    }
}

fn all_to(r: Role) -> Payout {
    match r {
        Role::User => Payout::UserAll,
        Role::Hub => Payout::HubAll,
    }
}

// ----- nreg -----

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NRegParams {
    pub req_id: u32,
    pub receipt_pk: PublicKey,
    /// Claims are allowed from this height (the promised anchor height plus a grace).
    pub d_receipt: u32,
    pub shape: AnchorShape,
    pub slot: String,
}

#[derive(Debug)]
pub struct NReg {
    pub params: NRegParams,
    name: String,
    store: ServedData,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NRegState {
    Init,
    /// The user claimed on the receipt.
    Claimed,
    /// The hub proved inclusion.
    Refuted,
    /// The user refuted the hub's chain.
    Reinstated,
}

impl NReg {
    pub const PREFIX: &'static str = "nreg";
    pub const BOND_TO_HUB: u8 = 0;
    pub const BOND_TO_USER: u8 = 1;
    pub fn new(params: NRegParams, store: ServedData) -> NReg {
        let name = format!("{}:{}", Self::PREFIX, serde_json::to_string(&params).expect("serializable"));
        NReg { params, name, store }
    }
    pub fn from_str(params: &str, store: ServedData) -> Result<NReg> {
        Ok(NReg::new(serde_json::from_str(params)?, store))
    }
    pub fn receipt_extra(&self) -> Extra {
        Extra { label: crate::statements::receipt_label(self.params.req_id), pk: self.params.receipt_pk.clone(), value: crate::statements::receipt_value(self.params.req_id) }
    }
}

impl Contract for NReg {
    type State = NRegState;
    type Move = bool;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![Outcome::new(Self::BOND_TO_HUB, "BondToHub", Payout::HubAll), Outcome::new(Self::BOND_TO_USER, "BondToUser", Payout::UserAll)]
    }
    fn initial(&self) -> NRegState {
        NRegState::Init
    }
    fn turn(&self, s: &NRegState) -> Option<Role> {
        match s {
            NRegState::Init => Some(Role::User),
            NRegState::Claimed => Some(Role::Hub),
            NRegState::Refuted => Some(Role::User),
            NRegState::Reinstated => None,
        }
    }
    fn transition(&self, s: &NRegState, m: &bool, mover: Role) -> Result<NRegState, Invalid> {
        match (s, mover, m) {
            (NRegState::Init, Role::User, true) => Ok(NRegState::Claimed),
            (NRegState::Claimed, Role::Hub, true) => Ok(NRegState::Refuted),
            (NRegState::Refuted, Role::User, true) => Ok(NRegState::Reinstated),
            _ => Err(Invalid("not this party's move".into())),
        }
    }
    fn resolution(&self, s: &NRegState) -> Outcome {
        let o = Contract::outcomes(self);
        match s {
            NRegState::Init | NRegState::Refuted => o[Self::BOND_TO_HUB as usize].clone(),
            NRegState::Claimed | NRegState::Reinstated => o[Self::BOND_TO_USER as usize].clone(),
        }
    }
    fn max_depth_from(&self, s: &NRegState) -> u32 {
        match s {
            NRegState::Init => 3,
            NRegState::Claimed => 2,
            NRegState::Refuted => 1,
            NRegState::Reinstated => 0,
        }
    }
    fn n_state_bits(&self) -> usize {
        2
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &NRegState) -> Vec<bool> {
        uint_to_bits(*s as u32, 2)
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<NRegState> {
        ensure!(b.len() == 2);
        Ok(match bits_to_uint(b) {
            0 => NRegState::Init,
            1 => NRegState::Claimed,
            2 => NRegState::Refuted,
            _ => NRegState::Reinstated,
        })
    }
    fn move_bits(&self, m: &bool) -> Vec<bool> {
        vec![*m]
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1);
        Ok(b[0])
    }
    fn move_extras(&self, depth: u32, _prover: Role) -> MoveExtras {
        if depth == 1 {
            MoveExtras { cltv: Some(self.params.d_receipt), expects: vec![self.receipt_extra()] }
        } else {
            MoveExtras::default()
        }
    }
    fn claim(&self, depth: u32) -> Option<ClaimSpec> {
        match depth {
            2 => Some(self.params.shape.spec()),
            3 => Some(self.params.shape.refutation().spec()),
            _ => None,
        }
    }
    fn claim_data(&self, depth: u32) -> ClaimData {
        match depth {
            2 => self.store.get(&format!("{}/incl", self.params.slot)).unwrap_or_default(),
            3 => self.store.get(&format!("{}/refute", self.params.slot)).unwrap_or_default(),
            _ => vec![],
        }
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        let want_state = i64::from(ctx.depth); // Claimed = 1, Refuted = 2, Reinstated = 3
        let want_code = i64::from(if ctx.depth == 2 { Self::BOND_TO_HUB } else { Self::BOND_TO_USER });
        vec![
            LeafBuilder::new(ctx).new_uint(0..2).int(want_state).op(OP_NUMNOTEQUAL).finish("state_mismatch", move |c| bits_to_uint(&c.new) != want_state as u32),
            LeafBuilder::new(ctx).code_uint().int(want_code).op(OP_NUMNOTEQUAL).finish("code_mismatch", move |c| i64::from(c.code) != want_code),
        ]
    }
    fn describe_state(&self, s: &NRegState) -> String {
        match s {
            NRegState::Init => "unclaimed".into(),
            NRegState::Claimed => "claimed (receipted, not anchored)".into(),
            NRegState::Refuted => "hub proved inclusion".into(),
            NRegState::Reinstated => "user refuted the hub's chain".into(),
        }
    }
    fn describe_move(&self, _m: &bool) -> String {
        format!("claim receipt {} unanchored / prove inclusion / refute the chain", self.params.req_id)
    }
}

// ----- anchorpay -----

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AnchorPayParams {
    pub prover: Role,
    pub shape: AnchorShape,
    pub slot: String,
}

#[derive(Debug)]
pub struct AnchorPay {
    pub params: AnchorPayParams,
    name: String,
    store: ServedData,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PayState {
    Init,
    Paid,
    Refuted,
}

impl AnchorPay {
    pub const PREFIX: &'static str = "anchorpay";
    pub const REFUND: u8 = 0;
    pub const PAID: u8 = 1;
    pub fn new(params: AnchorPayParams, store: ServedData) -> AnchorPay {
        let name = format!("{}:{}", Self::PREFIX, serde_json::to_string(&params).expect("serializable"));
        AnchorPay { params, name, store }
    }
    pub fn from_str(params: &str, store: ServedData) -> Result<AnchorPay> {
        Ok(AnchorPay::new(serde_json::from_str(params)?, store))
    }
}

impl Contract for AnchorPay {
    type State = PayState;
    type Move = bool;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![Outcome::new(Self::REFUND, "Refund", all_to(self.params.prover.other())), Outcome::new(Self::PAID, "Paid", all_to(self.params.prover))]
    }
    fn initial(&self) -> PayState {
        PayState::Init
    }
    fn turn(&self, s: &PayState) -> Option<Role> {
        match s {
            PayState::Init => Some(self.params.prover),
            PayState::Paid => Some(self.params.prover.other()),
            PayState::Refuted => None,
        }
    }
    fn transition(&self, s: &PayState, m: &bool, mover: Role) -> Result<PayState, Invalid> {
        match (s, m) {
            (PayState::Init, true) if mover == self.params.prover => Ok(PayState::Paid),
            (PayState::Paid, true) if mover != self.params.prover => Ok(PayState::Refuted),
            _ => Err(Invalid("not this party's move".into())),
        }
    }
    fn resolution(&self, s: &PayState) -> Outcome {
        let o = Contract::outcomes(self);
        match s {
            PayState::Paid => o[Self::PAID as usize].clone(),
            _ => o[Self::REFUND as usize].clone(),
        }
    }
    fn max_depth_from(&self, s: &PayState) -> u32 {
        match s {
            PayState::Init => 2,
            PayState::Paid => 1,
            PayState::Refuted => 0,
        }
    }
    fn n_state_bits(&self) -> usize {
        2
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &PayState) -> Vec<bool> {
        uint_to_bits(*s as u32, 2)
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<PayState> {
        ensure!(b.len() == 2);
        Ok(match bits_to_uint(b) {
            0 => PayState::Init,
            1 => PayState::Paid,
            2 => PayState::Refuted,
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
    fn claim(&self, depth: u32) -> Option<ClaimSpec> {
        match depth {
            1 => Some(self.params.shape.spec()),
            2 => Some(self.params.shape.refutation().spec()),
            _ => None,
        }
    }
    fn claim_data(&self, depth: u32) -> ClaimData {
        match depth {
            1 => self.store.get(&format!("{}/incl", self.params.slot)).unwrap_or_default(),
            2 => self.store.get(&format!("{}/refute", self.params.slot)).unwrap_or_default(),
            _ => vec![],
        }
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        let want_state = i64::from(ctx.depth); // Paid = 1, Refuted = 2
        let want_code = i64::from(if ctx.depth == 1 { Self::PAID } else { Self::REFUND });
        vec![
            LeafBuilder::new(ctx).new_uint(0..2).int(want_state).op(OP_NUMNOTEQUAL).finish("state_mismatch", move |c| bits_to_uint(&c.new) != want_state as u32),
            LeafBuilder::new(ctx).code_uint().int(want_code).op(OP_NUMNOTEQUAL).finish("code_mismatch", move |c| i64::from(c.code) != want_code),
        ]
    }
    fn describe_state(&self, s: &PayState) -> String {
        format!("{s:?}")
    }
    fn describe_move(&self, _m: &bool) -> String {
        "prove the entry is anchored / refute the chain".into()
    }
}

/// Registry with both factories reading proof data from `store`.
pub fn registry_programs(store: ServedData) -> ProgramRegistry {
    let mut r = ProgramRegistry::new();
    let s1 = store.clone();
    r.register_factory(NReg::PREFIX, move |p| Ok(Arc::new(NReg::from_str(p, s1.clone())?) as Arc<dyn Program>));
    let s2 = store;
    r.register_factory(AnchorPay::PREFIX, move |p| Ok(Arc::new(AnchorPay::from_str(p, s2.clone())?) as Arc<dyn Program>));
    r
}
