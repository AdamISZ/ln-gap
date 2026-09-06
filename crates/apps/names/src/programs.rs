//! The two contract programs of the names demo.
//!
//! * `nreg:{params}` — bonded registration (N-REG). The hub locks a bond.
//!   The user may claim "receipted, unattested" from `d_receipt` on by
//!   revealing the hub's receipt; the hub's only answer is to reveal the
//!   attestation (`disprove_attested`), which then becomes public.
//! * `attestpay:{params}` — a payment gated on an attestation. The locker's
//!   money goes to the prover if the prover reveals the hub's attestation
//!   before the deadline, else back to the locker.

use std::sync::Arc;

use anyhow::{ensure, Result};
use lngap_contract::prelude::*;
use lngap_contract::{Program, ProgramRegistry};
use lngap_lamport::PublicKey;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NRegParams {
    pub req_id: u32,
    pub receipt_pk: PublicKey,
    pub attest_label: String,
    pub attest_pk: PublicKey,
    pub attest_value: u32,
    /// The hub promised inclusion by this height; claims are allowed from it.
    pub d_receipt: u32,
}

#[derive(Debug)]
pub struct NReg {
    pub params: NRegParams,
    name: String,
}

impl NReg {
    pub const PREFIX: &'static str = "nreg";
    pub const BOND_TO_HUB: u8 = 0;
    pub const BOND_TO_USER: u8 = 1;
    pub fn new(params: NRegParams) -> NReg {
        let name = format!("{}:{}", Self::PREFIX, serde_json::to_string(&params).expect("serializable"));
        NReg { params, name }
    }
    pub fn from_str(params: &str) -> Result<NReg> {
        Ok(NReg::new(serde_json::from_str(params)?))
    }
    pub fn receipt_extra(&self) -> Extra {
        Extra { label: crate::statements::receipt_label(self.params.req_id), pk: self.params.receipt_pk.clone(), value: crate::statements::receipt_value(self.params.req_id) }
    }
    pub fn attest_extra(&self) -> Extra {
        Extra { label: self.params.attest_label.clone(), pk: self.params.attest_pk.clone(), value: self.params.attest_value }
    }
}

impl Contract for NReg {
    type State = bool; // claimed
    type Move = bool;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![Outcome::new(Self::BOND_TO_HUB, "BondToHub", Payout::HubAll), Outcome::new(Self::BOND_TO_USER, "BondToUser", Payout::UserAll)]
    }
    fn initial(&self) -> bool {
        false
    }
    fn turn(&self, s: &bool) -> Option<Role> {
        (!s).then_some(Role::User)
    }
    fn transition(&self, s: &bool, m: &bool, mover: Role) -> Result<bool, Invalid> {
        if *s || mover != Role::User || !*m {
            return Err(Invalid("only the user may claim, once".into()));
        }
        Ok(true)
    }
    fn resolution(&self, s: &bool) -> Outcome {
        Contract::outcomes(self).swap_remove(usize::from(*s))
    }
    fn max_depth_from(&self, s: &bool) -> u32 {
        u32::from(!s)
    }
    fn n_state_bits(&self) -> usize {
        1
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &bool) -> Vec<bool> {
        vec![*s]
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1);
        Ok(b[0])
    }
    fn move_bits(&self, m: &bool) -> Vec<bool> {
        vec![*m]
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1);
        Ok(b[0])
    }
    fn move_extras(&self, depth: u32, prover: Role) -> MoveExtras {
        debug_assert!(depth == 1 && prover == Role::User);
        MoveExtras { cltv: Some(self.params.d_receipt), expects: vec![self.receipt_extra()] }
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        vec![
            // the hub did attest: revealing the attestation takes the bond back
            LeafBuilder::new(ctx).need(self.attest_extra()).finish_needs_only("attested"),
            LeafBuilder::new(ctx).new_uint(0..1).op(OP_NOT).finish("state_mismatch", |c| !c.new[0]),
            LeafBuilder::new(ctx).code_uint().int(i64::from(Self::BOND_TO_USER)).op(OP_NUMNOTEQUAL).finish("code_mismatch", |c| c.code != Self::BOND_TO_USER),
        ]
    }
    fn describe_state(&self, s: &bool) -> String {
        if *s { "claimed (receipted, unattested)".into() } else { "unclaimed".into() }
    }
    fn describe_move(&self, _m: &bool) -> String {
        format!("claim receipt {} unattested", self.params.req_id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestPayParams {
    pub prover: Role,
    pub attest_label: String,
    pub attest_pk: PublicKey,
    pub attest_value: u32,
}

#[derive(Debug)]
pub struct AttestPay {
    pub params: AttestPayParams,
    name: String,
}

impl AttestPay {
    pub const PREFIX: &'static str = "attestpay";
    pub const REFUND: u8 = 0;
    pub const PAID: u8 = 1;
    pub fn new(params: AttestPayParams) -> AttestPay {
        let name = format!("{}:{}", Self::PREFIX, serde_json::to_string(&params).expect("serializable"));
        AttestPay { params, name }
    }
    pub fn from_str(params: &str) -> Result<AttestPay> {
        Ok(AttestPay::new(serde_json::from_str(params)?))
    }
    pub fn attest_extra(&self) -> Extra {
        Extra { label: self.params.attest_label.clone(), pk: self.params.attest_pk.clone(), value: self.params.attest_value }
    }
    fn all_to(r: Role) -> Payout {
        match r {
            Role::User => Payout::UserAll,
            Role::Hub => Payout::HubAll,
        }
    }
}

impl Contract for AttestPay {
    type State = bool; // attested
    type Move = bool;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![
            Outcome::new(Self::REFUND, "Refund", Self::all_to(self.params.prover.other())),
            Outcome::new(Self::PAID, "Paid", Self::all_to(self.params.prover)),
        ]
    }
    fn initial(&self) -> bool {
        false
    }
    fn turn(&self, s: &bool) -> Option<Role> {
        (!s).then_some(self.params.prover)
    }
    fn transition(&self, s: &bool, m: &bool, mover: Role) -> Result<bool, Invalid> {
        if *s || mover != self.params.prover || !*m {
            return Err(Invalid("only the prover may present the attestation, once".into()));
        }
        Ok(true)
    }
    fn resolution(&self, s: &bool) -> Outcome {
        Contract::outcomes(self).swap_remove(usize::from(*s))
    }
    fn max_depth_from(&self, s: &bool) -> u32 {
        u32::from(!s)
    }
    fn n_state_bits(&self) -> usize {
        1
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &bool) -> Vec<bool> {
        vec![*s]
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1);
        Ok(b[0])
    }
    fn move_bits(&self, m: &bool) -> Vec<bool> {
        vec![*m]
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1);
        Ok(b[0])
    }
    fn move_extras(&self, _depth: u32, _prover: Role) -> MoveExtras {
        MoveExtras { cltv: None, expects: vec![self.attest_extra()] }
    }
    /// D6: nothing about a valid attestation can be disproved; only the
    /// generic consistency checks remain.
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        vec![
            LeafBuilder::new(ctx).new_uint(0..1).op(OP_NOT).finish("state_mismatch", |c| !c.new[0]),
            LeafBuilder::new(ctx).code_uint().int(i64::from(Self::PAID)).op(OP_NUMNOTEQUAL).finish("code_mismatch", |c| c.code != Self::PAID),
        ]
    }
    fn describe_state(&self, s: &bool) -> String {
        if *s { "attested: paid".into() } else { "pending".into() }
    }
    fn describe_move(&self, _m: &bool) -> String {
        format!("present {}", self.params.attest_label)
    }
}

/// Registry with both factories.
pub fn registry_programs() -> ProgramRegistry {
    let mut r = ProgramRegistry::new();
    r.register_factory(NReg::PREFIX, |p| Ok(Arc::new(NReg::from_str(p)?) as Arc<dyn Program>));
    r.register_factory(AttestPay::PREFIX, |p| Ok(Arc::new(AttestPay::from_str(p)?) as Arc<dyn Program>));
    r
}
