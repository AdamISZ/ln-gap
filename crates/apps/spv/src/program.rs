//! The `spv` program: the hub claims an anchored ledger entry (depth 1);
//! the user may refute it with a heavier header chain from the same
//! checkpoint (depth 2, decision 8). Both claims are verified by bisection.

use anyhow::{ensure, Result};
use lngap_contract::claim::{ClaimData, ClaimSpec};
use lngap_contract::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpvState {
    Init,
    HubClaimed,
    UserRefuted,
}

#[derive(Debug)]
pub struct Spv {
    /// The hub's claim (depth 1).
    pub hub: (ClaimSpec, ClaimData),
    /// The user's refutation (depth 2): a header chain one longer than the hub's.
    pub user: (ClaimSpec, ClaimData),
}

impl Spv {
    pub const NAME: &'static str = "spv";
    pub const HUB_WINS: u8 = 0;
    pub const USER_WINS: u8 = 1;
}

impl Contract for Spv {
    type State = SpvState;
    type Move = bool;

    fn name(&self) -> &str {
        Self::NAME
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![Outcome::new(Self::HUB_WINS, "HubWins", Payout::HubAll), Outcome::new(Self::USER_WINS, "UserWins", Payout::UserAll)]
    }
    fn initial(&self) -> SpvState {
        SpvState::Init
    }
    fn turn(&self, s: &SpvState) -> Option<Role> {
        match s {
            SpvState::Init => Some(Role::Hub),
            SpvState::HubClaimed => Some(Role::User),
            SpvState::UserRefuted => None,
        }
    }
    fn transition(&self, s: &SpvState, m: &bool, mover: Role) -> Result<SpvState, Invalid> {
        match (s, mover, m) {
            (SpvState::Init, Role::Hub, true) => Ok(SpvState::HubClaimed),
            (SpvState::HubClaimed, Role::User, true) => Ok(SpvState::UserRefuted),
            _ => Err(Invalid("not this party's move".into())),
        }
    }
    fn resolution(&self, s: &SpvState) -> Outcome {
        let o = Contract::outcomes(self);
        match s {
            SpvState::Init => o[Self::USER_WINS as usize].clone(),
            SpvState::HubClaimed => o[Self::HUB_WINS as usize].clone(),
            SpvState::UserRefuted => o[Self::USER_WINS as usize].clone(),
        }
    }
    fn max_depth_from(&self, s: &SpvState) -> u32 {
        match s {
            SpvState::Init => 2,
            SpvState::HubClaimed => 1,
            SpvState::UserRefuted => 0,
        }
    }
    fn n_state_bits(&self) -> usize {
        2
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &SpvState) -> Vec<bool> {
        uint_to_bits(*s as u32, 2)
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<SpvState> {
        ensure!(b.len() == 2);
        Ok(match bits_to_uint(b) {
            0 => SpvState::Init,
            1 => SpvState::HubClaimed,
            2 => SpvState::UserRefuted,
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
            1 => Some(self.hub.0.clone()),
            2 => Some(self.user.0.clone()),
            _ => None,
        }
    }
    fn claim_data(&self, depth: u32) -> ClaimData {
        match depth {
            1 => self.hub.1.clone(),
            2 => self.user.1.clone(),
            _ => vec![],
        }
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        // depth 1: new state must be HubClaimed (1) with code HubWins; depth 2: UserRefuted (2) with code UserWins
        let (want_state, want_code) = if ctx.depth == 1 { (1i64, i64::from(Self::HUB_WINS)) } else { (2, i64::from(Self::USER_WINS)) };
        vec![
            LeafBuilder::new(ctx).new_uint(0..2).int(want_state).op(OP_NUMNOTEQUAL).finish("state_mismatch", move |c| bits_to_uint(&c.new) != want_state as u32),
            LeafBuilder::new(ctx).code_uint().int(want_code).op(OP_NUMNOTEQUAL).finish("code_mismatch", move |c| i64::from(c.code) != want_code),
        ]
    }
    fn describe_state(&self, s: &SpvState) -> String {
        format!("{s:?}")
    }
    fn describe_move(&self, _m: &bool) -> String {
        "present the claim".into()
    }
}
