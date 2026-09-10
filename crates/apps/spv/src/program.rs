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
    fn claim(&self, from: &[bool], depth: u32) -> Option<ClaimSpec> {
        // the state the depth-th move counted from `from` leaves from
        match bits_to_uint(from) + depth - 1 {
            0 => Some(self.hub.0.clone()),
            1 => Some(self.user.0.clone()),
            _ => None,
        }
    }
    fn claim_data(&self, from: &[bool], depth: u32) -> ClaimData {
        match bits_to_uint(from) + depth - 1 {
            0 => self.hub.1.clone(),
            1 => self.user.1.clone(),
            _ => vec![],
        }
    }
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        // every move advances the state by one; the code is UserWins iff the new state is UserRefuted (2)
        vec![
            LeafBuilder::new(ctx).prior_uint(0..2).new_uint(0..2).op(OP_SWAP).int(1).op(OP_ADD).op(OP_NUMNOTEQUAL).finish("state_mismatch", |c| bits_to_uint(&c.new) != bits_to_uint(&c.prior) + 1),
            LeafBuilder::new(ctx).new_uint(0..2).code_uint().op(OP_SWAP).int(2).op(OP_NUMEQUAL).op(OP_NUMNOTEQUAL).finish("code_mismatch", |c| u32::from(c.code) != u32::from(bits_to_uint(&c.new) == 2)),
        ]
    }
    fn describe_state(&self, s: &SpvState) -> String {
        format!("{s:?}")
    }
    fn describe_move(&self, _m: &bool) -> String {
        "present the claim".into()
    }
}
