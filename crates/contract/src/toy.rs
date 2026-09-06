//! `CoinFlipByReveal`: the M2 toy contract. The user reveals a bit, then the
//! hub reveals a bit; XOR = 0 → user wins, 1 → hub wins; whoever is on turn
//! and does not reveal forfeits. Small enough that every disprove leaf is a
//! few dozen opcodes, which is the point: it exercises Settle / Move /
//! Disprove / Split before tic-tac-toe does.

use anyhow::{ensure, Result};

use crate::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlipState {
    pub user: Option<bool>,
    pub hub: Option<bool>,
}

#[derive(Debug, Default)]
pub struct CoinFlip;

impl CoinFlip {
    pub const NAME: &'static str = "coinflip";
    // state bit layout
    const U_REV: usize = 0;
    const U_BIT: usize = 1;
    const H_REV: usize = 2;
    const H_BIT: usize = 3;
    pub const USER_WINS: u8 = 0;
    pub const HUB_WINS: u8 = 1;
}

impl Contract for CoinFlip {
    type State = FlipState;
    type Move = bool;

    fn name(&self) -> &str {
        Self::NAME
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![Outcome::new(Self::USER_WINS, "UserWins", Payout::UserAll), Outcome::new(Self::HUB_WINS, "HubWins", Payout::HubAll)]
    }
    fn initial(&self) -> FlipState {
        FlipState { user: None, hub: None }
    }
    fn turn(&self, s: &FlipState) -> Option<Role> {
        match (s.user, s.hub) {
            (None, _) => Some(Role::User),
            (Some(_), None) => Some(Role::Hub),
            _ => None,
        }
    }
    fn transition(&self, s: &FlipState, m: &bool, mover: Role) -> Result<FlipState, Invalid> {
        if self.turn(s) != Some(mover) {
            return Err(Invalid(format!("{mover} is not on turn")));
        }
        let mut s2 = s.clone();
        match mover {
            Role::User => s2.user = Some(*m),
            Role::Hub => s2.hub = Some(*m),
        }
        Ok(s2)
    }
    fn resolution(&self, s: &FlipState) -> Outcome {
        let code = match (s.user, s.hub) {
            (Some(u), Some(h)) => u8::from(u ^ h),
            (None, _) => Self::HUB_WINS,   // user on turn forfeits
            (Some(_), None) => Self::USER_WINS, // hub on turn forfeits
        };
        self.outcomes().into_iter().find(|o| o.code == code).unwrap()
    }
    fn max_depth_from(&self, s: &FlipState) -> u32 {
        u32::from(s.user.is_none()) + u32::from(s.hub.is_none())
    }
    fn n_state_bits(&self) -> usize {
        4
    }
    fn n_move_bits(&self) -> usize {
        1
    }
    fn state_bits(&self, s: &FlipState) -> Vec<bool> {
        vec![s.user.is_some(), s.user.unwrap_or(false), s.hub.is_some(), s.hub.unwrap_or(false)]
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<FlipState> {
        ensure!(b.len() == 4, "coinflip state is 4 bits");
        Ok(FlipState { user: b[Self::U_REV].then_some(b[Self::U_BIT]), hub: b[Self::H_REV].then_some(b[Self::H_BIT]) })
    }
    fn move_bits(&self, m: &bool) -> Vec<bool> {
        vec![*m]
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<bool> {
        ensure!(b.len() == 1, "coinflip move is 1 bit");
        Ok(b[0])
    }

    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        let p = ctx.prover;
        // 1. prover was not on turn in the prior state
        let not_on_turn = match p {
            Role::User => LeafBuilder::new(ctx).prior_uint(Self::U_REV..Self::U_REV + 1).finish("not_on_turn", |c| c.prior[Self::U_REV]),
            Role::Hub => LeafBuilder::new(ctx)
                .prior_uint(Self::U_REV..Self::U_REV + 1)
                .prior_uint(Self::H_REV..Self::H_REV + 1)
                // stack: u_rev h_rev
                .op(OP_SWAP)
                .op(OP_NOT)
                .op(OP_BOOLOR)
                .finish("not_on_turn", |c| !c.prior[Self::U_REV] || c.prior[Self::H_REV]),
        };
        // 2. new state != prior + flag + m·bitvalue
        let (flag, bitval): (i64, i64) = match p {
            Role::User => (1 << Self::U_REV, 1 << Self::U_BIT),
            Role::Hub => (1 << Self::H_REV, 1 << Self::H_BIT),
        };
        let state_mismatch = LeafBuilder::new(ctx)
            .prior_uint(0..4)
            .mv_uint(0..1)
            .new_uint(0..4)
            // stack: prior m new
            .op(OP_TOALTSTACK)
            .op(OP_IF)
            .int(bitval)
            .op(OP_ELSE)
            .int(0)
            .op(OP_ENDIF)
            .op(OP_ADD)
            .int(flag)
            .op(OP_ADD)
            .op(OP_FROMALTSTACK)
            .op(OP_NUMNOTEQUAL)
            .finish("state_mismatch", move |c| {
                let expected = i64::from(bits_to_uint(&c.prior)) + flag + if c.mv[0] { bitval } else { 0 };
                expected != i64::from(bits_to_uint(&c.new))
            });
        // 3. code != R(new)
        let code_mismatch = LeafBuilder::new(ctx)
            .new_uint(Self::U_REV..Self::U_REV + 1)
            .new_uint(Self::U_BIT..Self::U_BIT + 1)
            .new_uint(Self::H_REV..Self::H_REV + 1)
            .new_uint(Self::H_BIT..Self::H_BIT + 1)
            .code_uint()
            // stack: u_rev u_bit h_rev h_bit code
            .op(OP_TOALTSTACK)
            .op(OP_SWAP)
            .op(OP_IF)
            .op(OP_NUMNOTEQUAL) // u_rev (u_bit != h_bit)
            .op(OP_NIP)
            .op(OP_ELSE)
            .op(OP_2DROP)
            .op(OP_NOT)
            .op(OP_ENDIF)
            .op(OP_FROMALTSTACK)
            .op(OP_NUMNOTEQUAL)
            .finish("code_mismatch", |c| {
                let (u_rev, u_bit, h_rev, h_bit) = (c.new[0], c.new[1], c.new[2], c.new[3]);
                let expected = if h_rev { u8::from(u_bit != h_bit) } else { u8::from(!u_rev) };
                expected != c.code
            });
        vec![not_on_turn, state_mismatch, code_mismatch]
    }

    fn describe_state(&self, s: &FlipState) -> String {
        let f = |b: Option<bool>| match b {
            None => "?".to_string(),
            Some(x) => u8::from(x).to_string(),
        };
        format!("user={} hub={}", f(s.user), f(s.hub))
    }
}
