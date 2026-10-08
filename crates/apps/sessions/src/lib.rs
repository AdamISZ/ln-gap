//! LN-GAP 2.5's session layer (V25_POC_PLAN.md, Phase 6): a toy L2 of hub
//! IOUs ([`l2`]), the withdrawal statement mocked by a BitVMX program
//! ([`statement`]), and the session contract's payout and default
//! ([`session`]). The dispute is lngap-v25's graph over the search game.

pub mod l2;
pub mod session;
pub mod statement;
