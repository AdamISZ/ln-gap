//! SPV facts in the dispute path: a claim that a ledger entry is anchored
//! in a block of a valid header chain from an agreed checkpoint, built as
//! a register-file claim (`lngap-contract::claim`) and disputed by
//! bisection. Phase 2b of `docs/planning/SPV_DISPUTE.md`.

pub mod chain;
pub mod claim;
pub mod ledger;
pub mod program;

pub use claim::{AnchorClaim, HeaderChainClaim};
pub use ledger::Ledger;
pub use program::Spv;
