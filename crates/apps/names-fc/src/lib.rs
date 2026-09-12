//! Name registry contracts on the PoW fact chain.
//!
//! Same state machines as `lngap_names::programs` (nreg, anchorpay) but the
//! facts come from the fact chain, not Bitcoin SPV. Stage 1: no ClaimSpec
//! (the bisection dispute path is deferred). The proof (header chain + entry)
//! is verified natively off-chain; the on-chain contract is the state machine
//! with Moves, Splits, and Settle. The heavier-chain refutation (N9) works
//! because it is protocol-level (present one more header), not Script-level.

pub mod hub;
pub mod programs;

pub use hub::{FcHub, FcPromise, HubFaults};
pub use programs::{registry_programs, AnchorPayFc, AnchorPayFcParams, NRegFc, NRegFcParams};

// Re-export the registry types and user from lngap_names so consumers don't
// need a separate dependency.
pub use lngap_names::registry::{Event, Ledger};
pub use lngap_names::user::NamesUser;
