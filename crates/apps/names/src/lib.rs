//! A rudimentary name registry with a bonded hub (plan §8.2), on SPV facts
//! (SPV_DISPUTE.md phase 3).
//!
//! * `registry`: the rules (commit/reveal, earliest anchored commit wins,
//!   owner-signed transfers with a validity height), events with their
//!   64-byte ledger entries, the sparse-Merkle ledger, resolution.
//! * `anchor`: the hub's anchor chain — one UTXO spent per anchor to an
//!   `OP_RETURN <root>` transaction of fixed layout.
//! * `statements`: the hub's Lamport-signed receipts ("request r will be
//!   anchored at height h").
//! * `programs`: the contract programs — `nreg` (bonded registration: the
//!   user claims on the receipt, the hub answers with an inclusion proof,
//!   the user may refute the chain) and `anchorpay` (a payment gated on an
//!   inclusion proof).
//! * `hub`: the registry operator; `user`: a name owner; `audit`: the
//!   off-chain auditor the harness runs.

pub mod anchor;
pub mod audit;
pub mod hub;
pub mod programs;
pub mod registry;
pub mod statements;
pub mod user;

pub use programs::{registry_programs, AnchorPay, NReg, ServedData};
