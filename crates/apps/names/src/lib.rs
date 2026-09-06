//! A rudimentary name registry with a bonded hub (plan §8.2).
//!
//! * `registry`: the rules (commit/reveal, earliest anchored commit wins,
//!   owner-signed transfers with a validity height), the event log, its
//!   Merkle root, and client-side resolution.
//! * `anchor`: the hub's anchor chain — one UTXO spent per interval to an
//!   output whose key is tweaked with the registry root.
//! * `statements`: Lamport-signed hub statements (receipts, attestations).
//! * `programs`: the contract programs — `nreg` (bonded registration) and
//!   `attestpay` (payment gated on an attestation).
//! * `hub`: the registry operator; `user`: a name owner; `audit`: the
//!   off-chain auditor the harness runs.

pub mod anchor;
pub mod audit;
pub mod hub;
pub mod programs;
pub mod registry;
pub mod statements;
pub mod user;

pub use programs::{registry_programs, AttestPay, NReg};
