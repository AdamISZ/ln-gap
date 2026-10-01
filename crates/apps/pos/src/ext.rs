//! A game family defined outside this crate (Z3 step 6): `Game::Zk`'s
//! leaves live in `lngap-zk`, which depends on this crate, so the graph
//! reaches them through this trait (as blackjack's commitments ride in
//! `PosInstance::bj`).

use bitcoin::ScriptBuf;
use lngap_channel::Role;
use lngap_lamport::winternitz::WotsPublic;

use crate::ttt::{Layout, PosLeaf};

/// What the graph needs from a family it doesn't know.
pub trait Family: Send + Sync + std::fmt::Debug {
    /// The claimant's disproves over the parked pair at `l.depth` (each
    /// script after the challenger's gate, as for the built-in games).
    fn disprove_leaves(&self, l: &Layout, refute: &WotsPublic) -> Vec<PosLeaf>;
    /// The depth whose refuted output the mover must PROVE (D59): there the
    /// mover's split is replaced by `prove_leaves`, and the claimant's split
    /// waits a further `delta'`.
    fn final_depth(&self) -> Option<u32>;
    /// The mover's proofs at the final depth: (name, script after the
    /// mover's payment-key gate).
    fn prove_leaves(&self, l: &Layout, refute: &WotsPublic) -> Vec<(String, ScriptBuf)>;
    /// The venue's registered check of an entry at depth `d` (D55):
    /// authorship under the depth's state key, and whatever availability
    /// the family needs (D60: the bodies open the heads; D61: the input
    /// signed).
    fn entry_ok(&self, d: u32, state_key: &WotsPublic, entry: &[u8]) -> bool;
    /// Further one-time keys whose double signature forfeits the pot to
    /// the other side (D61: the prover's input keys): (leaf name, key, the
    /// key's holder).
    fn equiv_keys(&self) -> Vec<(String, WotsPublic, Role)>;
    /// The outcome code `settle` pays at the deadline (nobody disputed).
    fn settle_code(&self) -> u8;
}
