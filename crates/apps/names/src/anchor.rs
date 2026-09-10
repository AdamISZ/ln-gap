//! The hub's anchor chain: each anchor is an `OP_RETURN <root>` transaction
//! of fixed layout (`lngap_spv::chain::anchor_tx`) spending the previous
//! anchor's change output, so that continuity is one outpoint check and the
//! root sits at a fixed byte offset for the in-Script claim.

use anyhow::Result;
use bitcoin::key::Keypair;
use bitcoin::{Amount, OutPoint, Transaction, TxOut};
use lngap_spv::chain::{anchor_root, anchor_tx, p2tr_spk, sign_keypath};
pub use lngap_spv::chain::verify_anchor_chain;

use crate::registry::Hash32;

/// The plain P2TR output the anchor chain starts from and returns to.
pub fn anchor_spk(key: &Keypair) -> bitcoin::ScriptBuf {
    p2tr_spk(&key.x_only_public_key().0)
}

/// Spend `prev` (the chain's tip) to an anchor committing `root`.
pub fn build_anchor_tx(key: &Keypair, prev: (OutPoint, TxOut), root: &Hash32, fee: Amount) -> Result<Transaction> {
    let mut tx = anchor_tx(prev.0, root, anchor_spk(key), prev.1.value - fee);
    sign_keypath(&mut tx, &prev.1, key)?;
    Ok(tx)
}

/// The root an anchor transaction carries (layout checked).
pub fn root_of(tx: &Transaction) -> Result<Hash32> {
    anchor_root(tx)
}
