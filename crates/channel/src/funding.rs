//! Building and signing the funding transaction. Each party contributes one
//! coin held at its payout script; the output is the 2-of-2 funding tree.

use anyhow::Result;
use bitcoin::key::Keypair;
use bitcoin::{Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxOut};
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::build_tx;
use lngap_btc::witness::WitnessStack;

/// Unsigned funding tx: inputs `contribs` (user first, hub second), one output.
pub fn build_funding_tx(contribs: &[(OutPoint, TxOut); 2], funding_spk: ScriptBuf, amount: Amount) -> Transaction {
    let ins: Vec<(OutPoint, Sequence)> = contribs.iter().map(|c| (c.0, Sequence::ENABLE_RBF_NO_LOCKTIME)).collect();
    build_tx(&ins, vec![TxOut { value: amount, script_pubkey: funding_spk }], bitcoin::absolute::LockTime::ZERO)
}

/// Sign input `idx` of the funding tx, which spends a payout-tree coin with `kp`.
pub fn sign_funding_input(tx: &mut Transaction, idx: usize, prevouts: &[TxOut], payout_tree: &TapTree, kp: &Keypair) -> Result<()> {
    let leaf = payout_tree.leaf("claim")?;
    let sig = sign_tapscript(kp, tx, idx, prevouts, &leaf.script)?;
    tx.input[idx].witness = WitnessStack::new().push(sig.as_ref().to_vec()).build(&leaf.script, &payout_tree.control_block("claim")?);
    Ok(())
}
