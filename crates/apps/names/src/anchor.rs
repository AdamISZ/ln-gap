//! The anchor chain: the hub spends its anchor UTXO to a new output whose
//! taproot output key is the hub's anchor key tweaked with the registry
//! root (pay-to-contract). A UTXO spends once, so the chain is linear.

use anyhow::{anyhow, Result};
use bitcoin::hashes::Hash;
use bitcoin::key::{Keypair, TapTweak, XOnlyPublicKey};
use bitcoin::secp256k1::{Message, SECP256K1};
use bitcoin::sighash::{Prevouts, SighashCache, TapSighashType};
use bitcoin::taproot::TapNodeHash;
use bitcoin::{Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxOut};
use lngap_btc::tx::build_tx;

use crate::registry::Hash32;

/// Output script committing `root` under `anchor_key`.
pub fn anchor_spk(anchor_key: &XOnlyPublicKey, root: &Hash32) -> ScriptBuf {
    let tweaked = anchor_key.tap_tweak(SECP256K1, Some(TapNodeHash::from_byte_array(*root))).0;
    ScriptBuf::new_p2tr_tweaked(tweaked)
}

/// Does `spk` commit `root` under `anchor_key`?
pub fn verify_anchor_output(spk: &ScriptBuf, anchor_key: &XOnlyPublicKey, root: &Hash32) -> bool {
    *spk == anchor_spk(anchor_key, root)
}

/// Spend the current anchor (committing `prev_root`) to a new anchor
/// committing `root`. Key-path spend with the tweaked key.
pub fn build_anchor_tx(key: &Keypair, prev: (OutPoint, TxOut), prev_root: &Hash32, root: &Hash32, fee: Amount) -> Result<Transaction> {
    let xonly = key.x_only_public_key().0;
    anyhow::ensure!(verify_anchor_output(&prev.1.script_pubkey, &xonly, prev_root), "previous anchor does not commit prev_root");
    let out = TxOut { value: prev.1.value - fee, script_pubkey: anchor_spk(&xonly, root) };
    let mut tx = build_tx(&[(prev.0, Sequence::ENABLE_RBF_NO_LOCKTIME)], vec![out], bitcoin::absolute::LockTime::ZERO);
    let tweaked = key.tap_tweak(SECP256K1, Some(TapNodeHash::from_byte_array(*prev_root)));
    let sighash = SighashCache::new(&tx)
        .taproot_key_spend_signature_hash(0, &Prevouts::All(std::slice::from_ref(&prev.1)), TapSighashType::Default)
        .map_err(|e| anyhow!("sighash: {e}"))?;
    let sig = SECP256K1.sign_schnorr(&Message::from_digest(sighash.to_byte_array()), &tweaked.to_keypair());
    tx.input[0].witness = bitcoin::Witness::from_slice(&[sig.as_ref().to_vec()]);
    Ok(tx)
}
