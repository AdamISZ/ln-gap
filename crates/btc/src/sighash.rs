//! BIP-341 script-path sighash and Schnorr signing with SIGHASH_DEFAULT
//! (and SIGHASH_ALL|ANYONECANPAY for pre-signed transactions whose
//! broadcaster adds the fee).

use anyhow::{anyhow, Result};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::secp256k1::{schnorr, Message, SECP256K1};
use bitcoin::sighash::{Prevouts, SighashCache, TapSighashType};
use bitcoin::taproot::{LeafVersion, TapLeafHash};
use bitcoin::{Script, Transaction, TxOut};

/// The message a tapscript-path signature commits to.
pub fn tapscript_sighash(
    tx: &Transaction,
    input: usize,
    prevouts: &[TxOut],
    leaf: &Script,
) -> Result<Message> {
    let leaf_hash = TapLeafHash::from_script(leaf, LeafVersion::TapScript);
    let mut cache = SighashCache::new(tx);
    let h = cache
        .taproot_script_spend_signature_hash(input, &Prevouts::All(prevouts), leaf_hash, TapSighashType::Default)
        .map_err(|e| anyhow!("sighash: {e}"))?;
    Ok(Message::from_digest(h.to_byte_array()))
}

/// Sign a script-path spend with SIGHASH_DEFAULT. The 64-byte signature goes in
/// the witness as-is (no sighash byte).
pub fn sign_tapscript(
    kp: &Keypair,
    tx: &Transaction,
    input: usize,
    prevouts: &[TxOut],
    leaf: &Script,
) -> Result<schnorr::Signature> {
    let msg = tapscript_sighash(tx, input, prevouts, leaf)?;
    Ok(SECP256K1.sign_schnorr(&msg, kp))
}

/// Sign a script-path spend with SIGHASH_ALL|ANYONECANPAY: the signature
/// commits to this input (its prevout only) and every output, so whoever
/// broadcasts can add inputs, its own fee. Returns the 65-byte signature
/// (the sighash byte appended), as the witness carries it.
pub fn sign_tapscript_acp(kp: &Keypair, tx: &Transaction, input: usize, prevout: &TxOut, leaf: &Script) -> Result<Vec<u8>> {
    let leaf_hash = TapLeafHash::from_script(leaf, LeafVersion::TapScript);
    let mut cache = SighashCache::new(tx);
    let h = cache
        .taproot_script_spend_signature_hash(input, &Prevouts::One(input, prevout), leaf_hash, TapSighashType::AllPlusAnyoneCanPay)
        .map_err(|e| anyhow!("sighash: {e}"))?;
    let sig = SECP256K1.sign_schnorr(&Message::from_digest(h.to_byte_array()), kp);
    let mut v = sig.as_ref().to_vec();
    v.push(TapSighashType::AllPlusAnyoneCanPay as u8);
    Ok(v)
}

pub fn verify_tapscript(
    pk: &XOnlyPublicKey,
    sig: &schnorr::Signature,
    tx: &Transaction,
    input: usize,
    prevouts: &[TxOut],
    leaf: &Script,
) -> Result<()> {
    let msg = tapscript_sighash(tx, input, prevouts, leaf)?;
    SECP256K1.verify_schnorr(sig, &msg, pk).map_err(|e| anyhow!("bad signature: {e}"))
}

trait ToByteArray {
    fn to_byte_array(&self) -> [u8; 32];
}
impl ToByteArray for bitcoin::TapSighash {
    fn to_byte_array(&self) -> [u8; 32] {
        use bitcoin::hashes::Hash;
        Hash::to_byte_array(*self)
    }
}
