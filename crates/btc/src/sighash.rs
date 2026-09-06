//! BIP-341 script-path sighash and Schnorr signing with SIGHASH_DEFAULT.

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
