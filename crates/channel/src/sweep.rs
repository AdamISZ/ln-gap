//! Sweeps that need only one party's signature: penalty (revocation),
//! `to_remote` claims and delayed `to_local` claims.

use anyhow::Result;
use bitcoin::key::Keypair;
use bitcoin::{OutPoint, Sequence, Transaction, TxOut};
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::build_tx;
use lngap_btc::witness::WitnessStack;

/// One input of a sweep: which output, through which leaf, with what extra
/// witness data consumed *before* the signature (e.g. a revocation secret).
pub struct SweepInput<'a> {
    pub outpoint: OutPoint,
    pub prevout: TxOut,
    pub tree: &'a TapTree,
    pub leaf: &'a str,
    pub before_sig: Vec<Vec<u8>>,
}

/// Build and sign a sweep of `inputs` to `dest` minus `fee`, all inputs
/// signed with `kp`. Every leaf here is `[data...] <key> OP_CHECKSIG`, so the
/// witness is `before_sig..., sig` in consumption order — i.e. the sig is
/// consumed *last*... except that CHECKSIG is the last op, so it consumes the
/// sig after the data gadgets consumed theirs. Consumption order = script order.
pub fn build_sweep(
    inputs: &[SweepInput<'_>],
    dest: bitcoin::ScriptBuf,
    fee: bitcoin::Amount,
    kp: &Keypair,
    lock_time: bitcoin::absolute::LockTime,
) -> Result<Transaction> {
    let total: u64 = inputs.iter().map(|i| i.prevout.value.to_sat()).sum();
    let ins: Vec<(OutPoint, Sequence)> = inputs
        .iter()
        .map(|i| (i.outpoint, i.tree.leaf(i.leaf).expect("leaf").timelock.sequence()))
        .collect();
    let mut tx = build_tx(
        &ins,
        vec![TxOut { value: bitcoin::Amount::from_sat(total) - fee, script_pubkey: dest }],
        lock_time,
    );
    let prevouts: Vec<TxOut> = inputs.iter().map(|i| i.prevout.clone()).collect();
    for (n, i) in inputs.iter().enumerate() {
        let leaf = i.tree.leaf(i.leaf)?;
        lngap_btc::tx::check_timelock(&tx, n, &leaf.timelock)?;
        let sig = sign_tapscript(kp, &tx, n, &prevouts, &leaf.script)?;
        let mut w = WitnessStack::new();
        w.extend(i.before_sig.iter().cloned()).push(sig.as_ref().to_vec());
        tx.input[n].witness = w.build(&leaf.script, &i.tree.control_block(i.leaf)?);
    }
    Ok(tx)
}
