//! The final step's output on Bitcoin (D59): what the prover's refutation
//! would create at the last step of a computation dispute. Two leaves:
//! `zk_prove_<class>` (the prover's payment key after `delta + delta'`,
//! then the proof over the parked pair) and `timeout` (the claimant's key
//! after `delta + 2·delta'`). The claimant's disproves and `not_timely` sit
//! beside them after `delta` (D59 amended, 2026-10-01): the claimant's
//! disprove window comes first and is its own, as the other games' disprove
//! window precedes the mover's splits; a proof that raced the disproves
//! could pre-empt an S1/S2 disprove of a step that executes correctly on a
//! false read.

use anyhow::{anyhow, Result};
use bitcoin::key::Keypair;
use bitcoin::script::Builder;
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::xonly;
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::refute::disprove_witness;
use lngap_pos::ttt::PosLeaf;

/// The output and its two leaves.
pub struct FinalOutput {
    pub tree: TapTree,
    pub prove_name: String,
    pub prove: ScriptBuf,
    pub timeout: ScriptBuf,
    pub delta: u16,
    pub delta_prime: u16,
}

impl FinalOutput {
    pub fn new(proof: &PosLeaf, prover: &Keypair, claimant: &Keypair, delta: u16, delta_prime: u16) -> Result<FinalOutput> {
        let (pa, ta) = (delta + delta_prime, delta + 2 * delta_prime);
        let mut b = Builder::new().csv(pa).checksigverify(&xonly(prover)).into_script().into_bytes();
        b.extend_from_slice(proof.script.as_bytes());
        let prove = ScriptBuf::from_bytes(b);
        let timeout = Builder::new().csv(ta).checksig(&xonly(claimant)).into_script();
        let tree = TapTree::new(vec![Leaf::new(proof.name.clone(), prove.clone(), Timelock::csv(pa)), Leaf::new("timeout", timeout.clone(), Timelock::csv(ta))])?;
        Ok(FinalOutput { tree, prove_name: proof.name.clone(), prove, timeout, delta, delta_prime })
    }

    /// The proof's relative lock: after the claimant's disprove window.
    pub fn prove_after(&self) -> u16 {
        self.delta + self.delta_prime
    }

    /// The timeout's: after the prover's window.
    pub fn timeout_after(&self) -> u16 {
        self.delta + 2 * self.delta_prime
    }

    /// The prover's proof: the final step's extra data (checked against
    /// the new head's digest), the pair reveal under the mover's pair key
    /// over (prior head, new head), then the prover's signature.
    pub fn prove_tx(&self, op: OutPoint, prev: &TxOut, pay: TxOut, prover: &Keypair, pair_key: &WotsSecret, step: &crate::FinalStep, prior: &[u8; 48], new: &[u8; 48]) -> Result<Transaction> {
        let mut tx = build_spend(op, &Timelock::csv(self.prove_after()), vec![pay]);
        let sig = sign_tapscript(prover, &tx, 0, std::slice::from_ref(prev), &self.prove)?;
        let mut w = step.extra_witness();
        w.extend(disprove_witness(&pair_key.sign(&[prior.as_slice(), new.as_slice()].concat()).map_err(|e| anyhow!("{e}"))?));
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &self.prove, &self.tree.control_block(&self.prove_name)?);
        Ok(tx)
    }

    /// The claimant's timeout.
    pub fn timeout_tx(&self, op: OutPoint, prev: &TxOut, pay: TxOut, claimant: &Keypair) -> Result<Transaction> {
        let mut tx = build_spend(op, &Timelock::csv(self.timeout_after()), vec![pay]);
        let sig = sign_tapscript(claimant, &tx, 0, std::slice::from_ref(prev), &self.timeout)?;
        tx.input[0].witness = tapscript_witness(&[sig.as_ref().to_vec()], &self.timeout, &self.tree.control_block("timeout")?);
        Ok(tx)
    }

    /// A payment to this same output (for tests and the demo).
    pub fn pay_back(&self, value: Amount) -> TxOut {
        TxOut { value, script_pubkey: self.tree.script_pubkey() }
    }
}
