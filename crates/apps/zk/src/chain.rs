//! The final step's output on Bitcoin (D59): what the prover's refutation
//! would create at the last step of a computation dispute. Two leaves:
//! `zk_prove_<class>` (the prover's payment key after `delta`, then the
//! proof over the parked pair) and `timeout` (the claimant's key after
//! `delta + delta'`). The claimant's disproves and `not_timely` would sit
//! beside them; none reads the final step's execution.

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
        let mut b = Builder::new().csv(delta).checksigverify(&xonly(prover)).into_script().into_bytes();
        b.extend_from_slice(proof.script.as_bytes());
        let prove = ScriptBuf::from_bytes(b);
        let timeout = Builder::new().csv(delta + delta_prime).checksig(&xonly(claimant)).into_script();
        let tree = TapTree::new(vec![Leaf::new(proof.name.clone(), prove.clone(), Timelock::csv(delta)), Leaf::new("timeout", timeout.clone(), Timelock::csv(delta + delta_prime))])?;
        Ok(FinalOutput { tree, prove_name: proof.name.clone(), prove, timeout, delta, delta_prime })
    }

    /// The prover's proof: the pair reveal under the mover's pair key over
    /// (prior head, new head), then the prover's signature.
    pub fn prove_tx(&self, op: OutPoint, prev: &TxOut, pay: TxOut, prover: &Keypair, pair_key: &WotsSecret, prior: &[u8; 48], new: &[u8; 48]) -> Result<Transaction> {
        let mut tx = build_spend(op, &Timelock::csv(self.delta), vec![pay]);
        let sig = sign_tapscript(prover, &tx, 0, std::slice::from_ref(prev), &self.prove)?;
        let mut w = disprove_witness(&pair_key.sign(&[prior.as_slice(), new.as_slice()].concat()).map_err(|e| anyhow!("{e}"))?);
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &self.prove, &self.tree.control_block(&self.prove_name)?);
        Ok(tx)
    }

    /// The claimant's timeout.
    pub fn timeout_tx(&self, op: OutPoint, prev: &TxOut, pay: TxOut, claimant: &Keypair) -> Result<Transaction> {
        let mut tx = build_spend(op, &Timelock::csv(self.delta + self.delta_prime), vec![pay]);
        let sig = sign_tapscript(claimant, &tx, 0, std::slice::from_ref(prev), &self.timeout)?;
        tx.input[0].witness = tapscript_witness(&[sig.as_ref().to_vec()], &self.timeout, &self.tree.control_block("timeout")?);
        Ok(tx)
    }

    /// A payment to this same output (for tests and the demo).
    pub fn pay_back(&self, value: Amount) -> TxOut {
        TxOut { value, script_pubkey: self.tree.script_pubkey() }
    }
}
