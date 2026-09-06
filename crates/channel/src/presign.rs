//! A transaction that both parties sign in advance through a 2-of-2 leaf.

use anyhow::{anyhow, ensure, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::taproot::ControlBlock;
use bitcoin::{Transaction, TxOut, Txid, Witness};
use lngap_btc::sighash::{sign_tapscript, verify_tapscript};
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::check_timelock;
use lngap_btc::witness::WitnessStack;
use serde::{Deserialize, Serialize};

use crate::{PartyPubKeys, Role};

/// Which pre-signed transaction a signature belongs to.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct GraphKey {
    /// Whose commitment version the graph hangs off.
    pub version: Role,
    pub contract_id: u32,
    /// Path inside the contract's graph, e.g. `settle`, `move_1`, `move_1/split_UserWins`.
    pub label: String,
}

impl std::fmt::Display for GraphKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-commit/c{}/{}", self.version, self.contract_id, self.label)
    }
}

#[derive(Clone, Debug)]
pub struct PresignedTx {
    pub label: String,
    /// Unsigned; input 0 spends the parent through `leaf`.
    pub tx: Transaction,
    pub prevouts: Vec<TxOut>,
    pub leaf: Leaf,
    pub control_block: ControlBlock,
    pub sigs: [Option<Signature>; 2],
    /// For the log: what this tx does when broadcast.
    pub role_description: String,
}

impl PresignedTx {
    /// Build for a tx whose input 0 spends `parent_tree`'s leaf `leaf_name`.
    pub fn new(
        label: impl Into<String>,
        tx: Transaction,
        prevouts: Vec<TxOut>,
        parent_tree: &TapTree,
        leaf_name: &str,
        role_description: impl Into<String>,
    ) -> Result<PresignedTx> {
        let leaf = parent_tree.leaf(leaf_name)?.clone();
        check_timelock(&tx, 0, &leaf.timelock)?;
        ensure!(prevouts.len() == tx.input.len(), "prevouts/inputs mismatch");
        Ok(PresignedTx {
            label: label.into(),
            tx,
            prevouts,
            control_block: parent_tree.control_block(leaf_name)?,
            leaf,
            sigs: [None, None],
            role_description: role_description.into(),
        })
    }

    pub fn txid(&self) -> Txid {
        self.tx.compute_txid()
    }

    pub fn sign_as(&mut self, role: Role, kp: &Keypair) -> Result<Signature> {
        let sig = sign_tapscript(kp, &self.tx, 0, &self.prevouts, &self.leaf.script)?;
        self.sigs[role.idx()] = Some(sig);
        Ok(sig)
    }

    /// Verify and store the counterparty's signature.
    pub fn add_sig(&mut self, role: Role, sig: Signature, keys: &[PartyPubKeys; 2]) -> Result<()> {
        verify_tapscript(&keys[role.idx()].payment, &sig, &self.tx, 0, &self.prevouts, &self.leaf.script)
            .map_err(|e| anyhow!("{}: {role}'s signature invalid: {e}", self.label))?;
        self.sigs[role.idx()] = Some(sig);
        Ok(())
    }

    pub fn fully_signed(&self) -> bool {
        self.sigs.iter().all(Option::is_some)
    }

    /// Witness for the 2-of-2 leaf convention: `sig_user, sig_hub` consumed
    /// first, then `extra` (e.g. Lamport reveals) in consumption order.
    pub fn witness(&self, extra: &[Vec<u8>]) -> Result<Witness> {
        let su = self.sigs[0].ok_or_else(|| anyhow!("{}: missing user signature", self.label))?;
        let sh = self.sigs[1].ok_or_else(|| anyhow!("{}: missing hub signature", self.label))?;
        let mut w = WitnessStack::new();
        w.push(su.as_ref().to_vec()).push(sh.as_ref().to_vec()).extend(extra.iter().cloned());
        Ok(w.build(&self.leaf.script, &self.control_block))
    }

    /// The broadcastable transaction.
    pub fn finalize(&self, extra: &[Vec<u8>]) -> Result<Transaction> {
        let mut tx = self.tx.clone();
        tx.input[0].witness = self.witness(extra)?;
        Ok(tx)
    }
}
