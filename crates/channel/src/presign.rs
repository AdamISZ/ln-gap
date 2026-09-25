//! A transaction that both parties sign in advance through a 2-of-2 leaf.
//!
//! One role's signature may be an adaptor PRE-signature (D49, D52: the fee
//! lock's `claim`): `adaptor = Some((role, T))` says `role` signs under the
//! adaptor point `T`, so its half is not a signature until whoever learns
//! `t` with `t·G = T` completes it ([`PresignedTx::complete`]), and the
//! completed signature, once public, reveals `t` to the pre-signer
//! ([`PresignedTx::extract_secret`]).

use anyhow::{anyhow, bail, ensure, Result};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::secp256k1::{PublicKey, SecretKey};
use bitcoin::taproot::ControlBlock;
use bitcoin::{Transaction, TxOut, Txid, Witness};
use lngap_btc::adaptor::{adaptor_complete, adaptor_extract, adaptor_sign, adaptor_verify, AdaptorSig};
use lngap_btc::sighash::{sign_tapscript, tapscript_sighash, verify_tapscript};
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

/// A party's signature on a pre-signed transaction as exchanged in
/// `CommitSigs`: a full signature, or an adaptor pre-signature for the
/// role a [`PresignedTx::adaptor`] names.
#[derive(Clone, Debug)]
pub enum GraphSig {
    Full(Signature),
    Adaptor(AdaptorSig),
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
    /// `Some((role, T))`: `role`'s signature is an adaptor pre-signature
    /// locked to `T`, held in `pre_sig` until completed.
    pub adaptor: Option<(Role, PublicKey)>,
    pub pre_sig: Option<AdaptorSig>,
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
            adaptor: None,
            pre_sig: None,
            role_description: role_description.into(),
        })
    }

    /// `role`'s signature is to be an adaptor pre-signature locked to
    /// `point` (the fee lock: the payer pre-signs, the payee completes).
    pub fn with_adaptor(mut self, role: Role, point: PublicKey) -> Self {
        self.adaptor = Some((role, point));
        self
    }

    pub fn txid(&self) -> Txid {
        self.tx.compute_txid()
    }

    fn is_adaptor_role(&self, role: Role) -> bool {
        matches!(self.adaptor, Some((r, _)) if r == role)
    }

    /// Sign as `role`: a full signature, or — for the adaptor role — the
    /// pre-signature under the adaptor point.
    pub fn sign_as(&mut self, role: Role, kp: &Keypair) -> Result<GraphSig> {
        if let Some((r, t)) = &self.adaptor {
            if *r == role {
                let msg = tapscript_sighash(&self.tx, 0, &self.prevouts, &self.leaf.script)?;
                let pre = adaptor_sign(kp, &msg, t);
                self.pre_sig = Some(pre.clone());
                return Ok(GraphSig::Adaptor(pre));
            }
        }
        let sig = sign_tapscript(kp, &self.tx, 0, &self.prevouts, &self.leaf.script)?;
        self.sigs[role.idx()] = Some(sig);
        Ok(GraphSig::Full(sig))
    }

    /// `role`'s stored signature (full, or the pre-signature for the
    /// adaptor role), as it goes into `CommitSigs`.
    pub fn my_sig(&self, role: Role) -> Option<GraphSig> {
        if self.is_adaptor_role(role) {
            self.pre_sig.clone().map(GraphSig::Adaptor)
        } else {
            self.sigs[role.idx()].map(GraphSig::Full)
        }
    }

    /// Verify and store the counterparty's signature — a pre-signature
    /// checked against the adaptor point for the adaptor role, a full
    /// signature otherwise.
    pub fn add_sig(&mut self, role: Role, sig: GraphSig, keys: &[PartyPubKeys; 2]) -> Result<()> {
        match (self.adaptor, sig) {
            (Some((r, t)), GraphSig::Adaptor(pre)) if r == role => {
                let msg = tapscript_sighash(&self.tx, 0, &self.prevouts, &self.leaf.script)?;
                ensure!(adaptor_verify(&keys[role.idx()].payment, &msg, &t, &pre), "{}: {role}'s pre-signature does not verify under the adaptor point", self.label);
                self.pre_sig = Some(pre);
            }
            (Some((r, _)), GraphSig::Full(_)) if r == role => bail!("{}: {role} must pre-sign under the adaptor point", self.label),
            (_, GraphSig::Adaptor(_)) => bail!("{}: {role} sent a pre-signature where a signature is due", self.label),
            (_, GraphSig::Full(sig)) => {
                verify_tapscript(&keys[role.idx()].payment, &sig, &self.tx, 0, &self.prevouts, &self.leaf.script)
                    .map_err(|e| anyhow!("{}: {role}'s signature invalid: {e}", self.label))?;
                self.sigs[role.idx()] = Some(sig);
            }
        }
        Ok(())
    }

    /// Both halves held: full signatures, or the pre-signature for the
    /// adaptor role (completable, not yet broadcastable).
    pub fn fully_signed(&self) -> bool {
        Role::BOTH.iter().all(|r| if self.is_adaptor_role(*r) { self.pre_sig.is_some() } else { self.sigs[r.idx()].is_some() })
    }

    /// Complete the adaptor role's pre-signature with `t` (the payee, once
    /// the venue's attestation revealed it). Checked: a wrong `t` yields
    /// an invalid signature, which is rejected here rather than by the
    /// node.
    pub fn complete(&mut self, t: &SecretKey, keys: &[PartyPubKeys; 2]) -> Result<()> {
        let (role, _) = self.adaptor.ok_or_else(|| anyhow!("{}: no adaptor", self.label))?;
        let pre = self.pre_sig.as_ref().ok_or_else(|| anyhow!("{}: no pre-signature to complete", self.label))?;
        let sig = adaptor_complete(pre, t);
        verify_tapscript(&keys[role.idx()].payment, &sig, &self.tx, 0, &self.prevouts, &self.leaf.script)
            .map_err(|_| anyhow!("{}: the secret does not open the adaptor point", self.label))?;
        self.sigs[role.idx()] = Some(sig);
        Ok(())
    }

    /// The adaptor secret, from the CONFIRMED transaction's witness (the
    /// pre-signer learns `t = s − s'` once the payee's completed signature
    /// is public).
    pub fn extract_secret(&self, confirmed: &Transaction) -> Result<SecretKey> {
        let (_, t_point) = self.adaptor.ok_or_else(|| anyhow!("{}: no adaptor", self.label))?;
        let pre = self.pre_sig.as_ref().ok_or_else(|| anyhow!("{}: no pre-signature", self.label))?;
        ensure!(confirmed.compute_txid() == self.txid(), "{}: not this transaction", self.label);
        // the completed signature is the 64-byte witness element whose
        // difference from the pre-scalar opens the adaptor point
        for elem in confirmed.input[0].witness.iter().filter(|e| e.len() == 64) {
            if let Ok(sig) = Signature::from_slice(elem) {
                if let Some(t) = adaptor_extract(pre, &sig) {
                    if PublicKey::from_secret_key(bitcoin::secp256k1::SECP256K1, &t) == t_point {
                        return Ok(t);
                    }
                }
            }
        }
        bail!("{}: no witness element completes the pre-signature", self.label)
    }

    /// Witness for the 2-of-2 leaf convention: `sig_user, sig_hub` consumed
    /// first, then `extra` (e.g. Lamport reveals) in consumption order.
    pub fn witness(&self, extra: &[Vec<u8>]) -> Result<Witness> {
        let su = self.sigs[0].ok_or_else(|| anyhow!("{}: missing user signature{}", self.label, if self.is_adaptor_role(Role::User) { " (the pre-signature is not completed)" } else { "" }))?;
        let sh = self.sigs[1].ok_or_else(|| anyhow!("{}: missing hub signature{}", self.label, if self.is_adaptor_role(Role::Hub) { " (the pre-signature is not completed)" } else { "" }))?;
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
