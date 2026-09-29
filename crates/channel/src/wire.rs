//! A serialisable form of the channel's messages, for two parties in
//! different processes (the demos' shared-directory bus). A `Propose`
//! carries the state's balances and its contract ids; the receiver maps
//! each id to the contract instance it built itself (both parties build
//! identical instances from the offers they exchanged; the commitment
//! signatures then fail on any disagreement). Graph signatures travel as
//! full Schnorr signatures; adaptor pre-signatures (the fee lock's) are
//! not supported here.

use std::sync::Arc;

use anyhow::{anyhow, bail, Result};
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::Amount;
use serde::{Deserialize, Serialize};

use crate::presign::{GraphKey, GraphSig};
use crate::protocol::{Envelope, Msg};
use crate::{ChannelState, ContractOutput, Role};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum WireMsg {
    Propose { seq: u64, balances: [u64; 2], contracts: Vec<u32> },
    CommitSigs { seq: u64, commit_sig: String, graph_sigs: Vec<(GraphKey, String)> },
    RevokeAndAck { seq: u64, secret: String, next_rev_hash: String },
    CloseRequest { fee: u64, sig: String },
    CloseSig { sig: String },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WireEnvelope {
    pub from: Role,
    pub to: Role,
    pub msg: WireMsg,
}

fn sig_hex(s: &Signature) -> String {
    hex::encode(s.as_ref())
}

fn sig_from(h: &str) -> Result<Signature> {
    Ok(Signature::from_slice(&hex::decode(h)?)?)
}

impl WireEnvelope {
    pub fn from_env(e: &Envelope) -> Result<WireEnvelope> {
        let msg = match &e.msg {
            Msg::Propose { state } => WireMsg::Propose {
                seq: state.seq,
                balances: [state.balances[0].to_sat(), state.balances[1].to_sat()],
                contracts: state.contracts.iter().map(|c| c.id()).collect(),
            },
            Msg::CommitSigs { seq, commit_sig, graph_sigs } => WireMsg::CommitSigs {
                seq: *seq,
                commit_sig: sig_hex(commit_sig),
                graph_sigs: graph_sigs
                    .iter()
                    .map(|(k, s)| match s {
                        GraphSig::Full(s) => Ok((k.clone(), sig_hex(s))),
                        GraphSig::Adaptor(_) => bail!("adaptor pre-signatures do not travel on the wire"),
                    })
                    .collect::<Result<_>>()?,
            },
            Msg::RevokeAndAck { seq, secret, next_rev_hash } => WireMsg::RevokeAndAck { seq: *seq, secret: hex::encode(secret), next_rev_hash: hex::encode(next_rev_hash) },
            Msg::CloseRequest { fee, sig } => WireMsg::CloseRequest { fee: fee.to_sat(), sig: sig_hex(sig) },
            Msg::CloseSig { sig } => WireMsg::CloseSig { sig: sig_hex(sig) },
        };
        Ok(WireEnvelope { from: e.from, to: e.to, msg })
    }

    /// Back to an [`Envelope`], each contract id resolved to the
    /// receiver's own instance.
    pub fn into_env(self, resolve: impl Fn(u32) -> Option<Arc<dyn ContractOutput>>) -> Result<Envelope> {
        let msg = match self.msg {
            WireMsg::Propose { seq, balances, contracts } => Msg::Propose {
                state: ChannelState {
                    seq,
                    balances: [Amount::from_sat(balances[0]), Amount::from_sat(balances[1])],
                    contracts: contracts.iter().map(|id| resolve(*id).ok_or_else(|| anyhow!("proposed state carries contract {id}, which I have not built"))).collect::<Result<_>>()?,
                },
            },
            WireMsg::CommitSigs { seq, commit_sig, graph_sigs } => Msg::CommitSigs {
                seq,
                commit_sig: sig_from(&commit_sig)?,
                graph_sigs: graph_sigs.into_iter().map(|(k, s)| Ok((k, GraphSig::Full(sig_from(&s)?)))).collect::<Result<_>>()?,
            },
            WireMsg::RevokeAndAck { seq, secret, next_rev_hash } => Msg::RevokeAndAck {
                seq,
                secret: hex::decode(&secret)?.try_into().map_err(|_| anyhow!("a revocation secret is 32 bytes"))?,
                next_rev_hash: hex::decode(&next_rev_hash)?.try_into().map_err(|_| anyhow!("a revocation hash is 20 bytes"))?,
            },
            WireMsg::CloseRequest { fee, sig } => Msg::CloseRequest { fee: Amount::from_sat(fee), sig: sig_from(&sig)? },
            WireMsg::CloseSig { sig } => Msg::CloseSig { sig: sig_from(&sig)? },
        };
        Ok(Envelope { from: self.from, to: self.to, msg })
    }
}
