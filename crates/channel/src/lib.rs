//! The channel: two asymmetric commitment transactions per state, revocation
//! of old states, unilateral close with a delay for the closer, penalty, and
//! room on every commitment for *contract outputs* whose trees and pre-signed
//! graphs are supplied by the `lngap-contract` crate through [`ContractOutput`].

pub mod chain;
pub mod commit;
pub mod funding;
pub mod presign;
pub mod protocol;
pub mod sweep;

use std::sync::Arc;

use anyhow::{ensure, Result};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::script::Builder;
use bitcoin::{Amount, OutPoint, ScriptBuf, TxOut};
use lngap_btc::keys::{xonly, Seed};
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_btc::{hash160, Hash160};
use serde::{Deserialize, Serialize};

pub use commit::{CommitCtx, Commitment};
pub use presign::PresignedTx;

/// Which side of the channel. Index 0 is the user, 1 is the hub, everywhere.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Role {
    User = 0,
    Hub = 1,
}

impl Role {
    pub const BOTH: [Role; 2] = [Role::User, Role::Hub];
    pub fn other(self) -> Role {
        match self {
            Role::User => Role::Hub,
            Role::Hub => Role::User,
        }
    }
    pub fn idx(self) -> usize {
        self as usize
    }
    pub fn name(self) -> &'static str {
        match self {
            Role::User => "user",
            Role::Hub => "hub",
        }
    }
}

impl std::fmt::Display for Role {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Channel-wide constants agreed at open.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct ChannelParams {
    pub funding_amount: Amount,
    pub to_self_delay: u16,
    /// Fee of a commitment transaction, paid from the broadcaster's balance.
    pub commit_fee: Amount,
    /// Fee of every pre-signed transaction, paid from the value it carries.
    pub presign_fee: Amount,
    /// Outputs below this are omitted.
    pub dust: Amount,
    /// Challenge window after a Move (relative, `OP_CSV`).
    pub delta: u16,
    /// Extra delay on prover-favourable Splits.
    pub delta_prime: u16,
    /// Blocks of slack added when computing absolute deadlines (D2).
    pub deadline_margin: u32,
}

impl ChannelParams {
    pub fn regtest(funding_amount: Amount) -> ChannelParams {
        ChannelParams {
            funding_amount,
            to_self_delay: 6,
            commit_fee: Amount::from_sat(1_000),
            presign_fee: Amount::from_sat(1_000),
            dust: Amount::from_sat(330),
            delta: 6,
            delta_prime: 6,
            deadline_margin: 8,
        }
    }
    /// D2: how far ahead of the current height an off-chain deadline is set.
    pub fn deadline_offset(&self) -> u32 {
        u32::from(self.to_self_delay) + u32::from(self.delta) + self.deadline_margin
    }
}

/// A party's public keys as the counterparty sees them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PartyPubKeys {
    pub funding: XOnlyPublicKey,
    /// Signs every in-channel 2-of-2 leaf and claims `to_remote`.
    pub payment: XOnlyPublicKey,
    /// Claims the delayed `to_local`.
    pub delayed: XOnlyPublicKey,
    /// Where this party's sweeps and close payouts go.
    pub payout_spk: ScriptBuf,
}

/// A party's secret keys. Holds only its own material; built from its own seed.
pub struct PartyKeys {
    pub role: Role,
    seed: Seed,
    pub funding: Keypair,
    pub payment: Keypair,
    pub delayed: Keypair,
    pub payout: Keypair,
}

impl std::fmt::Debug for PartyKeys {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PartyKeys({})", self.role)
    }
}

impl PartyKeys {
    pub fn from_seed(role: Role, seed: Seed) -> PartyKeys {
        PartyKeys {
            role,
            funding: seed.keypair("funding"),
            payment: seed.keypair("payment"),
            delayed: seed.keypair("delayed"),
            payout: seed.keypair("payout"),
            seed,
        }
    }
    pub fn seed(&self) -> &Seed {
        &self.seed
    }
    pub fn payout_tree(&self) -> TapTree {
        payout_tree(&xonly(&self.payout))
    }
    pub fn public(&self) -> PartyPubKeys {
        PartyPubKeys {
            funding: xonly(&self.funding),
            payment: xonly(&self.payment),
            delayed: xonly(&self.delayed),
            payout_spk: self.payout_tree().script_pubkey(),
        }
    }
    /// Per-state revocation secret (revealed to the counterparty when the
    /// state is superseded).
    pub fn revocation_secret(&self, seq: u64) -> [u8; 32] {
        self.seed.derive_bytes(&format!("revocation/{seq}"))
    }
    pub fn revocation_hash(&self, seq: u64) -> Hash160 {
        hash160(&self.revocation_secret(seq))
    }
}

/// A single-leaf `<key> OP_CHECKSIG` taproot output: the PoC's "wallet".
pub fn payout_tree(key: &XOnlyPublicKey) -> TapTree {
    TapTree::new(vec![Leaf::new("claim", Builder::new().checksig(key).into_script(), Timelock::NONE)])
        .expect("one leaf")
}

/// The revocation leaf shared by every revocable output (to_local and all
/// contract outputs) of `broadcaster`'s commitment.
/// Script: `OP_HASH160 <rev_hash> OP_EQUALVERIFY <counterparty.payment> OP_CHECKSIG`.
/// Witness (consumption order): `revocation_secret, sig_counterparty`.
pub fn revoke_leaf(rev_hash: &Hash160, counterparty_payment: &XOnlyPublicKey) -> Leaf {
    Leaf::new(
        "revoke",
        Builder::new().hash160_verify(rev_hash).checksig(counterparty_payment).into_script(),
        Timelock::NONE,
    )
}

/// One contract output on a commitment transaction, as the channel sees it.
/// Implemented by `lngap-contract`; the channel only needs its value, its
/// taptree per commitment version and its pre-signed graph.
pub trait ContractOutput: Send + Sync + std::fmt::Debug {
    fn id(&self) -> u32;
    fn value(&self) -> Amount;
    /// The output's taptree on `ctx.broadcaster`'s commitment.
    fn tree(&self, ctx: &CommitCtx) -> Result<TapTree>;
    /// The pre-signed transactions hanging off this output at `outpoint`,
    /// unsigned. Labels must be unique within the output.
    fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>>;
}

/// Off-chain channel state `k`.
#[derive(Clone, Debug)]
pub struct ChannelState {
    pub seq: u64,
    pub balances: [Amount; 2],
    pub contracts: Vec<Arc<dyn ContractOutput>>,
}

impl ChannelState {
    pub fn balance(&self, r: Role) -> Amount {
        self.balances[r.idx()]
    }
    pub fn contracts_value(&self) -> Amount {
        self.contracts.iter().map(|c| c.value()).sum()
    }
    /// `bal_user + bal_hub + sum(V_i) == funding amount`.
    pub fn check_invariant(&self, funding_amount: Amount) -> Result<()> {
        let total = self.balances[0] + self.balances[1] + self.contracts_value();
        ensure!(total == funding_amount, "state {}: {} + {} + contracts {} != funding {}",
            self.seq, self.balances[0], self.balances[1], self.contracts_value(), funding_amount);
        let mut ids: Vec<u32> = self.contracts.iter().map(|c| c.id()).collect();
        ids.sort_unstable();
        ids.dedup();
        ensure!(ids.len() == self.contracts.len(), "duplicate contract ids");
        Ok(())
    }
    pub fn contract(&self, id: u32) -> Option<&Arc<dyn ContractOutput>> {
        self.contracts.iter().find(|c| c.id() == id)
    }
}
