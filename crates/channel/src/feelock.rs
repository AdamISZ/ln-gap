//! The fee lock (ATTESTATION_FEES.md; D49, D52): an HTLC-shaped channel
//! output paying the slot's proposer iff the venue attests exactly the
//! payer's head.
//!
//! The payer offers `value` to the counterparty (the payee: the proposer's
//! node — the hub in the PoC) locked to a point `T = ΣP`, the sum of the
//! anticipation points the payer's head selects under the slot's table
//! (`lngap_pos::fee::lock_point`). Its discrete log `Σs` exists only once
//! the scheduled member has attested exactly that head, and is public
//! thereafter (`lngap_pos::fee::lock_secret`).
//!
//! The output's tree on either commitment:
//!
//! - `revoke`: the standard revocation leaf;
//! - `claim`: 2-of-2, pre-signed to the payee's payout — the PAYER's half
//!   an adaptor pre-signature under `T` ([`PresignedTx::with_adaptor`]),
//!   so the payee can broadcast it only by completing with `Σs`, and the
//!   completed signature hands `Σs` to the payer (D49's extract);
//! - `timeout`: after `expiry` (CLTV), the payer's key alone.
//!
//! Cooperatively nothing touches Bitcoin: the payee, holding `Σs`,
//! proposes the settled state ([`FeeLock::settled`]) and the payer accepts
//! it iff the secret it was handed opens the lock
//! ([`FeeLock::accept_settlement`]) — Lightning's update_fulfill with the
//! secret delivered out of band. The payer's refund after `expiry` is the
//! symmetric update ([`FeeLock::refunded`]) or the on-chain sweep.
//!
//! [`PresignedTx::with_adaptor`]: crate::presign::PresignedTx::with_adaptor

use std::sync::Arc;

use anyhow::{anyhow, ensure, Result};
use bitcoin::script::Builder;
use bitcoin::secp256k1::{PublicKey, SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, TxOut};
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};

use crate::{ChannelState, CommitCtx, ContractOutput, PresignedTx, Role};

#[derive(Clone, Debug)]
pub struct FeeLock {
    pub id: u32,
    pub payer: Role,
    pub value: Amount,
    /// The adaptor point `ΣP`.
    pub lock: PublicKey,
    /// The Bitcoin height from which the payer may take the value back.
    pub expiry: u32,
    /// For the log: what the lock pays for (the slot, the head).
    pub memo: String,
}

impl FeeLock {
    pub fn payee(&self) -> Role {
        self.payer.other()
    }

    /// Does `t` open the lock (`t·G == ΣP`)?
    pub fn opens(&self, t: &SecretKey) -> bool {
        PublicKey::from_secret_key(SECP256K1, t) == self.lock
    }

    /// The fee lock `id` in `state`, if any.
    pub fn find(state: &ChannelState, id: u32) -> Option<&FeeLock> {
        state.contract(id).and_then(|c| c.as_any().downcast_ref::<FeeLock>())
    }

    /// The next state with this lock removed and `value` moved to `to`.
    fn resolved(&self, state: &ChannelState, to: Role) -> ChannelState {
        let mut st = state.clone();
        st.seq += 1;
        st.contracts.retain(|c| c.id() != self.id);
        st.balances[to.idx()] += self.value;
        st
    }

    /// The settled state: the payee paid (proposed by the payee holding
    /// `Σs`).
    pub fn settled(&self, state: &ChannelState) -> ChannelState {
        self.resolved(state, self.payee())
    }

    /// The refunded state: the payer repaid (proposed cooperatively after
    /// `expiry`, or when both agree the attestation will not come).
    pub fn refunded(&self, state: &ChannelState) -> ChannelState {
        self.resolved(state, self.payer)
    }

    /// The state with this lock added, `value` taken from the payer's
    /// balance.
    pub fn offered(self, state: &ChannelState) -> Result<ChannelState> {
        let mut st = state.clone();
        st.seq += 1;
        ensure!(st.balances[self.payer.idx()] >= self.value, "the payer cannot fund the lock");
        st.balances[self.payer.idx()] -= self.value;
        ensure!(st.contract(self.id).is_none(), "contract {} exists", self.id);
        st.contracts.push(Arc::new(self));
        Ok(st)
    }

    /// The payer's rule for a settlement of lock `id` proposed by the
    /// payee: `new` is exactly `old` with the lock removed and `value`
    /// moved to the payee, and `secret` opens the lock.
    pub fn accept_settlement(old: &ChannelState, new: &ChannelState, id: u32, secret: Option<&SecretKey>) -> Result<()> {
        let lock = FeeLock::find(old, id).ok_or_else(|| anyhow!("no fee lock {id} in the old state"))?;
        let t = secret.ok_or_else(|| anyhow!("fee lock {id}: no secret was delivered"))?;
        ensure!(lock.opens(t), "fee lock {id}: the delivered secret does not open the lock");
        let want = lock.settled(old);
        ensure!(new.seq == want.seq && new.balances == want.balances, "fee lock {id}: the settlement moves the wrong amount");
        let mut a: Vec<u32> = new.contracts.iter().map(|c| c.id()).collect();
        let mut b: Vec<u32> = want.contracts.iter().map(|c| c.id()).collect();
        a.sort_unstable();
        b.sort_unstable();
        ensure!(a == b, "fee lock {id}: the settlement changes other contracts");
        Ok(())
    }

    fn claim_leaf(&self, ctx: &CommitCtx) -> Leaf {
        let mut b = Builder::new();
        let mut tl = Timelock::NONE;
        if self.payee() == ctx.broadcaster && ctx.params.to_self_delay > 0 {
            b = b.csv(ctx.params.to_self_delay);
            tl.csv = Some(ctx.params.to_self_delay);
        }
        Leaf::new("claim", ctx.two_of_two(b).into_script(), tl)
    }

    fn timeout_leaf(&self, ctx: &CommitCtx) -> Leaf {
        let mut b = Builder::new().cltv(self.expiry);
        let mut tl = Timelock::cltv(self.expiry);
        if self.payer == ctx.broadcaster && ctx.params.to_self_delay > 0 {
            b = b.csv(ctx.params.to_self_delay);
            tl.csv = Some(ctx.params.to_self_delay);
        }
        Leaf::new("timeout", b.checksig(&ctx.key(self.payer).payment).into_script(), tl)
    }
}

impl ContractOutput for FeeLock {
    fn id(&self) -> u32 {
        self.id
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn value(&self) -> Amount {
        self.value
    }
    fn tree(&self, ctx: &CommitCtx) -> Result<TapTree> {
        TapTree::new(vec![ctx.revoke_leaf(), self.claim_leaf(ctx), self.timeout_leaf(ctx)])
    }
    /// One pre-signed transaction: `claim`, to the payee's payout, the
    /// payer's half an adaptor pre-signature under the lock.
    fn graph(&self, ctx: &CommitCtx, outpoint: OutPoint, prevout: &TxOut) -> Result<Vec<PresignedTx>> {
        let tree = self.tree(ctx)?;
        let leaf = tree.leaf("claim")?;
        let tx = build_spend(outpoint, &leaf.timelock, vec![TxOut { value: prevout.value - ctx.params.presign_fee, script_pubkey: ctx.key(self.payee()).payout_spk.clone() }]);
        let p = PresignedTx::new("claim", tx, vec![prevout.clone()], &tree, "claim", format!("fee claim: {}", self.memo))?.with_adaptor(self.payer, self.lock);
        Ok(vec![p])
    }
}
