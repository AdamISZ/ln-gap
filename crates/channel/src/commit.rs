//! Commitment transactions: one version per party, per state.

use anyhow::{ensure, Result};
use bitcoin::script::Builder;
use bitcoin::{Amount, OutPoint, Sequence, Transaction, TxOut};
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_tx, Timelock};
use lngap_btc::Hash160;

use crate::{revoke_leaf, ChannelParams, ChannelState, PartyPubKeys, Role};

/// Everything a contract needs to know to build its output on one commitment.
#[derive(Clone, Debug)]
pub struct CommitCtx<'a> {
    pub params: &'a ChannelParams,
    pub keys: &'a [PartyPubKeys; 2],
    /// Whose version of the commitment this is (they broadcast it).
    pub broadcaster: Role,
    pub seq: u64,
    /// The broadcaster's revocation hash for this state.
    pub rev_hash: Hash160,
}

impl<'a> CommitCtx<'a> {
    pub fn key(&self, r: Role) -> &PartyPubKeys {
        &self.keys[r.idx()]
    }
    /// The revocation leaf every revocable output of this commitment carries.
    pub fn revoke_leaf(&self) -> Leaf {
        revoke_leaf(&self.rev_hash, &self.key(self.broadcaster.other()).payment)
    }
    /// The 2-of-2 fragment used on every pre-signed path: user first, hub second.
    pub fn two_of_two(&self, b: Builder) -> Builder {
        b.two_of_two(&self.keys[0].payment, &self.keys[1].payment)
    }
    pub fn two_of_two_verify(&self, b: Builder) -> Builder {
        b.two_of_two_verify(&self.keys[0].payment, &self.keys[1].payment)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputKind {
    /// The broadcaster's delayed, revocable balance.
    ToLocal,
    /// The counterparty's balance, claimable immediately.
    ToRemote,
    Contract(u32),
}

#[derive(Clone, Debug)]
pub struct CommitOutput {
    pub kind: OutputKind,
    pub vout: u32,
    pub value: Amount,
    pub tree: TapTree,
}

/// A built commitment transaction (unsigned) with its output descriptions.
#[derive(Clone, Debug)]
pub struct Commitment {
    pub broadcaster: Role,
    pub seq: u64,
    pub tx: Transaction,
    pub funding_prevout: TxOut,
    pub outputs: Vec<CommitOutput>,
}

impl Commitment {
    pub fn txid(&self) -> bitcoin::Txid {
        self.tx.compute_txid()
    }
    pub fn output(&self, kind: OutputKind) -> Option<&CommitOutput> {
        self.outputs.iter().find(|o| o.kind == kind)
    }
    pub fn outpoint(&self, o: &CommitOutput) -> OutPoint {
        OutPoint { txid: self.txid(), vout: o.vout }
    }
    pub fn txout(&self, o: &CommitOutput) -> TxOut {
        self.tx.output[o.vout as usize].clone()
    }
}

/// `to_local` tree for `ctx.broadcaster`: revocable by the counterparty,
/// claimable by the broadcaster after `to_self_delay`.
pub fn to_local_tree(ctx: &CommitCtx) -> Result<TapTree> {
    let me = ctx.key(ctx.broadcaster);
    TapTree::new(vec![
        ctx.revoke_leaf(),
        Leaf::new(
            "delayed",
            Builder::new().csv(ctx.params.to_self_delay).checksig(&me.delayed).into_script(),
            Timelock::csv(ctx.params.to_self_delay),
        ),
    ])
}

/// `to_remote` tree: the counterparty claims with its payment key, no delay.
pub fn to_remote_tree(ctx: &CommitCtx) -> Result<TapTree> {
    let them = ctx.key(ctx.broadcaster.other());
    TapTree::new(vec![Leaf::new("claim", Builder::new().checksig(&them.payment).into_script(), Timelock::NONE)])
}

/// Build `ctx.broadcaster`'s commitment for `state`. Fee comes out of the
/// broadcaster's balance. Output order: to_local, to_remote, contracts by id.
pub fn build_commitment(state: &ChannelState, ctx: &CommitCtx, funding: (OutPoint, TxOut)) -> Result<Commitment> {
    state.check_invariant(ctx.params.funding_amount)?;
    ensure!(state.seq == ctx.seq, "state seq {} != ctx seq {}", state.seq, ctx.seq);
    let me = ctx.broadcaster;
    let bal_me = state.balance(me);
    ensure!(bal_me >= ctx.params.commit_fee, "{me}'s balance cannot cover the commitment fee");
    let mut outputs = Vec::new();
    let mut txouts = Vec::new();
    let mut push = |kind: OutputKind, value: Amount, tree: TapTree, txouts: &mut Vec<TxOut>| {
        if value < ctx.params.dust {
            return;
        }
        txouts.push(TxOut { value, script_pubkey: tree.script_pubkey() });
        outputs.push(CommitOutput { kind, vout: (txouts.len() - 1) as u32, value, tree });
    };
    push(OutputKind::ToLocal, bal_me - ctx.params.commit_fee, to_local_tree(ctx)?, &mut txouts);
    push(OutputKind::ToRemote, state.balance(me.other()), to_remote_tree(ctx)?, &mut txouts);
    let mut contracts: Vec<_> = state.contracts.iter().collect();
    contracts.sort_by_key(|c| c.id());
    for c in contracts {
        push(OutputKind::Contract(c.id()), c.value(), c.tree(ctx)?, &mut txouts);
    }
    let tx = build_tx(&[(funding.0, Sequence::ENABLE_RBF_NO_LOCKTIME)], txouts, bitcoin::absolute::LockTime::ZERO);
    Ok(Commitment { broadcaster: me, seq: state.seq, tx, funding_prevout: funding.1, outputs })
}
