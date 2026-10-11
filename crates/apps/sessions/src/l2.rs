//! A toy L2 of hub IOUs (V25_POC_PLAN.md, Phase 6): accounts of the hub's
//! tokens, hashlocked transfers (a session's activation), returns to the
//! hub with a memo (a withdrawal), and a single sequencer that seals
//! batches by signing the state's root. Validity and data availability
//! are the harness's: every operation is checked as it is submitted, and
//! anyone can read the state.

use std::collections::BTreeMap;

use anyhow::{bail, ensure, Context, Result};
use bitcoin::hashes::{hash160, Hash};
use bitcoin::key::Keypair;
use bitcoin::secp256k1::{schnorr, Message, SECP256K1};

/// The hub's account.
pub const HUB: &str = "hub";

/// A transfer locked under `HASH160(s)`: `to` receives it by revealing `s`.
#[derive(Clone, Debug)]
pub struct Lock {
    pub to: String,
    pub amount: u32,
    pub hash: [u8; 20],
    pub claimed: bool,
}

/// A return of `amount` to the hub, tagged `memo` (a session's identifier).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Return {
    pub amount: u32,
    pub memo: u32,
}

#[derive(Clone, Debug)]
pub enum Op {
    /// The hub issues tokens to itself.
    Mint { amount: u32 },
    /// The hub locks tokens to `to` under a hash.
    Lock { to: String, amount: u32, hash: [u8; 20] },
    /// `to` claims lock `id` with its preimage.
    Claim { id: usize, preimage: Vec<u8> },
    Transfer { from: String, to: String, amount: u32 },
    /// `from` returns tokens to the hub with a memo.
    Return { from: String, amount: u32, memo: u32 },
}

/// A sealed batch: the state's root after it, signed by the sequencer.
#[derive(Clone, Debug)]
pub struct Batch {
    pub height: u64,
    pub root: [u8; 32],
    pub sig: schnorr::Signature,
    /// The returns this batch made final.
    pub returns: Vec<Return>,
}

#[derive(Clone, Default)]
struct State {
    balances: BTreeMap<String, u32>,
    locks: Vec<Lock>,
}

impl State {
    fn take(&mut self, who: &str, amount: u32) -> Result<()> {
        let b = self.balances.entry(who.to_string()).or_default();
        ensure!(*b >= amount, "{who} holds {b}, not {amount}");
        *b -= amount;
        Ok(())
    }
    fn give(&mut self, who: &str, amount: u32) {
        *self.balances.entry(who.to_string()).or_default() += amount;
    }
    fn apply(&mut self, op: &Op) -> Result<Option<Return>> {
        match op {
            Op::Mint { amount } => self.give(HUB, *amount),
            Op::Lock { to, amount, hash } => {
                self.take(HUB, *amount)?;
                self.locks.push(Lock { to: to.clone(), amount: *amount, hash: *hash, claimed: false });
            }
            Op::Claim { id, preimage } => {
                let l = self.locks.get_mut(*id).context("no such lock")?;
                ensure!(!l.claimed, "lock {id} already claimed");
                ensure!(hash160::Hash::hash(preimage).to_byte_array() == l.hash, "wrong preimage for lock {id}");
                l.claimed = true;
                let (to, amount) = (l.to.clone(), l.amount);
                self.give(&to, amount);
            }
            Op::Transfer { from, to, amount } => {
                self.take(from, *amount)?;
                self.give(to, *amount);
            }
            Op::Return { from, amount, memo } => {
                if from == HUB {
                    bail!("the hub does not return to itself");
                }
                self.take(from, *amount)?;
                self.give(HUB, *amount);
                return Ok(Some(Return { amount: *amount, memo: *memo }));
            }
        }
        Ok(None)
    }
    /// A digest of the state (a stand-in for a Merkle root).
    fn root(&self, height: u64) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(&height.to_be_bytes());
        for (k, v) in &self.balances {
            h.update(k.as_bytes());
            h.update(&v.to_be_bytes());
        }
        for l in &self.locks {
            h.update(l.to.as_bytes());
            h.update(&l.amount.to_be_bytes());
            h.update(&l.hash);
            h.update(&[u8::from(l.claimed)]);
        }
        *h.finalize().as_bytes()
    }
}

pub struct L2 {
    sequencer: Keypair,
    state: State,
    pending: Vec<Op>,
    pending_returns: Vec<Return>,
    pub batches: Vec<Batch>,
}

impl L2 {
    pub fn new(sequencer: Keypair) -> L2 {
        L2 { sequencer, state: State::default(), pending: vec![], pending_returns: vec![], batches: vec![] }
    }
    pub fn sequencer_key(&self) -> bitcoin::XOnlyPublicKey {
        self.sequencer.x_only_public_key().0
    }
    /// Submit an operation; it is checked against the state now and made
    /// final by the next batch. Returns a lock's id for `Op::Lock`.
    pub fn submit(&mut self, op: Op) -> Result<usize> {
        if let Some(r) = self.state.apply(&op)? {
            self.pending_returns.push(r);
        }
        self.pending.push(op);
        Ok(self.state.locks.len().saturating_sub(1))
    }
    /// Seal the pending operations into a batch.
    pub fn seal(&mut self) -> Batch {
        let height = self.batches.len() as u64 + 1;
        let root = self.state.root(height);
        let sig = SECP256K1.sign_schnorr_no_aux_rand(&Message::from_digest(root), &self.sequencer);
        self.pending.clear();
        let b = Batch { height, root, sig, returns: std::mem::take(&mut self.pending_returns) };
        self.batches.push(b.clone());
        b
    }
    pub fn balance(&self, who: &str) -> u32 {
        self.state.balances.get(who).copied().unwrap_or(0)
    }
    /// The hub's check of a withdrawal: a return of `amount` with `memo`
    /// in a batch whose root carries the sequencer's signature.
    pub fn is_final_return(&self, amount: u32, memo: u32) -> bool {
        let key = self.sequencer_key();
        self.batches
            .iter()
            .any(|b| SECP256K1.verify_schnorr(&b.sig, &Message::from_digest(b.root), &key).is_ok() && b.returns.contains(&Return { amount, memo }))
    }
    /// Every final return, as the statement's table: `(b, c)`.
    pub fn final_returns(&self) -> Vec<(u32, u32)> {
        self.batches.iter().flat_map(|b| b.returns.iter().map(|r| (r.amount, r.memo))).collect()
    }
}
