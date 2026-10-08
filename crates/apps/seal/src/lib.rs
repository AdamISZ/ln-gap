//! LN-GAP 2.5: a venue member's seal chain and its connector trees
//! (V25_POC_PLAN.md, Phases 1 and 2).
//!
//! A member locks its bond in a chain of SEAL OUTPUTS `S_1 .. S_n`, one per
//! period of a term, and a final output `S_{n+1}`. The k-th SEAL CLOSING
//! spends `S_k` into `S_{k+1}` from height `H_k` on, and carries in its
//! witness a one-time (Winternitz) signature of the member's 20-byte root
//! for period k, or, for an idle period, the preimage `z_k` of a committed
//! hash. Every closing also creates a CONNECTOR `κ_k` and an anchor output
//! for fee bumping.
//!
//! The connector unfolds through a pinned binary SPLIT TREE into `Q` leaf
//! connectors `ℓ_{k,s}`, each hash-locked to a preimage the member hands to
//! the mover of one (contract, depth) it serves. A contract pre-signs its
//! rebuttal through this member to spend that leaf as a second input; the
//! leaf can exist only if closing k confirmed, so the rebuttal proves it.
//! A dispute broadcasts only the splits on its own leaf's path; every other
//! leaf stays reachable through the siblings those splits create.
//!
//! Heights are "mineable from": a leaf that opens at height `X` carries
//! `CLTV X - 1` (a transaction is final in a block of height greater than
//! its nLockTime), so its spend can be in block `X` and not before.
//!
//! Each seal output `S_k`'s leaves:
//! - `close`: ceremony key, member key, WOTS verify of the root;
//! - `close_empty`: ceremony key, member key, the empty-period preimage
//!   (the same pre-signed transaction as `close`: only the witness differs,
//!   so the connector's outpoint is the same either way);
//! - `burn`: after `H_k + grace`, the ceremony-signed burn, whose only
//!   output is a zero-value OP_RETURN: the whole bond goes to fees, so any
//!   miner prefers it to a late closing, and nobody can redirect it.
//!
//! The final output carries `reclaim` (member key, after `release`) and,
//! per period j, `slash_{j}`: two different roots under period j's key,
//! after `race_from`, in a ceremony-signed transaction paying everything to
//! fees. (At `race_from` the bond is in the final output or already burned,
//! so the slash leaves live only there.)
//!
//! PINNING: Bitcoin has no covenants, so the closings, burns, slashes and
//! splits are fixed by a pre-signing CEREMONY whose keys are then deleted
//! (one honest deleter suffices). The ceremony is independent of any
//! contract: roots and preimages go in witnesses, which no signature
//! covers. Here the ceremony is a single toy party (`ceremony`), whose
//! secrets go out of scope when it returns.

pub mod dating;
pub mod world;

use anyhow::{anyhow, ensure, Result};
use bitcoin::hashes::{sha256, Hash};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_btc::{hash160, Hash160};
use lngap_lamport::winternitz::{WotsExt, WotsParams, WotsPublic, WotsSecret, WotsSig};

/// A period root is 20 bytes (a BLAKE3-160 Merkle root in later phases).
pub const ROOT_BYTES: u32 = 20;

/// The OP_RETURN payload of burns and slashes (a few bytes, so the
/// transaction is not under Core's 65-byte minimum).
pub const BURN_TAG: &[u8; 15] = b"lngap-seal-burn";

/// The Winternitz parameters of a root key: 40 message digits, 3 checksum.
pub fn root_params() -> WotsParams {
    WotsParams::for_bytes(ROOT_BYTES)
}

/// The seal chain's parameters, fixed before the ceremony.
#[derive(Clone, Debug)]
pub struct SealSpec {
    /// The bond, locked in `S_1`.
    pub value: Amount,
    /// `H_1`, the first closing height.
    pub start: u32,
    /// Blocks between closings.
    pub period: u32,
    /// The number of periods `n` in the term.
    pub periods: u32,
    /// Blocks after `H_k` within which closing k must confirm; the burn
    /// opens at `H_k + grace`.
    pub grace: u32,
    /// Blocks after `race_from` before the member may reclaim the bond.
    pub release_delay: u32,
    /// The connector tree's depth: `Q = 2^fanout_depth` leaves per closing.
    pub fanout_depth: u32,
    /// The value of each leaf connector.
    pub leaf_value: Amount,
    /// The fixed fee of each pre-signed split.
    pub split_fee: Amount,
    /// The value of each anchor output (closings and splits).
    pub anchor_value: Amount,
    /// The fixed fee of each pre-signed closing.
    pub closing_fee: Amount,
}

impl SealSpec {
    /// `Q`, the leaf connectors per closing.
    pub fn leaves(&self) -> u32 {
        1 << self.fanout_depth
    }
    /// `H_k`: closing k (1-based) is valid from this height.
    pub fn height(&self, k: u32) -> u32 {
        self.start + (k - 1) * self.period
    }
    /// The height from which `S_k` can be burned.
    pub fn burn_from(&self, k: u32) -> u32 {
        self.height(k) + self.grace
    }
    /// The slash leaves open here: after the term's last burn height.
    pub fn race_from(&self) -> u32 {
        self.burn_from(self.periods) + 1
    }
    /// The member's reclaim of the final output opens here.
    pub fn release(&self) -> u32 {
        self.race_from() + self.release_delay
    }
    /// The value of a connector-tree node at depth `t` (the root `κ_k` at
    /// 0, the leaves at `fanout_depth`): its leaves, plus the fee and
    /// anchor of every split below it.
    pub fn node_value(&self, t: u32) -> Amount {
        let below = 1u64 << (self.fanout_depth - t);
        self.leaf_value * below + (self.split_fee + self.anchor_value) * (below - 1)
    }
    /// The value of each closing's connector `κ_k`.
    pub fn connector_value(&self) -> Amount {
        self.node_value(0)
    }
    /// The value of `S_k` (k = 1..=n+1).
    pub fn output_value(&self, k: u32) -> Amount {
        let per = self.connector_value() + self.anchor_value + self.closing_fee;
        self.value - per * u64::from(k - 1)
    }
    fn check(&self) -> Result<()> {
        ensure!(self.periods >= 1 && self.period >= 1, "a term needs at least one period of at least one block");
        ensure!(self.start >= 2, "H_1 must be at least 2");
        ensure!(self.grace >= 1, "the grace must be at least one block");
        ensure!(self.grace < self.period, "the grace must end before the next period's closing");
        ensure!(self.fanout_depth <= 16, "a connector tree of more than 2^16 leaves is out of scope");
        ensure!(
            self.output_value(self.periods + 1) > Amount::from_sat(1_000),
            "the bond does not cover the term's connectors, anchors and fees"
        );
        Ok(())
    }
}

fn derive(seed: &[u8; 32], tag: &str, k: u32, s: u32) -> [u8; 32] {
    let mut data = seed.to_vec();
    data.extend_from_slice(tag.as_bytes());
    data.extend_from_slice(&k.to_be_bytes());
    data.extend_from_slice(&s.to_be_bytes());
    sha256::Hash::hash(&data).to_byte_array()
}

fn keypair(secret: [u8; 32]) -> Keypair {
    Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&secret).expect("a hash is a valid secret key"))
}

/// A member's secrets: its key, and per period a root key, an empty-period
/// preimage and `Q` leaf-connector preimages, all derived from one seed.
pub struct Member {
    key: Keypair,
    seed: [u8; 32],
    periods: u32,
    leaves: u32,
}

/// What a member publishes before the ceremony.
#[derive(Clone, Debug)]
pub struct MemberPublic {
    pub key: XOnlyPublicKey,
    /// `K^root_k`, k = 1..=n (index k - 1).
    pub roots: Vec<WotsPublic>,
    /// `HASH160(z_k)`, k = 1..=n (index k - 1).
    pub empties: Vec<Hash160>,
    /// `HASH160(e_{k,s})`: per period (index k - 1), per leaf s.
    pub leaf_locks: Vec<Vec<Hash160>>,
}

impl Member {
    pub fn new(seed: [u8; 32], spec: &SealSpec) -> Member {
        Member { key: keypair(derive(&seed, "member-key", 0, 0)), seed, periods: spec.periods, leaves: spec.leaves() }
    }
    fn root_secret(&self, k: u32) -> WotsSecret {
        WotsSecret::from_entropy(root_params(), derive(&self.seed, "root", k, 0))
    }
    /// The empty-period preimage `z_k`.
    pub fn empty_preimage(&self, k: u32) -> [u8; 32] {
        derive(&self.seed, "empty", k, 0)
    }
    /// The preimage `e_{k,s}` of leaf connector s of closing k: handed at
    /// registration to the mover of the (contract, depth) assigned to it.
    pub fn leaf_preimage(&self, k: u32, s: u32) -> [u8; 32] {
        derive(&self.seed, "leaf", k, s)
    }
    /// The member's one-time signature of a root for period k. Signing two
    /// different roots for one period is the slashable fault.
    pub fn sign_root(&self, k: u32, root: &[u8; 20]) -> Result<WotsSig> {
        ensure!((1..=self.periods).contains(&k), "period {k} is outside the term");
        self.root_secret(k).sign(root)
    }
    pub fn keypair(&self) -> &Keypair {
        &self.key
    }
    pub fn public(&self) -> MemberPublic {
        MemberPublic {
            key: self.key.x_only_public_key().0,
            roots: (1..=self.periods).map(|k| self.root_secret(k).public()).collect(),
            empties: (1..=self.periods).map(|k| hash160(&self.empty_preimage(k))).collect(),
            leaf_locks: (1..=self.periods)
                .map(|k| (0..self.leaves).map(|s| hash160(&self.leaf_preimage(k, s))).collect())
                .collect(),
        }
    }
}

/// A Winternitz signature's witness elements in wire order (bottom of the
/// stack first): ascending digits, the hash element before the digit.
pub fn wots_wire(sig: &WotsSig) -> Vec<Vec<u8>> {
    let mut w = Vec::with_capacity(2 * sig.digits.len());
    for (h, d) in sig.hashes.iter().zip(&sig.digits) {
        w.push(h.to_vec());
        w.push(if *d == 0 { vec![] } else { vec![*d] });
    }
    w
}

fn drop_digits(mut b: Builder, n: usize) -> Builder {
    for _ in 0..n / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    if n % 2 == 1 {
        b = b.push_opcode(OP_DROP);
    }
    b
}

/// `close` for period k: the pinned closing, carrying the root.
pub fn close_leaf(spec: &SealSpec, ceremony: &XOnlyPublicKey, member: &MemberPublic, k: u32) -> Leaf {
    let lock = spec.height(k) - 1;
    let key = &member.roots[(k - 1) as usize];
    let b = Builder::new()
        .cltv(lock)
        .checksigverify(ceremony)
        .checksigverify(&member.key)
        .wots_verify(key);
    let b = drop_digits(b, key.params.message_digits as usize);
    Leaf::new("close", b.push_int(1).into_script(), Timelock::cltv(lock))
}

/// `close_empty` for period k: the same pinned closing, for an idle period.
pub fn close_empty_leaf(spec: &SealSpec, ceremony: &XOnlyPublicKey, member: &MemberPublic, k: u32) -> Leaf {
    let lock = spec.height(k) - 1;
    let b = Builder::new()
        .cltv(lock)
        .checksigverify(ceremony)
        .checksigverify(&member.key)
        .push_opcode(OP_HASH160)
        .push_bytes(&member.empties[(k - 1) as usize])
        .push_opcode(OP_EQUAL);
    Leaf::new("close_empty", b.into_script(), Timelock::cltv(lock))
}

/// `burn` for period k: the ceremony-signed burn, once the grace has
/// passed. The signature is public, so anyone can broadcast it; its
/// outputs are fixed, so nobody can redirect it.
pub fn burn_leaf(spec: &SealSpec, ceremony: &XOnlyPublicKey, k: u32) -> Leaf {
    let lock = spec.burn_from(k) - 1;
    Leaf::new("burn", Builder::new().cltv(lock).checksig(ceremony).into_script(), Timelock::cltv(lock))
}

/// `slash_{j}` on the final output: the ceremony-signed slash, with two
/// valid root signatures under period j's key over DIFFERENT roots in the
/// witness (the choreography of the v1 `equiv` leaf: verify the top block,
/// park its digits, verify the block below, restore, compare).
pub fn slash_leaf(spec: &SealSpec, ceremony: &XOnlyPublicKey, member: &MemberPublic, j: u32) -> Leaf {
    let lock = spec.race_from() - 1;
    let key = &member.roots[(j - 1) as usize];
    let m = key.params.message_digits as usize;
    let mut b = Builder::new().cltv(lock).checksigverify(ceremony).wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    b = b.push_int(0);
    for i in 0..m {
        b = b
            .push_int((m - i) as i64)
            .push_opcode(OP_PICK)
            .push_int((2 * m - i + 1) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SUB)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_ADD);
    }
    b = b.push_opcode(OP_VERIFY);
    b = drop_digits(b, 2 * m);
    Leaf::new(format!("slash_{j}"), b.push_int(1).into_script(), Timelock::cltv(lock))
}

/// `reclaim` on the final output: the member, after `release`.
pub fn reclaim_leaf(spec: &SealSpec, member: &MemberPublic) -> Leaf {
    let lock = spec.release() - 1;
    Leaf::new("reclaim", Builder::new().cltv(lock).checksig(&member.key).into_script(), Timelock::cltv(lock))
}

/// The tree of seal output `S_k`, k = 1..=n.
pub fn seal_tree(spec: &SealSpec, ceremony: &XOnlyPublicKey, member: &MemberPublic, k: u32) -> Result<TapTree> {
    TapTree::new(vec![
        close_leaf(spec, ceremony, member, k),
        close_empty_leaf(spec, ceremony, member, k),
        burn_leaf(spec, ceremony, k),
    ])
}

/// The tree of the final output `S_{n+1}`.
pub fn final_tree(spec: &SealSpec, slash_key: &XOnlyPublicKey, member: &MemberPublic) -> Result<TapTree> {
    let mut leaves = vec![reclaim_leaf(spec, member)];
    leaves.extend((1..=spec.periods).map(|j| slash_leaf(spec, slash_key, member, j)));
    TapTree::new(leaves)
}

/// An internal node of a connector tree (the root `κ_k` included):
/// spendable only by its pinned split, under the period's split key.
pub fn node_tree(split_key: &XOnlyPublicKey) -> Result<TapTree> {
    TapTree::new(vec![Leaf::new("split", Builder::new().checksig(split_key).into_script(), Timelock::NONE)])
}

/// A leaf connector `ℓ_{k,s}`: anyone holding the preimage `e_{k,s}`.
pub fn leaf_tree(lock: &Hash160) -> Result<TapTree> {
    TapTree::new(vec![Leaf::new(
        "use",
        Builder::new().push_opcode(OP_HASH160).push_bytes(lock).push_opcode(OP_EQUAL).into_script(),
        Timelock::NONE,
    )])
}

/// Pay-to-anchor (`OP_1 <0x4e73>`): anyone may spend it to bump the
/// transaction that created it, by CPFP.
pub fn anchor_spk() -> ScriptBuf {
    ScriptBuf::from_bytes(vec![0x51, 0x02, 0x4e, 0x73])
}

fn burn_output() -> TxOut {
    TxOut { value: Amount::ZERO, script_pubkey: ScriptBuf::new_op_return(BURN_TAG) }
}

/// A pre-signed transaction with one ceremony signature (a split, a burn,
/// a slash).
#[derive(Clone, Debug)]
pub struct Signed {
    /// The transaction, without witness.
    pub tx: Transaction,
    /// The output it spends.
    pub prevout: TxOut,
    /// The ceremony's signature.
    pub sig: Vec<u8>,
}

/// One period's pre-signed transactions.
#[derive(Clone, Debug)]
pub struct ClosingTemplate {
    pub k: u32,
    /// The closing, without witness.
    pub tx: Transaction,
    /// `S_k`, the output it spends.
    pub prevout: TxOut,
    pub tree: TapTree,
    /// The ceremony's signatures under `Q_k`, one per closing leaf.
    pub sig_close: Vec<u8>,
    pub sig_empty: Vec<u8>,
    /// The burn of `S_k`.
    pub burn: Signed,
    /// The period's split key `C_k` (public): every internal node of the
    /// connector tree, `κ_k` included, is `<C_k> CHECKSIG`.
    pub split_key: XOnlyPublicKey,
    /// The connector tree's splits in heap order: index `n - 1` splits
    /// node `n` (node 1 is `κ_k`; nodes `Q..2Q-1` are the leaves).
    pub splits: Vec<Signed>,
}

/// The ceremony's output: the whole term pre-signed.
#[derive(Clone, Debug)]
pub struct PresignedChain {
    pub spec: SealSpec,
    pub member: MemberPublic,
    pub funding: OutPoint,
    pub closings: Vec<ClosingTemplate>,
    pub final_tree: TapTree,
    /// The slash of the final output for period j (index j - 1).
    pub slashes: Vec<Signed>,
}

fn ceremony_keys(seed: &[u8; 32], n: u32) -> (Vec<Keypair>, Vec<Keypair>, Keypair) {
    let qs = (1..=n).map(|k| keypair(derive(seed, "Q", k, 0))).collect();
    let cs = (1..=n).map(|k| keypair(derive(seed, "split", k, 0))).collect();
    (qs, cs, keypair(derive(seed, "slash", 0, 0)))
}

/// The tree of `S_1` (to fund it before the ceremony signs): the toy
/// ceremony derives its keys from its seed.
pub fn first_tree(spec: &SealSpec, member: &MemberPublic, ceremony_seed: &[u8; 32]) -> Result<TapTree> {
    let (qs, _, _) = ceremony_keys(ceremony_seed, 1);
    seal_tree(spec, &qs[0].x_only_public_key().0, member, 1)
}

fn sign(kp: &Keypair, tx: &Transaction, prevout: &TxOut, leaf: &ScriptBuf) -> Result<Vec<u8>> {
    Ok(sign_tapscript(kp, tx, 0, std::slice::from_ref(prevout), leaf)?.as_ref().to_vec())
}

/// The pre-signed splits of one closing's connector tree, rooted at
/// `kappa` (the closing's output 1).
fn connector_splits(spec: &SealSpec, split: &Keypair, locks: &[Hash160], kappa: OutPoint) -> Result<Vec<Signed>> {
    let q = spec.leaves();
    let node = node_tree(&split.x_only_public_key().0)?;
    let split_leaf = node.leaf("split")?.script.clone();
    // node n's output (its outpoint and TxOut), filled parent-first
    let mut out: Vec<Option<(OutPoint, TxOut)>> = vec![None; (2 * q) as usize];
    out[1] = Some((kappa, TxOut { value: spec.node_value(0), script_pubkey: node.script_pubkey() }));
    let mut splits = Vec::with_capacity((q - 1) as usize);
    for n in 1..q {
        let (op, prevout) = out[n as usize].clone().expect("parents come first in heap order");
        let t = 32 - n.leading_zeros(); // the children's depth: floor(log2 n) + 1
        let child = |c: u32| -> Result<TxOut> {
            let spk = if c < q { node.script_pubkey() } else { leaf_tree(&locks[(c - q) as usize])?.script_pubkey() };
            Ok(TxOut { value: spec.node_value(t), script_pubkey: spk })
        };
        let outputs = vec![child(2 * n)?, child(2 * n + 1)?, TxOut { value: spec.anchor_value, script_pubkey: anchor_spk() }];
        let tx = build_spend(op, &Timelock::NONE, outputs);
        let txid = tx.compute_txid();
        out[(2 * n) as usize] = Some((OutPoint { txid, vout: 0 }, tx.output[0].clone()));
        out[(2 * n + 1) as usize] = Some((OutPoint { txid, vout: 1 }, tx.output[1].clone()));
        let sig = sign(split, &tx, &prevout, &split_leaf)?;
        splits.push(Signed { tx, prevout, sig });
    }
    Ok(splits)
}

/// The toy ceremony: derive its keys, build every transaction of the term
/// (closings, burns, connector splits, slashes) and pre-sign them. The
/// secrets are dropped when this returns.
pub fn ceremony(spec: &SealSpec, member: &MemberPublic, funding: OutPoint, ceremony_seed: &[u8; 32]) -> Result<PresignedChain> {
    spec.check()?;
    let n = spec.periods;
    ensure!(member.roots.len() == n as usize, "the member's keys must cover the term");
    ensure!(
        member.leaf_locks.iter().all(|l| l.len() == spec.leaves() as usize),
        "the member's leaf locks must cover every connector leaf"
    );
    let (qs, cs, slash_key) = ceremony_keys(ceremony_seed, n);
    let trees: Vec<TapTree> = (1..=n)
        .map(|k| seal_tree(spec, &qs[(k - 1) as usize].x_only_public_key().0, member, k))
        .collect::<Result<_>>()?;
    let final_tree = final_tree(spec, &slash_key.x_only_public_key().0, member)?;
    let mut prev = funding;
    let mut prevout = TxOut { value: spec.value, script_pubkey: trees[0].script_pubkey() };
    let mut closings = Vec::with_capacity(n as usize);
    for k in 1..=n {
        let i = (k - 1) as usize;
        let next_spk = if k < n { trees[i + 1].script_pubkey() } else { final_tree.script_pubkey() };
        let outputs = vec![
            TxOut { value: spec.output_value(k + 1), script_pubkey: next_spk },
            TxOut {
                value: spec.connector_value(),
                script_pubkey: node_tree(&cs[i].x_only_public_key().0)?.script_pubkey(),
            },
            TxOut { value: spec.anchor_value, script_pubkey: anchor_spk() },
        ];
        let close = trees[i].leaf("close")?;
        let empty = trees[i].leaf("close_empty")?;
        ensure!(close.timelock == empty.timelock, "both closing leaves share the closing's locktime");
        let tx = build_spend(prev, &close.timelock, outputs);
        let sig_close = sign(&qs[i], &tx, &prevout, &close.script)?;
        let sig_empty = sign(&qs[i], &tx, &prevout, &empty.script)?;
        let burn_leaf = trees[i].leaf("burn")?;
        let burn_tx = build_spend(prev, &burn_leaf.timelock, vec![burn_output()]);
        let burn = Signed { sig: sign(&qs[i], &burn_tx, &prevout, &burn_leaf.script)?, tx: burn_tx, prevout: prevout.clone() };
        let txid = tx.compute_txid();
        let splits = connector_splits(spec, &cs[i], &member.leaf_locks[i], OutPoint { txid, vout: 1 })?;
        let next_out = tx.output[0].clone();
        let split_key = cs[i].x_only_public_key().0;
        closings.push(ClosingTemplate { k, tx, prevout, tree: trees[i].clone(), sig_close, sig_empty, burn, split_key, splits });
        prev = OutPoint { txid, vout: 0 };
        prevout = next_out;
    }
    // the slashes of the final output, one per period
    let slashes = (1..=n)
        .map(|j| {
            let leaf = final_tree.leaf(&format!("slash_{j}"))?;
            let tx = build_spend(prev, &leaf.timelock, vec![burn_output()]);
            Ok(Signed { sig: sign(&slash_key, &tx, &prevout, &leaf.script)?, tx, prevout: prevout.clone() })
        })
        .collect::<Result<_>>()?;
    Ok(PresignedChain { spec: spec.clone(), member: member.clone(), funding, closings, final_tree, slashes })
}

impl PresignedChain {
    fn template(&self, k: u32) -> Result<&ClosingTemplate> {
        self.closings
            .get((k as usize).wrapping_sub(1))
            .ok_or_else(|| anyhow!("period {k} is outside the term"))
    }
    /// The outpoint of `S_k`, k = 1..=n+1.
    pub fn seal_outpoint(&self, k: u32) -> Result<OutPoint> {
        if k == 1 {
            return Ok(self.funding);
        }
        Ok(OutPoint { txid: self.template(k - 1)?.tx.compute_txid(), vout: 0 })
    }
    /// The output `S_k` itself, k = 1..=n+1.
    pub fn seal_txout(&self, k: u32) -> Result<TxOut> {
        if k == self.spec.periods + 1 {
            return Ok(self.template(k - 1)?.tx.output[0].clone());
        }
        Ok(self.template(k)?.prevout.clone())
    }
    /// The tree of `S_k`, k = 1..=n+1.
    pub fn seal_tree(&self, k: u32) -> Result<&TapTree> {
        if k == self.spec.periods + 1 {
            return Ok(&self.final_tree);
        }
        Ok(&self.template(k)?.tree)
    }
    /// `κ_k`, the connector closing k creates.
    pub fn connector_outpoint(&self, k: u32) -> Result<OutPoint> {
        Ok(OutPoint { txid: self.template(k)?.tx.compute_txid(), vout: 1 })
    }

    /// Closing k with a root: the member signs the root and the closing.
    pub fn close(&self, member: &Member, k: u32, root: &[u8; 20]) -> Result<Transaction> {
        let t = self.template(k)?;
        let leaf = t.tree.leaf("close")?;
        let sig_m = sign(member.keypair(), &t.tx, &t.prevout, &leaf.script)?;
        let mut args = wots_wire(&member.sign_root(k, root)?);
        args.push(sig_m);
        args.push(t.sig_close.clone());
        let mut tx = t.tx.clone();
        tx.input[0].witness = tapscript_witness(&args, &leaf.script, &t.tree.control_block("close")?);
        Ok(tx)
    }

    /// Closing k for an idle period: reveals `z_k`.
    pub fn close_empty(&self, member: &Member, k: u32) -> Result<Transaction> {
        let t = self.template(k)?;
        let leaf = t.tree.leaf("close_empty")?;
        let sig_m = sign(member.keypair(), &t.tx, &t.prevout, &leaf.script)?;
        let args = vec![member.empty_preimage(k).to_vec(), sig_m, t.sig_empty.clone()];
        let mut tx = t.tx.clone();
        tx.input[0].witness = tapscript_witness(&args, &leaf.script, &t.tree.control_block("close_empty")?);
        Ok(tx)
    }

    /// The pinned burn of `S_k`, broadcastable by anyone once the grace has
    /// passed.
    pub fn burn(&self, k: u32) -> Result<Transaction> {
        let t = self.template(k)?;
        let leaf = t.tree.leaf("burn")?;
        let mut tx = t.burn.tx.clone();
        tx.input[0].witness = tapscript_witness(std::slice::from_ref(&t.burn.sig), &leaf.script, &t.tree.control_block("burn")?);
        Ok(tx)
    }

    /// The pinned slash of the final output on two different root
    /// signatures for period j, broadcastable by anyone after `race_from`.
    pub fn slash(&self, j: u32, a: &WotsSig, b: &WotsSig) -> Result<Transaction> {
        let s = self.slashes.get((j as usize).wrapping_sub(1)).ok_or_else(|| anyhow!("period {j} is outside the term"))?;
        let name = format!("slash_{j}");
        let leaf = self.final_tree.leaf(&name)?;
        let mut args = wots_wire(a);
        args.extend(wots_wire(b));
        args.push(s.sig.clone());
        let mut tx = s.tx.clone();
        tx.input[0].witness = tapscript_witness(&args, &leaf.script, &self.final_tree.control_block(&name)?);
        Ok(tx)
    }

    /// The member's reclaim of the final output after `release`.
    pub fn reclaim(&self, member: &Member, outputs: Vec<TxOut>) -> Result<Transaction> {
        let k = self.spec.periods + 1;
        let leaf = self.final_tree.leaf("reclaim")?;
        let prevout = self.seal_txout(k)?;
        let mut tx = build_spend(self.seal_outpoint(k)?, &leaf.timelock, outputs);
        let sig = sign(member.keypair(), &tx, &prevout, &leaf.script)?;
        tx.input[0].witness = tapscript_witness(&[sig], &leaf.script, &self.final_tree.control_block("reclaim")?);
        Ok(tx)
    }

    // ---- connector trees ----

    fn leaf_node(&self, s: u32) -> Result<u32> {
        let q = self.spec.leaves();
        ensure!(s < q, "leaf {s} is outside the connector tree ({q} leaves)");
        Ok(q + s)
    }

    /// The splits on the path from `κ_k` to leaf s, root first, with their
    /// ceremony signatures in the witness: broadcast them in order to
    /// create the leaf. (Splits already on chain from an earlier dispute in
    /// the same period are simply skipped by the caller.)
    pub fn connector_path(&self, k: u32, s: u32) -> Result<Vec<Transaction>> {
        let t = self.template(k)?;
        let node = node_tree(&t.split_key)?;
        let leaf = node.leaf("split")?;
        let cb = node.control_block("split")?;
        let mut path = Vec::new();
        let mut n = self.leaf_node(s)?;
        while n > 1 {
            n /= 2;
            path.push(n);
        }
        path.reverse();
        let mut txs = Vec::with_capacity(path.len());
        for n in path {
            let sp = &t.splits[(n - 1) as usize];
            let mut tx = sp.tx.clone();
            tx.input[0].witness = tapscript_witness(std::slice::from_ref(&sp.sig), &leaf.script, &cb);
            txs.push(tx);
        }
        Ok(txs)
    }

    /// The outpoint and output of leaf connector s of closing k (known in
    /// advance: every transaction on its path is pinned).
    pub fn leaf_connector(&self, k: u32, s: u32) -> Result<(OutPoint, TxOut)> {
        let t = self.template(k)?;
        let n = self.leaf_node(s)?;
        let parent = &t.splits[(n / 2 - 1) as usize];
        let vout = n % 2;
        Ok((OutPoint { txid: parent.tx.compute_txid(), vout }, parent.tx.output[vout as usize].clone()))
    }

    /// The witness that spends leaf connector s of closing k, given its
    /// preimage (the mover's, handed out at registration).
    pub fn leaf_witness(&self, k: u32, s: u32, preimage: &[u8; 32]) -> Result<bitcoin::Witness> {
        let lock = self.member.leaf_locks.get((k - 1) as usize).and_then(|l| l.get(s as usize));
        let lock = lock.ok_or_else(|| anyhow!("no leaf ({k}, {s})"))?;
        let tree = leaf_tree(lock)?;
        let leaf = tree.leaf("use")?;
        Ok(tapscript_witness(&[preimage.to_vec()], &leaf.script, &tree.control_block("use")?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub(crate) fn spec() -> SealSpec {
        SealSpec {
            value: Amount::from_sat(200_000),
            start: 110,
            period: 4,
            periods: 3,
            grace: 2,
            release_delay: 5,
            fanout_depth: 3,
            leaf_value: Amount::from_sat(330),
            split_fee: Amount::from_sat(400),
            anchor_value: Amount::from_sat(240),
            closing_fee: Amount::from_sat(3_000),
        }
    }

    fn chain() -> (SealSpec, Member, PresignedChain) {
        let s = spec();
        let m = Member::new([7; 32], &s);
        let funding = OutPoint { txid: bitcoin::Txid::all_zeros(), vout: 0 };
        let c = ceremony(&s, &m.public(), funding, &[3; 32]).unwrap();
        (s, m, c)
    }

    #[test]
    fn ceremony_builds_a_linked_chain() {
        let (s, m, chain) = chain();
        assert_eq!(chain.closings.len(), 3);
        for k in 1..=3u32 {
            let t = &chain.closings[(k - 1) as usize];
            assert_eq!(t.tx.input[0].previous_output, chain.seal_outpoint(k).unwrap());
            assert_eq!(t.burn.tx.input[0].previous_output, chain.seal_outpoint(k).unwrap(), "the burn spends S_k too");
            assert_eq!(t.tx.lock_time.to_consensus_u32(), s.height(k) - 1);
            assert_eq!(t.burn.tx.lock_time.to_consensus_u32(), s.burn_from(k) - 1);
            assert_eq!(t.tx.output[0].value, s.output_value(k + 1));
            assert_eq!(t.tx.output[1].value, s.connector_value());
        }
        assert_eq!(chain.closings[2].tx.output[0].script_pubkey, chain.final_tree.script_pubkey());
        assert_eq!(first_tree(&s, &m.public(), &[3; 32]).unwrap().script_pubkey(), chain.closings[0].tree.script_pubkey());
        for (j, sl) in chain.slashes.iter().enumerate() {
            assert_eq!(sl.tx.input[0].previous_output, chain.seal_outpoint(4).unwrap(), "slash {} spends the final output", j + 1);
        }
    }

    #[test]
    fn connector_tree_is_value_balanced_and_linked() {
        let (s, _, chain) = chain();
        let t = &chain.closings[0];
        assert_eq!(t.splits.len(), (s.leaves() - 1) as usize);
        assert_eq!(t.splits[0].tx.input[0].previous_output, chain.connector_outpoint(1).unwrap());
        for sp in &t.splits {
            let out: Amount = sp.tx.output.iter().map(|o| o.value).sum();
            assert_eq!(sp.prevout.value, out + s.split_fee, "each split pays exactly its fixed fee");
        }
        for leaf in 0..s.leaves() {
            let path = chain.connector_path(1, leaf).unwrap();
            assert_eq!(path.len(), s.fanout_depth as usize);
            let (op, out) = chain.leaf_connector(1, leaf).unwrap();
            assert_eq!(path.last().unwrap().compute_txid(), op.txid, "the path ends at the leaf's parent");
            assert_eq!(out.value, s.leaf_value);
            // consecutive splits chain
            for w in path.windows(2) {
                assert_eq!(w[1].input[0].previous_output.txid, w[0].compute_txid());
            }
        }
    }

    #[test]
    fn roots_verify_off_chain_and_differ() {
        let s = spec();
        let m = Member::new([7; 32], &s);
        let p = m.public();
        let a = m.sign_root(1, &[1; 20]).unwrap();
        let b = m.sign_root(1, &[2; 20]).unwrap();
        assert_eq!(p.roots[0].verify(&a).unwrap(), vec![1; 20]);
        assert_eq!(p.roots[0].verify(&b).unwrap(), vec![2; 20]);
        assert!(p.roots[1].verify(&a).is_err(), "a period-1 root does not verify under period 2's key");
    }
}
