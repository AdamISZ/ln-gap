//! LN-GAP 2.5: a venue member's seal chain (V25_POC_PLAN.md, Phase 1).
//!
//! A member locks its bond in a chain of SEAL OUTPUTS `S_1 .. S_n`, one per
//! period of a term, and a final output `S_{n+1}`. The k-th SEAL CLOSING
//! spends `S_k` into `S_{k+1}` from height `H_k` on, and carries in its
//! witness a one-time (Winternitz) signature of the member's 20-byte root
//! for period k, or, for an idle period, the preimage `z_k` of a committed
//! hash. Every closing also creates a CONNECTOR output (Phase 2 unfolds it
//! into a tree) and an anchor output for fee bumping.
//!
//! Heights are "mineable from": a leaf that opens at height `X` carries
//! `CLTV X - 1` (a transaction is final in a block of height greater than
//! its nLockTime), so its spend can be in block `X` and not before.
//!
//! Each seal output's leaves:
//! - `close`: ceremony key, member key, WOTS verify of the root;
//! - `close_empty`: ceremony key, member key, the empty-period preimage;
//! - `burn`: anyone, after `H_k + grace` (the fee race takes the bond);
//! - `slash_{j}`: two different roots under period j's root key, behind
//!   `race_from` (no head start for the cheater, D46).
//!
//! The final output carries `reclaim` (member key, after `release`) and
//! the same slash leaves.
//!
//! PINNING: Bitcoin has no covenants, so the closings' outputs (the next
//! seal output at full value, the connector, the anchor) are fixed by a
//! pre-signing CEREMONY over per-period keys `Q_k` that are then deleted
//! (one honest deleter suffices). The ceremony is independent of any
//! contract: the root goes in the witness, which no signature covers.
//! Here the ceremony is a single toy party (`ceremony`), whose secrets go
//! out of scope when it returns.

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
    /// Value of each closing's connector output.
    pub connector_value: Amount,
    /// Value of each closing's anchor output (fee bumping).
    pub anchor_value: Amount,
    /// The fixed fee of each pre-signed closing.
    pub closing_fee: Amount,
}

impl SealSpec {
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
    /// The value of `S_k` (k = 1..=n+1).
    pub fn output_value(&self, k: u32) -> Amount {
        let per = self.connector_value + self.anchor_value + self.closing_fee;
        self.value - per * u64::from(k - 1)
    }
    fn check(&self) -> Result<()> {
        ensure!(self.periods >= 1 && self.period >= 1, "a term needs at least one period of at least one block");
        ensure!(self.start >= 2, "H_1 must be at least 2");
        ensure!(self.grace >= 1, "the grace must be at least one block");
        ensure!(self.grace < self.period, "the grace must end before the next period's closing");
        ensure!(
            self.output_value(self.periods + 1) > Amount::from_sat(1_000),
            "the bond does not cover the term's connectors, anchors and fees"
        );
        Ok(())
    }
}

fn derive(seed: &[u8; 32], tag: &str, k: u32) -> [u8; 32] {
    let mut data = seed.to_vec();
    data.extend_from_slice(tag.as_bytes());
    data.extend_from_slice(&k.to_be_bytes());
    sha256::Hash::hash(&data).to_byte_array()
}

fn keypair(secret: [u8; 32]) -> Keypair {
    Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&secret).expect("a hash is a valid secret key"))
}

/// A member's secrets: its key, and per period a root key and an
/// empty-period preimage, all derived from one seed.
pub struct Member {
    key: Keypair,
    seed: [u8; 32],
    periods: u32,
}

/// What a member publishes before the ceremony.
#[derive(Clone, Debug)]
pub struct MemberPublic {
    pub key: XOnlyPublicKey,
    /// `K^root_k`, k = 1..=n (index k - 1).
    pub roots: Vec<WotsPublic>,
    /// `HASH160(z_k)`, k = 1..=n (index k - 1).
    pub empties: Vec<Hash160>,
}

impl Member {
    pub fn new(seed: [u8; 32], periods: u32) -> Member {
        Member { key: keypair(derive(&seed, "member-key", 0)), seed, periods }
    }
    fn root_secret(&self, k: u32) -> WotsSecret {
        WotsSecret::from_entropy(root_params(), derive(&self.seed, "root", k))
    }
    /// The empty-period preimage `z_k`.
    pub fn empty_preimage(&self, k: u32) -> [u8; 32] {
        derive(&self.seed, "empty", k)
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

/// `burn` for period k: anyone, once the grace has passed.
pub fn burn_leaf(spec: &SealSpec, k: u32) -> Leaf {
    let lock = spec.burn_from(k) - 1;
    Leaf::new("burn", Builder::new().cltv(lock).push_int(1).into_script(), Timelock::cltv(lock))
}

/// `slash_{j}`: two valid root signatures under period j's key over
/// DIFFERENT roots (the choreography of the v1 `equiv` leaf: verify the
/// top block, park its digits, verify the block below, restore, compare).
pub fn slash_leaf(spec: &SealSpec, member: &MemberPublic, j: u32) -> Leaf {
    let lock = spec.race_from() - 1;
    let key = &member.roots[(j - 1) as usize];
    let m = key.params.message_digits as usize;
    let mut b = Builder::new().cltv(lock).wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    b = b.push_int(0);
    for j in 0..m {
        b = b
            .push_int((m - j) as i64)
            .push_opcode(OP_PICK)
            .push_int((2 * m - j + 1) as i64)
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

fn slash_leaves(spec: &SealSpec, member: &MemberPublic) -> Vec<Leaf> {
    (1..=spec.periods).map(|j| slash_leaf(spec, member, j)).collect()
}

/// The tree of seal output `S_k`, k = 1..=n.
pub fn seal_tree(spec: &SealSpec, ceremony: &XOnlyPublicKey, member: &MemberPublic, k: u32) -> Result<TapTree> {
    let mut leaves = vec![
        close_leaf(spec, ceremony, member, k),
        close_empty_leaf(spec, ceremony, member, k),
        burn_leaf(spec, k),
    ];
    leaves.extend(slash_leaves(spec, member));
    TapTree::new(leaves)
}

/// The tree of the final output `S_{n+1}`.
pub fn final_tree(spec: &SealSpec, member: &MemberPublic) -> Result<TapTree> {
    let mut leaves = vec![reclaim_leaf(spec, member)];
    leaves.extend(slash_leaves(spec, member));
    TapTree::new(leaves)
}

/// Phase 1's connector: a taproot output spendable only under the period's
/// connector key (Phase 2 replaces it with the root of a pinned split tree).
pub fn connector_tree(connector_key: &XOnlyPublicKey) -> Result<TapTree> {
    TapTree::new(vec![Leaf::new("split", Builder::new().checksig(connector_key).into_script(), Timelock::NONE)])
}

/// Pay-to-anchor (`OP_1 <0x4e73>`): anyone may spend it to bump the
/// closing by CPFP.
pub fn anchor_spk() -> ScriptBuf {
    ScriptBuf::from_bytes(vec![0x51, 0x02, 0x4e, 0x73])
}

/// One pre-signed closing.
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
}

/// The ceremony's output: the whole term's closings, pre-signed.
#[derive(Clone, Debug)]
pub struct PresignedChain {
    pub spec: SealSpec,
    pub member: MemberPublic,
    /// `Q_k`, k = 1..=n.
    pub ceremony_keys: Vec<XOnlyPublicKey>,
    /// The connector keys (Phase 1 placeholder), k = 1..=n.
    pub connector_keys: Vec<XOnlyPublicKey>,
    pub funding: OutPoint,
    pub closings: Vec<ClosingTemplate>,
    pub final_tree: TapTree,
}

/// The tree of `S_1` (to fund it): the ceremony keys are needed, so the
/// toy ceremony derives them from its seed here too.
pub fn first_tree(spec: &SealSpec, member: &MemberPublic, ceremony_seed: &[u8; 32]) -> Result<TapTree> {
    let q1 = keypair(derive(ceremony_seed, "Q", 1)).x_only_public_key().0;
    seal_tree(spec, &q1, member, 1)
}

/// The toy ceremony: derive `Q_k` and the connector keys, build every
/// closing of the term and pre-sign both closing leaves of each. The
/// secrets are dropped when this returns.
pub fn ceremony(spec: &SealSpec, member: &MemberPublic, funding: OutPoint, ceremony_seed: &[u8; 32]) -> Result<PresignedChain> {
    spec.check()?;
    ensure!(member.roots.len() == spec.periods as usize, "the member's keys must cover the term");
    let n = spec.periods;
    let qs: Vec<Keypair> = (1..=n).map(|k| keypair(derive(ceremony_seed, "Q", k))).collect();
    let cks: Vec<Keypair> = (1..=n).map(|k| keypair(derive(ceremony_seed, "connector", k))).collect();
    let trees: Vec<TapTree> = (1..=n)
        .map(|k| seal_tree(spec, &qs[(k - 1) as usize].x_only_public_key().0, member, k))
        .collect::<Result<_>>()?;
    let final_tree = final_tree(spec, member)?;
    let mut prev = funding;
    let mut prevout = TxOut { value: spec.value, script_pubkey: trees[0].script_pubkey() };
    let mut closings = Vec::with_capacity(n as usize);
    for k in 1..=n {
        let i = (k - 1) as usize;
        let next_spk = if k < n { trees[i + 1].script_pubkey() } else { final_tree.script_pubkey() };
        let outputs = vec![
            TxOut { value: spec.output_value(k + 1), script_pubkey: next_spk },
            TxOut {
                value: spec.connector_value,
                script_pubkey: connector_tree(&cks[i].x_only_public_key().0)?.script_pubkey(),
            },
            TxOut { value: spec.anchor_value, script_pubkey: anchor_spk() },
        ];
        let close = trees[i].leaf("close")?;
        let empty = trees[i].leaf("close_empty")?;
        ensure!(close.timelock == empty.timelock, "both closing leaves share the closing's locktime");
        let tx = build_spend(prev, &close.timelock, outputs);
        let sig = |leaf: &ScriptBuf| -> Result<Vec<u8>> {
            Ok(sign_tapscript(&qs[i], &tx, 0, std::slice::from_ref(&prevout), leaf)?.as_ref().to_vec())
        };
        let (sig_close, sig_empty) = (sig(&close.script)?, sig(&empty.script)?);
        let next = OutPoint { txid: tx.compute_txid(), vout: 0 };
        let next_out = tx.output[0].clone();
        closings.push(ClosingTemplate { k, tx, prevout, tree: trees[i].clone(), sig_close, sig_empty });
        prev = next;
        prevout = next_out;
    }
    Ok(PresignedChain {
        spec: spec.clone(),
        member: member.clone(),
        ceremony_keys: qs.iter().map(|q| q.x_only_public_key().0).collect(),
        connector_keys: cks.iter().map(|c| c.x_only_public_key().0).collect(),
        funding,
        closings,
        final_tree,
    })
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
    /// The connector outpoint closing k creates.
    pub fn connector_outpoint(&self, k: u32) -> Result<OutPoint> {
        Ok(OutPoint { txid: self.template(k)?.tx.compute_txid(), vout: 1 })
    }

    /// Closing k with a root: the member signs the root and the closing.
    pub fn close(&self, member: &Member, k: u32, root: &[u8; 20]) -> Result<Transaction> {
        let t = self.template(k)?;
        let leaf = t.tree.leaf("close")?;
        let sig_m = sign_tapscript(member.keypair(), &t.tx, 0, std::slice::from_ref(&t.prevout), &leaf.script)?;
        let mut args = wots_wire(&member.sign_root(k, root)?);
        args.push(sig_m.as_ref().to_vec());
        args.push(t.sig_close.clone());
        let mut tx = t.tx.clone();
        tx.input[0].witness = tapscript_witness(&args, &leaf.script, &t.tree.control_block("close")?);
        Ok(tx)
    }

    /// Closing k for an idle period: reveals `z_k`.
    pub fn close_empty(&self, member: &Member, k: u32) -> Result<Transaction> {
        let t = self.template(k)?;
        let leaf = t.tree.leaf("close_empty")?;
        let sig_m = sign_tapscript(member.keypair(), &t.tx, 0, std::slice::from_ref(&t.prevout), &leaf.script)?;
        let args = vec![member.empty_preimage(k).to_vec(), sig_m.as_ref().to_vec(), t.sig_empty.clone()];
        let mut tx = t.tx.clone();
        tx.input[0].witness = tapscript_witness(&args, &leaf.script, &t.tree.control_block("close_empty")?);
        Ok(tx)
    }

    /// Anyone's burn of `S_k` once the grace has passed.
    pub fn burn(&self, k: u32, outputs: Vec<TxOut>) -> Result<Transaction> {
        let tree = self.seal_tree(k)?;
        let leaf = tree.leaf("burn")?;
        let mut tx = build_spend(self.seal_outpoint(k)?, &leaf.timelock, outputs);
        tx.input[0].witness = tapscript_witness(&[], &leaf.script, &tree.control_block("burn")?);
        Ok(tx)
    }

    /// Anyone's slash of `S_k` (k = 1..=n+1, wherever the bond sits) on
    /// two different root signatures for period j.
    pub fn slash(&self, k: u32, j: u32, a: &WotsSig, b: &WotsSig, outputs: Vec<TxOut>) -> Result<Transaction> {
        let tree = self.seal_tree(k)?;
        let name = format!("slash_{j}");
        let leaf = tree.leaf(&name)?;
        let mut args = wots_wire(a);
        args.extend(wots_wire(b));
        let mut tx = build_spend(self.seal_outpoint(k)?, &leaf.timelock, outputs);
        tx.input[0].witness = tapscript_witness(&args, &leaf.script, &tree.control_block(&name)?);
        Ok(tx)
    }

    /// The member's reclaim of the final output after `release`.
    pub fn reclaim(&self, member: &Member, outputs: Vec<TxOut>) -> Result<Transaction> {
        let k = self.spec.periods + 1;
        let tree = self.seal_tree(k)?;
        let leaf = tree.leaf("reclaim")?;
        let prevout = self.seal_txout(k)?;
        let mut tx = build_spend(self.seal_outpoint(k)?, &leaf.timelock, outputs);
        let sig = sign_tapscript(member.keypair(), &tx, 0, std::slice::from_ref(&prevout), &leaf.script)?;
        tx.input[0].witness = tapscript_witness(&[sig.as_ref().to_vec()], &leaf.script, &tree.control_block("reclaim")?);
        Ok(tx)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec() -> SealSpec {
        SealSpec {
            value: Amount::from_sat(200_000),
            start: 110,
            period: 4,
            periods: 3,
            grace: 2,
            release_delay: 5,
            connector_value: Amount::from_sat(330),
            anchor_value: Amount::from_sat(330),
            closing_fee: Amount::from_sat(3_000),
        }
    }

    #[test]
    fn ceremony_builds_a_linked_chain() {
        let s = spec();
        let m = Member::new([7; 32], s.periods);
        let funding = OutPoint { txid: bitcoin::Txid::all_zeros(), vout: 0 };
        let chain = ceremony(&s, &m.public(), funding, &[3; 32]).unwrap();
        assert_eq!(chain.closings.len(), 3);
        for k in 1..=3u32 {
            let t = &chain.closings[(k - 1) as usize];
            assert_eq!(t.tx.input[0].previous_output, chain.seal_outpoint(k).unwrap());
            assert_eq!(t.tx.lock_time.to_consensus_u32(), s.height(k) - 1);
            assert_eq!(t.tx.output[0].value, s.output_value(k + 1));
        }
        assert_eq!(chain.closings[2].tx.output[0].script_pubkey, chain.final_tree.script_pubkey());
        assert_eq!(first_tree(&s, &m.public(), &[3; 32]).unwrap().script_pubkey(), chain.closings[0].tree.script_pubkey());
    }

    #[test]
    fn roots_verify_off_chain_and_differ() {
        let m = Member::new([7; 32], 3);
        let p = m.public();
        let a = m.sign_root(1, &[1; 20]).unwrap();
        let b = m.sign_root(1, &[2; 20]).unwrap();
        assert_eq!(p.roots[0].verify(&a).unwrap(), vec![1; 20]);
        assert_eq!(p.roots[0].verify(&b).unwrap(), vec![2; 20]);
        assert!(p.roots[1].verify(&a).is_err(), "a period-1 root does not verify under period 2's key");
    }
}
