//! Chain data as the claim sees it: raw headers, transaction Merkle paths,
//! and the fixed-layout anchor transaction (decision 4: `OP_RETURN <root>`).

use anyhow::{ensure, Result};
use bitcoin::consensus::encode::serialize;
use bitcoin::hashes::Hash;
use bitcoin::{OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut, Txid, Witness};
use sha2::{Digest, Sha256};

pub fn sha256d(data: &[u8]) -> [u8; 32] {
    Sha256::digest(Sha256::digest(data)).into()
}

/// A block header as 80 raw bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RawHeader(pub [u8; 80]);

impl RawHeader {
    pub fn from_header(h: &bitcoin::block::Header) -> RawHeader {
        RawHeader(serialize(h).try_into().expect("80 bytes"))
    }
    /// The block hash as the raw 32 SHA-256d bytes (internal byte order).
    pub fn digest(&self) -> [u8; 32] {
        sha256d(&self.0)
    }
    pub fn prev(&self) -> [u8; 32] {
        self.0[4..36].try_into().unwrap()
    }
    pub fn merkle_root(&self) -> [u8; 32] {
        self.0[36..68].try_into().unwrap()
    }
    pub fn nbits(&self) -> u32 {
        u32::from_le_bytes(self.0[72..76].try_into().unwrap())
    }
    /// The 256-bit target of `nbits` as 32 little-endian bytes.
    pub fn target_le(nbits: u32) -> [u8; 32] {
        let exp = (nbits >> 24) as usize;
        let mant = nbits & 0x007f_ffff;
        let mut t = [0u8; 32];
        // target = mant * 256^(exp - 3)
        let m = mant.to_le_bytes();
        for (i, b) in m.iter().take(3).enumerate() {
            let pos = exp - 3 + i;
            if pos < 32 {
                t[pos] = *b;
            }
        }
        t
    }
    /// Does the header's hash meet its own target?
    pub fn meets_target(&self) -> bool {
        let d = self.digest();
        let t = Self::target_le(self.nbits());
        for i in (0..32).rev() {
            if d[i] != t[i] {
                return d[i] < t[i];
            }
        }
        true
    }
}

/// The Merkle path of `txids[index]` to the block's Merkle root (Bitcoin's
/// rule: an odd last element is paired with itself). `siblings[j]` with
/// `side[j]` true meaning the running node is the right child.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub siblings: Vec<[u8; 32]>,
    pub sides: Vec<bool>,
}

impl MerklePath {
    pub fn for_tx(txids: &[Txid], index: usize) -> MerklePath {
        let mut level: Vec<[u8; 32]> = txids.iter().map(|t| t.to_byte_array()).collect();
        let mut i = index;
        let mut siblings = Vec::new();
        let mut sides = Vec::new();
        while level.len() > 1 {
            if level.len() % 2 == 1 {
                level.push(*level.last().unwrap());
            }
            let sib = if i % 2 == 0 { level[i + 1] } else { level[i - 1] };
            siblings.push(sib);
            sides.push(i % 2 == 1);
            level = level.chunks(2).map(|p| { let mut b = [0u8; 64]; b[..32].copy_from_slice(&p[0]); b[32..].copy_from_slice(&p[1]); sha256d(&b) }).collect();
            i /= 2;
        }
        MerklePath { siblings, sides }
    }
    pub fn root(&self, txid: &[u8; 32]) -> [u8; 32] {
        let mut h = *txid;
        for (s, right) in self.siblings.iter().zip(&self.sides) {
            let mut b = [0u8; 64];
            if *right {
                b[..32].copy_from_slice(s);
                b[32..].copy_from_slice(&h);
            } else {
                b[..32].copy_from_slice(&h);
                b[32..].copy_from_slice(s);
            }
            h = sha256d(&b);
        }
        h
    }
}

/// Serialized size of an anchor transaction (fixed layout).
pub const ANCHOR_TX_LEN: usize = 208;
/// Byte offset of the root inside the serialized anchor transaction (word-aligned to the third 64-byte chunk).
pub const ANCHOR_ROOT_OFFSET: usize = 128;
const FILLER: usize = 69;

/// Build the anchor transaction: one input spending the previous anchor
/// outpoint (key-path), outputs `OP_RETURN <69 filler bytes> <root> OP_0`
/// then a P2TR change output. Its legacy serialization is exactly
/// [`ANCHOR_TX_LEN`] bytes with the root at [`ANCHOR_ROOT_OFFSET`]
/// (4 + 1 + 41 + 1 + 8 + 1 + 1 + 1 + 69 + 1 = 128 bytes before it).
pub fn anchor_tx(prev: OutPoint, root: &[u8; 32], change_spk: ScriptBuf, change_value: bitcoin::Amount) -> Transaction {
    let mut script = Vec::with_capacity(105);
    script.push(0x6a); // OP_RETURN
    script.push(FILLER as u8); // OP_PUSHBYTES_69
    script.extend(std::iter::repeat(0u8).take(FILLER));
    script.push(32); // OP_PUSHBYTES_32
    script.extend_from_slice(root);
    script.push(0x00); // OP_0: pads the serialization to 208 bytes
    let tx = Transaction {
        version: bitcoin::transaction::Version::TWO,
        lock_time: bitcoin::absolute::LockTime::ZERO,
        input: vec![TxIn { previous_output: prev, script_sig: ScriptBuf::new(), sequence: Sequence::ENABLE_RBF_NO_LOCKTIME, witness: Witness::new() }],
        output: vec![TxOut { value: bitcoin::Amount::ZERO, script_pubkey: ScriptBuf::from_bytes(script) }, TxOut { value: change_value, script_pubkey: change_spk }],
    };
    let bytes = anchor_bytes(&tx);
    debug_assert_eq!(bytes.len(), ANCHOR_TX_LEN);
    debug_assert_eq!(&bytes[ANCHOR_ROOT_OFFSET..ANCHOR_ROOT_OFFSET + 32], root);
    tx
}

/// The legacy (txid) serialization of a transaction.
pub fn anchor_bytes(tx: &Transaction) -> Vec<u8> {
    let mut t = tx.clone();
    for i in &mut t.input {
        i.witness = Witness::new();
    }
    serialize(&t)
}

/// Byte offset of the output count in the serialized anchor (must be 2).
pub const ANCHOR_NOUT_OFFSET: usize = 46;
/// Byte offset of output 0's first script byte (must be `OP_RETURN`, 0x6a).
pub const ANCHOR_OPRETURN_OFFSET: usize = 56;

/// Check an anchor transaction's shape — exactly 208 bytes, two outputs, the
/// first unspendable (`OP_RETURN …`) — and extract its root. The same three
/// facts are predicates of the inclusion claim, so the anchor chain has
/// exactly one spendable output per anchor and is a single line.
pub fn anchor_root(tx: &Transaction) -> Result<[u8; 32]> {
    let b = anchor_bytes(tx);
    ensure!(b.len() == ANCHOR_TX_LEN, "anchor tx is {} bytes, expected {ANCHOR_TX_LEN}", b.len());
    ensure!(b[ANCHOR_NOUT_OFFSET] == 2, "anchor tx has {} outputs, expected 2", b[ANCHOR_NOUT_OFFSET]);
    ensure!(b[ANCHOR_OPRETURN_OFFSET] == 0x6a, "anchor tx output 0 is spendable (no OP_RETURN)");
    Ok(b[ANCHOR_ROOT_OFFSET..ANCHOR_ROOT_OFFSET + 32].try_into().unwrap())
}

/// Walk an anchor chain from `genesis`: every transaction must have the
/// anchor shape and spend the previous anchor's output 1. Returns the tip
/// (the outpoint the next anchor must spend) and the roots in order. This is
/// the check a user runs before trusting a receipt's `prev_anchor`.
pub fn verify_anchor_chain(genesis: OutPoint, anchors: &[Transaction]) -> Result<(OutPoint, Vec<[u8; 32]>)> {
    let mut tip = genesis;
    let mut roots = Vec::new();
    for (i, tx) in anchors.iter().enumerate() {
        ensure!(tx.input.len() == 1 && tx.input[0].previous_output == tip, "anchor {i} does not spend the chain's tip {tip}");
        roots.push(anchor_root(tx)?);
        tip = OutPoint { txid: tx.compute_txid(), vout: 1 };
    }
    Ok((tip, roots))
}

/// The 36 outpoint bytes as they appear in the serialization (txid, then vout LE).
pub fn outpoint_bytes(op: &OutPoint) -> [u8; 36] {
    let mut b = [0u8; 36];
    b[..32].copy_from_slice(&op.txid.to_byte_array());
    b[32..].copy_from_slice(&op.vout.to_le_bytes());
    b
}

/// A plain P2TR output for `key` (no script tree), and its key-path spend.
pub fn p2tr_spk(key: &bitcoin::XOnlyPublicKey) -> ScriptBuf {
    ScriptBuf::new_p2tr(bitcoin::secp256k1::SECP256K1, *key, None)
}

/// Sign input 0 of `tx` (spending `prev`, a [`p2tr_spk`] output of `kp`) by the key path.
pub fn sign_keypath(tx: &mut Transaction, prev: &TxOut, kp: &bitcoin::key::Keypair) -> Result<()> {
    use bitcoin::hashes::Hash as _;
    use bitcoin::key::TapTweak;
    use bitcoin::sighash::{Prevouts, SighashCache, TapSighashType};
    let tweaked = kp.tap_tweak(bitcoin::secp256k1::SECP256K1, None);
    let sighash = SighashCache::new(&*tx).taproot_key_spend_signature_hash(0, &Prevouts::All(std::slice::from_ref(prev)), TapSighashType::Default)?;
    let sig = bitcoin::secp256k1::SECP256K1.sign_schnorr(&bitcoin::secp256k1::Message::from_digest(sighash.to_byte_array()), &tweaked.to_keypair());
    tx.input[0].witness = Witness::from_slice(&[sig.as_ref().to_vec()]);
    Ok(())
}
