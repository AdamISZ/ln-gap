//! The refutation leaf (POS_FACTCHAIN_PLAN.md step 3; D32): the answer to a
//! "Bob did not publish a valid move in the window" claim.
//!
//! Bob's refutation spend proves, in one leaf:
//!
//! 1. the venue attested slot d's head — the EC-OTS readout of the head's 96
//!    chunk positions (one possession proof per chunk under the slot's epoch
//!    table), leaving the head's nibbles on the stack; and
//! 2. the mover RE-COMMITS the same 48 bytes under a per-slot refute key
//!    (Winternitz `wots_verify`), each re-committed digit tied nibble-equal
//!    to the read-out value.
//!
//! The re-commitment is what parks the tuple on-chain for the disprove
//! stage: the refutation output's tree is keyed to the refute key, so a
//! follow-on leaf can trust a tuple carried by the key's reveal, because the
//! refutation leaf is the only place that key's signature is tied to the
//! venue attestation. (The contract's existing re-commitment discipline —
//! pre-signed graphs have no covenants, so run-time data crosses outputs
//! only as pinned-key signatures.)
//!
//! Witness (consumption order): the WOTS reveal of the head (the
//! re-commitment), then per head chunk the possession signature and value.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use lngap_ec_wots::{chunk_value, readout_value_fragment, snum, EpochTable};
use lngap_factchain::HEAD_BYTES;
use lngap_lamport::winternitz::{WotsExt, WotsParams, WotsPublic, WotsSecret, WotsSig};

/// The head field's first chunk position in the 96-byte header
/// (`prev(20) root(20)` precede it) and its length in chunks.
pub const HEAD_CHUNK_START: usize = 40 * 2;
pub const HEAD_CHUNKS: usize = HEAD_BYTES * 2;

/// The Winternitz parameters of a refute key (the 48-byte head: 96 message
/// digits plus checksum digits).
pub fn refute_params() -> WotsParams {
    WotsParams::for_bytes(HEAD_BYTES as u32)
}

/// A refute key from entropy. (In the graph: per role per slot, pinned at
/// open; the key-set derivation lands with the contract integration.)
pub fn refute_key(entropy: [u8; 32]) -> WotsSecret {
    WotsSecret::from_entropy(refute_params(), entropy)
}

/// A WOTS signature's witness elements in WIRE order (bottom of stack
/// first, as `lngap_btc::witness::tapscript_witness` expects): ascending
/// digits, hash element before digit element. (`WotsSig::consumption_order`
/// is top-first, the reverse.)
pub fn wots_wire(sig: &WotsSig) -> Vec<Vec<u8>> {
    let n = sig.params.total_digits() as usize;
    let mut w = Vec::with_capacity(2 * n);
    for i in 0..n {
        w.push(sig.hashes[i].to_vec());
        w.push(snum(sig.digits[i]));
    }
    w
}

/// The refutation leaf for one slot: `table` is the slot's epoch table (only
/// the head chunks' points are embedded in the script) and `key` the mover's
/// refute key for the slot.
pub fn refute_leaf(table: &EpochTable, key: &WotsPublic) -> ScriptBuf {
    let mut b = Builder::new().wots_verify(key);
    // the re-committed digits to the altstack (d_0 comes out first)
    for _ in 0..HEAD_CHUNKS {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    // the readout, each attested nibble tied to its re-committed digit
    for j in HEAD_CHUNK_START..HEAD_CHUNK_START + HEAD_CHUNKS {
        b = readout_value_fragment(b, &table.points[j]);
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_EQUALVERIFY);
    }
    b.push_int(1).into_script()
}

/// The refutation witness, wire order. `head_sigs[j]` must sign the spend's
/// sighash under the point for the attested value of head chunk `j`
/// (= header chunk `HEAD_CHUNK_START + j`); `sig` re-commits the head.
pub fn refute_witness(
    head: &[u8; HEAD_BYTES],
    head_sigs: &[Vec<u8>],
    sig: &WotsSig,
) -> Vec<Vec<u8>> {
    assert_eq!(head_sigs.len(), HEAD_CHUNKS);
    let mut w = Vec::with_capacity(2 * HEAD_CHUNKS + 2 * sig.params.total_digits() as usize);
    // chunk items, descending: head chunk 0's pair ends up consumed first
    for j in (0..HEAD_CHUNKS).rev() {
        w.push(head_sigs[j].clone());
        w.push(snum(chunk_value(head, j)));
    }
    w.extend(wots_wire(sig));
    w
}

/// The disprove witness: the re-commitment reveal alone.
pub fn disprove_witness(sig: &WotsSig) -> Vec<Vec<u8>> {
    wots_wire(sig)
}

// ----- the two-head refutation (D35, plan 5.1 option (a)) -----

/// The Winternitz parameters of a PAIR refute key: the refutation at depth
/// `d >= 2` re-commits `head(d-1) || head(d)` (the prior state lives in the
/// previous slot's head — the tuple (state, move, state') spans two slots).
pub fn pair_params() -> WotsParams {
    WotsParams::for_bytes(2 * HEAD_BYTES as u32)
}

/// A pair refute key from entropy. (In the graph: the mover's, one per
/// depth, pinned at open; the label-disciplined derivation is in
/// `crate::instance`.)
pub fn pair_key(entropy: [u8; 32]) -> WotsSecret {
    WotsSecret::from_entropy(pair_params(), entropy)
}

/// The two-head refutation leaf: the pair key's re-commitment of
/// `head(d-1) || head(d)`, each of the 192 re-committed digits tied
/// nibble-equal to the readout of that head's chunks — the prior head's
/// under slot `d-1`'s table, the new head's under slot `d`'s. The heads'
/// slots are bound by the epoch tables (epoch = slot); no covenant needed.
/// Witness (consumption order): the pair reveal, then the prior head's
/// chunk items ascending, then the new head's.
pub fn refute_leaf_pair(table_prev: &EpochTable, table: &EpochTable, key: &WotsPublic) -> ScriptBuf {
    refute_leaf_pair_gated(table_prev, table, key, |b| b)
}

/// [`refute_leaf_pair`] with a GATE over the re-committed digits: `gate`
/// runs on the register file (the 192 message digits, digit `j` at stack
/// depth `191 - j`) right after the re-commitment verify, before the
/// readout ties the digits to the attestation. The conjunction is
/// order-free — a digit that fails the readout was never the attested
/// value — so the gate's verdict over the file is a verdict over the
/// attested pair. (The terminal exhibit, D37: the gate is
/// `status != OPEN` on the new head, so the leaf fires only on a finished
/// game.)
pub fn refute_leaf_pair_gated(
    table_prev: &EpochTable,
    table: &EpochTable,
    key: &WotsPublic,
    gate: impl FnOnce(Builder) -> Builder,
) -> ScriptBuf {
    let mut b = gate(Builder::new().wots_verify(key));
    // the re-committed digits to the altstack (d_0 comes out first)
    for _ in 0..2 * HEAD_CHUNKS {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    // the prior head's chunks tie to digits 0..HEAD_CHUNKS
    for j in HEAD_CHUNK_START..HEAD_CHUNK_START + HEAD_CHUNKS {
        b = readout_value_fragment(b, &table_prev.points[j]);
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_EQUALVERIFY);
    }
    // then the new head's tie to digits HEAD_CHUNKS..
    for j in HEAD_CHUNK_START..HEAD_CHUNK_START + HEAD_CHUNKS {
        b = readout_value_fragment(b, &table.points[j]);
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_EQUALVERIFY);
    }
    b.push_int(1).into_script()
}

/// The two-head refutation witness, wire order: the NEW head's chunk items
/// (descending), then the PRIOR head's (descending — its chunk 0 is consumed
/// first after the reveal), then the pair reveal. `sigs_prev`/`sigs` must
/// sign the spend's sighash under the two slots' tables' head-chunk points.
pub fn refute_witness_pair(
    head_prev: &[u8; HEAD_BYTES],
    sigs_prev: &[Vec<u8>],
    head: &[u8; HEAD_BYTES],
    sigs: &[Vec<u8>],
    sig: &WotsSig,
) -> Vec<Vec<u8>> {
    assert_eq!(sigs_prev.len(), HEAD_CHUNKS);
    assert_eq!(sigs.len(), HEAD_CHUNKS);
    let mut w = Vec::with_capacity(4 * HEAD_CHUNKS + 2 * sig.params.total_digits() as usize);
    for j in (0..HEAD_CHUNKS).rev() {
        w.push(sigs[j].clone());
        w.push(snum(chunk_value(head, j)));
    }
    for j in (0..HEAD_CHUNKS).rev() {
        w.push(sigs_prev[j].clone());
        w.push(snum(chunk_value(head_prev, j)));
    }
    w.extend(wots_wire(sig));
    w
}
