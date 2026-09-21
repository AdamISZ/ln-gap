//! The on-chain half: the readout leaf and the equivocation slash leaf.
//!
//! The readout leaf proves (a) possession of one attestation secret per
//! message chunk — one OP_CHECKSIGVERIFY per chunk against the chunk's
//! selected anticipation point — and (b) that the attested message equals the
//! claimed message, nibble by nibble. What remains provable on-chain is then
//! "the attester attested this message": the values land on the stack as
//! verified nibbles, the project's standard witness format.
//!
//! Per-chunk fragment, with the stack shown bottom-to-top (witness enters as
//! [... c_j, sig_j, v_j], v_j on top):
//!
//! ```text
//!   <S_0> ... <S_15>          # [c, sig, v, S_0..S_15]        16 pushes
//!   OP_16 OP_PICK             # copy v_j:  [.., S_0..S_15, v]
//!   OP_15 OP_SWAP OP_SUB      # 15 - v
//!   OP_PICK                   # select S_v
//!   OP_18 OP_ROLL             # bring sig_j to the top
//!   OP_SWAP OP_CHECKSIGVERIFY # abort unless sig_j verifies under S_v
//!   OP_2DROP x8               # drop the sixteen points: [c, v]
//!   OP_EQUALVERIFY            # abort unless v == c: []
//! ```
//!
//! Wrong `v_j` selects a point whose secret the claimant does not hold and the
//! leaf aborts; OP_PICK's depth self-enforces the 0..=15 range, and an empty
//! signature fails at the VERIFY. After all chunks the stack is empty and the
//! leaf pushes OP_1.

use bitcoin::key::XOnlyPublicKey;
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;

use crate::EpochTable;

/// The readout fragment for one chunk position, leaving the attested value
/// on the stack: witness enters as `[.. sig_j, v_j]` (v_j on top), and after
/// the fragment the stack holds `[.., v_j]`. Unlike [`readout_leaf`] there is
/// no claimed value to equal — the values ARE the data (this is the form a
/// refutation composes: the venue-attested message accumulates on the stack).
pub fn readout_value_fragment(mut b: Builder, points: &[XOnlyPublicKey; 16]) -> Builder {
    for pt in points {
        b = b.push_slice(pt.serialize());
    }
    b = b
        .push_int(16)
        .push_opcode(OP_PICK) // copy v_j
        .push_int(15)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_SUB) // 15 - v_j
        .push_opcode(OP_PICK) // select S_{v_j}
        .push_int(18)
        .push_opcode(OP_ROLL) // bring sig_j to the top (region: v, 16 points, S_v above it)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_CHECKSIGVERIFY); // abort unless sig_j verifies under S_{v_j}
    for _ in 0..8 {
        b = b.push_opcode(OP_2DROP); // drop the sixteen points, keep v_j
    }
    b
}

/// The TIED form of [`readout_value_fragment`]: the value comes off the
/// ALTSTACK (the re-committed digit the composing leaf parked there), not
/// the witness — one witness element per chunk instead of two. Entering:
/// `[.., sig_j]` on the main stack, the chunk's value on the altstack top;
/// after the fragment the chunk is fully consumed (`[]` — there is no free
/// value: the value IS the parked digit, so the old form's closing
/// `OP_EQUALVERIFY` against the re-commitment is definitionally satisfied).
///
/// The soundness is unchanged: a digit that is not the attested value
/// selects an anticipation point whose secret the claimant does not hold,
/// and the leaf aborts at the CHECKSIGVERIFY. The tie to the parked message
/// is strengthened if anything — the attested value and the parked digit
/// are the same element, not two witnesses compared after the fact.
///
/// Per chunk: `FROMALTSTACK`, the 16 points, `OP_16 OP_PICK` (copy the
/// digit), `15 - v`, `OP_PICK` (select S_v), `OP_18 OP_ROLL` (the sig: the
/// stack carries no claimed value, so the same depth as the standalone
/// form), `OP_SWAP OP_CHECKSIGVERIFY`, then 8 x OP_2DROP (the points) and
/// OP_DROP (the digit — the standalone form leaves it for the caller's
/// EQUALVERIFY; here it IS the parked digit, nothing to compare).
pub fn readout_tied_fragment(mut b: Builder, points: &[XOnlyPublicKey; 16]) -> Builder {
    b = b.push_opcode(OP_FROMALTSTACK); // the chunk's value = the parked digit
    for pt in points {
        b = b.push_slice(pt.serialize());
    }
    b = b
        .push_int(16)
        .push_opcode(OP_PICK) // copy the digit
        .push_int(15)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_SUB) // 15 - v
        .push_opcode(OP_PICK) // select S_v
        .push_int(18)
        .push_opcode(OP_ROLL) // bring sig_j to the top
        .push_opcode(OP_SWAP)
        .push_opcode(OP_CHECKSIGVERIFY);
    for _ in 0..8 {
        b = b.push_opcode(OP_2DROP); // the sixteen points
    }
    b.push_opcode(OP_DROP) // the digit (it IS the parked digit — the tie is by construction)
}

/// A leaf reading out the chunk positions `chunks` of `table`: the attested
/// values land on the stack in range order, the last chunk's value on top.
/// Does NOT end with OP_1 — compose with whatever consumes the values.
pub fn readout_values_leaf(
    table: &EpochTable,
    chunks: std::ops::Range<usize>,
) -> ScriptBuf {
    let mut b = Builder::new();
    for j in chunks {
        b = readout_value_fragment(b, &table.points[j]);
    }
    b.into_script()
}

/// Witness args (wire order, bottom first) for [`readout_values_leaf`] over
/// `chunks`: per chunk in DESCENDING chunk order, `sig_j` then `v_j` (so the
/// lowest chunk's pair ends up on top and is consumed first). `sigs[k]` must
/// sign the spend's sighash under the point for the attested value of chunk
/// `chunks.start + k`.
pub fn readout_values_witness(
    msg: &[u8],
    chunks: std::ops::Range<usize>,
    sigs: &[Vec<u8>],
) -> Vec<Vec<u8>> {
    assert_eq!(sigs.len(), chunks.end - chunks.start);
    let mut out = Vec::with_capacity(2 * sigs.len());
    for k in (0..sigs.len()).rev() {
        out.push(sigs[k].clone());
        out.push(crate::snum(crate::chunk_value(msg, chunks.start + k)));
    }
    out
}

/// Script bytes per chunk of the readout leaf (16 point pushes + 20 opcodes).
pub const CHUNK_SCRIPT_BYTES: usize = 16 * 33 + 20;

/// The readout leaf for `table` (see the module docs). Consumes, per chunk,
/// the witness triple (v_j, sig_j, c_j) in that order.
pub fn readout_leaf(table: &EpochTable) -> ScriptBuf {
    let mut b = Builder::new();
    for j in 0..table.chunks {
        for pt in &table.points[j] {
            b = b.push_slice(pt.serialize());
        }
        b = b
            .push_int(16)
            .push_opcode(OP_PICK) // copy v_j
            .push_int(15)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_SUB) // 15 - v_j
            .push_opcode(OP_PICK) // select S_{v_j}
            .push_int(18)
            .push_opcode(OP_ROLL) // bring sig_j to the top
            .push_opcode(OP_SWAP)
            .push_opcode(OP_CHECKSIGVERIFY);
        for _ in 0..8 {
            b = b.push_opcode(OP_2DROP); // drop the sixteen points
        }
        b = b.push_opcode(OP_EQUALVERIFY); // v_j == c_j
    }
    b.push_int(1).into_script()
}

/// Witness args for a readout spend, in wire order (bottom of stack first),
/// as `lngap_btc::witness::tapscript_witness` expects. `sigs[j]` must be a
/// BIP340 signature over the spend's sighash under chunk j's point for the
/// *attested* value; the leaf checks the attested values against `claimed`.
pub fn readout_witness_args(
    table: &EpochTable,
    attested: &[u8],
    claimed: &[u8],
    sigs: &[Vec<u8>],
) -> Vec<Vec<u8>> {
    let n = table.chunks;
    assert_eq!(sigs.len(), n);
    assert_eq!(attested.len() * 2, n);
    assert_eq!(claimed.len() * 2, n);
    let mut out = Vec::with_capacity(3 * n);
    for j in (0..n).rev() {
        out.push(crate::snum(crate::chunk_value(claimed, j)));
        out.push(sigs[j].clone());
        out.push(crate::snum(crate::chunk_value(attested, j)));
    }
    out
}

/// The equivocation slash leaf: two possession proofs under two different
/// points at one chunk position — possible only if the attester attested two
/// values at position j of this epoch, i.e. equivocated.
pub fn slash_leaf(table: &EpochTable, j: usize, v: u8, v2: u8) -> ScriptBuf {
    assert!(v < 16 && v2 < 16 && v != v2);
    Builder::new()
        .push_slice(table.points[j][v as usize].serialize())
        .push_opcode(OP_CHECKSIGVERIFY)
        .push_slice(table.points[j][v2 as usize].serialize())
        .push_opcode(OP_CHECKSIGVERIFY)
        .push_int(1)
        .into_script()
}

/// Witness args for a slash spend, wire order. `sig_v` / `sig_v2` sign the
/// spend's sighash under the points for values `v` / `v2` respectively.
pub fn slash_witness_args(sig_v: Vec<u8>, sig_v2: Vec<u8>) -> Vec<Vec<u8>> {
    vec![sig_v2, sig_v]
}

/// The equivocation slash leaf, witness-parameterized form (D38): ONE leaf
/// per chunk position — the two values arrive in the witness — where
/// [`slash_leaf`] hardcodes a (v, v2) pair per leaf (120 leaves per chunk).
/// Two possession proofs under two DIFFERENT points at position `j` of this
/// epoch: possible only if the attester attested two values there, i.e.
/// equivocated on the epoch's message. (Two distinct fixed-length messages
/// differ at some chunk, so the chunk-level rule is complete for
/// message-level equivocation; and signing the SAME value twice opens the
/// same point — the `v != v2` check keeps that harmless.)
///
/// Witness (wire order, bottom first): `sig2 v2 sig1 v1` — v1 on top; the
/// sigs sign the spend's sighash under the points for v1 and v2.
pub fn slash_leaf_any(table: &EpochTable, j: usize) -> ScriptBuf {
    assert!(j < table.chunks);
    let mut b = Builder::new();
    for pt in &table.points[j] {
        b = b.push_slice(pt.serialize());
    }
    // stack enters [sig2, v2, sig1, v1, S_0..S_15]: v1 at depth 16, sig1 at 17
    b = b
        .push_int(16)
        .push_opcode(OP_PICK) // copy v1
        .push_int(15)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_SUB) // 15 - v1
        .push_opcode(OP_PICK) // select S_{v1}
        .push_int(18)
        .push_opcode(OP_ROLL) // sig1 to the top
        .push_opcode(OP_SWAP)
        .push_opcode(OP_CHECKSIGVERIFY); // abort unless sig1 verifies under S_{v1}
    // now [sig2, v2, v1, S_0..S_15]: v2 at depth 17, sig2 at 18
    b = b
        .push_int(17)
        .push_opcode(OP_PICK) // copy v2
        .push_int(15)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_SUB) // 15 - v2
        .push_opcode(OP_PICK) // select S_{v2}
        .push_int(19)
        .push_opcode(OP_ROLL) // sig2 to the top
        .push_opcode(OP_SWAP)
        .push_opcode(OP_CHECKSIGVERIFY); // abort unless sig2 verifies under S_{v2}
    // now [v2, v1, S_0..S_15]
    for _ in 0..8 {
        b = b.push_opcode(OP_2DROP);
    }
    // [v2, v1]: the two values must differ
    b.push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_VERIFY).push_int(1).into_script()
}

/// Witness args for [`slash_leaf_any`], wire order (bottom first).
/// `sig1` / `sig2` sign the spend's sighash under the points for values
/// `v1` / `v2` respectively.
pub fn slash_any_witness(sig1: Vec<u8>, v1: u8, sig2: Vec<u8>, v2: u8) -> Vec<Vec<u8>> {
    assert!(v1 < 16 && v2 < 16 && v1 != v2);
    vec![sig2, crate::snum(v2), sig1, crate::snum(v1)]
}
