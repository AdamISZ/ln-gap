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

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;

use crate::EpochTable;

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
