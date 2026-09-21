//! The chess disprove family over the parked tuple (POS_FACTCHAIN_PLAN.md
//! step 7's chess port — the PC-suite gap; D42).
//!
//! A chess venue entry's head uses all 48 bytes: `word0 || move<<16 ||
//! state` (the 40-byte [`ChessState::to_e`], the same encoding chess-fc's
//! PoW entries carry — the head IS the PoW entry's first 48 bytes). After a
//! refutation at depth `d` the parked register file is the pair
//! `head(d-1) || head(d)` exactly as in tic-tac-toe (192 digits, the prior
//! head at 0..96, the new at 96..192), so the chess state regions sit at
//! digits 16..96 (prior) and 112..192 (new) — and the whole
//! [`lngap_chess::leaf`] machinery rides over the pair UNCHANGED, because
//! `leaf_over_registers` is parameterized by the register offsets:
//! `Registers { n_nibbles: 192, e_off: 112, e2_off: 16 }`. The family is
//! `wrong_slot` (ttt's — word0's layout is the venue's, not the game's)
//! plus the twelve challenge kinds (all but `MoveNumber`, which the venue
//! state does not carry — same set as the PoW graph's).
//!
//! Depth 1 has no slot-0 head: the disprove leaves push the 96 constant
//! nibbles of [`initial_head`] right after the 96-digit re-commitment
//! verify, so the kinds still see a 192-nibble file — with the REVERSED
//! layout (the attested head at digits 0..96, the constant prior at
//! 96..192): `Registers { n_nibbles: 192, e_off: 16, e2_off: 112 }`.
//! `wrong_slot` at depth 1 needs no pad (it reads only the new head's
//! word0), same as ttt's.
//!
//! What this port does NOT have (D42):
//!
//! - No status gate and no terminal-exhibit family. Chess terminality is
//!   not a field (mate/stalemate = move-existence, not Script-computable),
//!   and it is not needed: mate at depth `t` leaves the mated side with no
//!   legal move, so the absence claim at `t + 1` is unanswerable (any
//!   refutation attempt is an illegal transition and is disproved) and
//!   races ahead of any dead-depth false claim at `t + 2`. The last-depth
//!   corner is excluded by chess-fc's standing assumption that the game
//!   ends before `w_max`, and interior draws do not exist under the PoC's
//!   stalemate-loses-by-stall reading (chess-fc's deferral) — so D37's
//!   interior-draw DUAL exhibit is moot here.
//! - The checked split's resolution is then trivial: `R(s) = side-to-move
//!   forfeits`, read off the parked new state's side nibble (state byte
//!   32's low nibble = head digit 81). Open state: the claimant is to
//!   move and forfeits. Mate: the mated (to-move) side loses. A stalemate
//!   loses the same way, consistent with the PoC reading. `code ==
//!   1 - side`, so the Draw split can never fire on this graph — draws
//!   remain cooperative-only.
//! - word1 (the duplicated move) and the state depth byte are NOT checked
//!   in-script: the family judges `(prior position, move, position')` with
//!   the move read from the new head's state bytes 36..38; word1 is venue
//!   indexing commentary. (chess-fc's entry decode still cross-checks it
//!   for clients.)
//!
//! The D41 authorship fragment is over chess's SIGNED_BITS = 336 (the state
//! bits, then the move's 16 bits — the chess-fc `places()` mapping), so the
//! mover's per-depth state key is 336 Lamport bits and the D39 equivocation
//! family is per (depth, signed bit).
//!
//! The native mirrors decode the parked heads and re-run the certificate
//! search (`find_kind`), the same oracle the chess-fc test suite uses; they
//! are defined on WELL-FORMED encodings. A malformed-but-attested state
//! (out-of-range nibble values) may evade every kind — inherited from
//! D30's PoW leaves verbatim — but such a head is attributable (the
//! authorship gate binds it to its mover) and its refuted output is stuck
//! (no disprove fires, the `1 - side` split cannot fire): the mover who
//! parks it self-griefs the pot.

use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::Leaf;
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_chess::certificate::find_kind;
use lngap_chess::leaf::{leaf_over_registers, Kind, Registers};
use lngap_chess_fc::{ChessState, SIGNED_BITS, STATE_BYTES};
use lngap_factchain::HEAD_BYTES;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_lamport::PublicKey;

use crate::ttt::{self, Layout, PosLeaf};

/// Head digits per parked head.
const HD: usize = HEAD_BYTES * 2; // 96
/// Head digit where the 40-byte state region starts (word0, word1 precede).
const SD: usize = 16;

/// The 48-byte head of a chess venue entry: `word0 || move<<16 || state`.
/// (chess-fc's entry head, byte-identical.)
pub fn head(game_id: u16, depth: u8, mover: Role, state: &ChessState) -> [u8; HEAD_BYTES] {
    let mut h = [0u8; HEAD_BYTES];
    h[0..4].copy_from_slice(&ttt::word0(game_id, u32::from(depth), mover).to_be_bytes());
    h[4..8].copy_from_slice(&(u32::from(state.mv.to_u16()) << 16).to_be_bytes());
    h[8..48].copy_from_slice(&state.to_e());
    h
}

/// The constant head(0): depth 0, the null move, the start position. The
/// mover byte is the depth-0 parity mover (hub); no leaf reads it
/// (`wrong_slot` skips the constant prior at depth 1).
pub fn initial_head(game_id: u16) -> [u8; HEAD_BYTES] {
    head(game_id, 0, Role::Hub, &ChessState::initial())
}

/// The 96 constant digits of `head` (high nibble first) — the depth-1
/// disprove leaves' padded prior file.
fn pad(head: &[u8; HEAD_BYTES]) -> [i64; HD] {
    let mut out = [0i64; HD];
    for (i, b) in head.iter().enumerate() {
        out[2 * i] = i64::from(b >> 4);
        out[2 * i + 1] = i64::from(b & 15);
    }
    out
}

/// The register layout the twelve kinds see at this layout, plus the
/// constant prior pad to push after the re-commitment verify (depth 1
/// only). See the module docs for the two layouts.
fn registers(l: &Layout) -> (Registers, Option<[i64; HD]>) {
    match l.prior {
        Some(_) => (Registers { n_nibbles: 2 * HD, e_off: HD + SD, e2_off: SD }, None),
        None => (Registers { n_nibbles: 2 * HD, e_off: SD, e2_off: HD + SD }, Some(pad(&initial_head(l.game_id)))),
    }
}

/// The challenge kinds the family covers (all but the move number, which
/// the venue state does not carry) — chess-fc's set.
pub fn kinds() -> Vec<Kind> {
    Kind::ALL.into_iter().filter(|k| *k != Kind::MoveNumber).collect()
}

/// The leaf name of a kind (chess-fc's convention).
pub fn leaf_name(kind: Kind) -> String {
    format!("chess_{}", format!("{kind:?}").to_lowercase())
}

/// Decode a parked head's state region.
fn state_of_head(h: &[u8; HEAD_BYTES]) -> anyhow::Result<ChessState> {
    ChessState::from_e(h[8..8 + STATE_BYTES].try_into().unwrap())
}

/// The disprove family for the refuted output at this layout: `wrong_slot`
/// (ttt's) then the twelve kinds over the register file, each with its
/// native mirror.
pub fn disprove_leaves(l: &Layout, key: &WotsPublic) -> Vec<PosLeaf> {
    let mut v = vec![ttt::wrong_slot(l, key)];
    for kind in kinds() {
        v.push(kind_leaf(l, key, kind));
    }
    v
}

/// One kind's leaf: the re-commitment verify (then the constant prior pad
/// at depth 1), then the chess body over the registers. The witness is the
/// pair reveal over the exhibit (the exhibit elements are deepest — see
/// [`disprove_witness`]).
fn kind_leaf(l: &Layout, key: &WotsPublic, kind: Kind) -> PosLeaf {
    let (regs, pad) = registers(l);
    let mut b = Builder::new().wots_verify(key);
    if let Some(p) = &pad {
        for &c in p.iter() {
            b = b.push_int(c);
        }
    }
    let script = leaf_over_registers(b, kind, regs);
    let has_prior = l.prior.is_some();
    PosLeaf {
        name: leaf_name(kind),
        script,
        fires: Arc::new(move |p, h| {
            let prior = if has_prior { state_of_head(p) } else { Ok(ChessState::initial()) };
            let (Ok(pr), Ok(af)) = (prior, state_of_head(h)) else { return false };
            find_kind(&pr.pos, af.mv, &af.pos, kind).is_some()
        }),
    }
}

// ----- the authorship fragment (D41, chess bit mapping) ----

/// Signed bit `i`'s home in a head: (head digit, nibble bit 0..4). The
/// state's bits first (`lngap_chess_fc::ChessEntry::signed_bits`): bit `i`
/// is bit `i % 8` (least significant first) of state byte `i / 8` — head
/// byte `8 + i / 8`. Then the move's 16 bits, low byte first: bit `t` at
/// head byte `5 - t / 8` (chess-fc's `places()`), bit `t % 8`. Byte `b`'s
/// low nibble (bits 0..4) is head digit `2b + 1`, its high nibble digit
/// `2b`.
fn place(i: usize) -> (usize, usize) {
    let (byte, j) = if i < 8 * STATE_BYTES { (8 + i / 8, i % 8) } else { (5 - (i - 8 * STATE_BYTES) / 8, (i - 8 * STATE_BYTES) % 8) };
    if j < 4 { (2 * byte + 1, j) } else { (2 * byte, j - 4) }
}

/// The chess authorship fragment: per parked head, the 336 preimages of
/// THAT head's mover's state key, each opening the commitment of the bit
/// value the head's claimed state||move has at that bit. Identical in
/// shape to ttt's (whose docs apply), differing only in the bit mapping
/// and count; ~19 kvB of script per head where ttt's is ~1.9.
pub fn authorship_fragment(mut b: Builder, file: usize, head_off: usize, key: &PublicKey) -> Builder {
    assert_eq!(key.bits.len(), SIGNED_BITS, "a chess state key is {SIGNED_BITS} bits");
    for i in 0..SIGNED_BITS {
        let (dig, bit) = place(i);
        let d = head_off + dig; // the file digit holding signed bit i
        b = b.push_int(file as i64).push_opcode(OP_ROLL).push_opcode(OP_HASH160); // [.. H(p_i)]
        b = b.push_int((file - d) as i64).push_opcode(OP_PICK); // [.. H(p_i), digit] (shifted one deep by H)
        b = ttt::nib_bit(b, bit); // [.. H(p_i), bit]
        b = b
            .push_opcode(OP_IF)
            .push_bytes(&key.bits[i].h1)
            .push_opcode(OP_ELSE)
            .push_bytes(&key.bits[i].h0)
            .push_opcode(OP_ENDIF) // [.. H(p_i), h_b]
            .push_opcode(OP_EQUALVERIFY);
    }
    b
}

// ----- the self-checking split (the refuted output's mover splits) ----

/// The new state's side nibble's file digit: state byte 32's low nibble =
/// head digit `16 + 65` = 81.
const SIDE_DIGIT: usize = SD + 65;

/// The chess resolution fragment: R(parked new state) is "side to move
/// forfeits" — `code == 1 - side` (side 0 = white to move pays hub,
/// outcome 1; side 1 = black to move pays user, outcome 0). No branch, no
/// terminal case: mate is the side-to-move losing, stalemate is the same
/// under the PoC reading, and an open state forfeits the claimant. The
/// Draw split can never satisfy the check (R is never 2 here) — draws are
/// cooperative-only on this graph.
pub fn resolution_fragment(mut b: Builder, file: usize, new_off: usize, code: u8) -> Builder {
    let d = file - 1 - (new_off + SIDE_DIGIT);
    b = b.push_int(d as i64).push_opcode(OP_PICK); // [.., side]
    b = b
        .push_int(1)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_SUB) // 1 - side
        .push_int(i64::from(code))
        .push_opcode(OP_NUMEQUALVERIFY);
    b
}

/// The self-checking split leaf of the refuted output at this layout: the
/// chess analogue of ttt's (`ttt::checked_split_leaf`'s docs apply): after
/// `delta + delta'` the mover splits by its revealed outcome code, the leaf
/// proving `code == R(parked new state)` in-leaf. The witness is ttt's
/// (`ttt::checked_split_witness`), unchanged.
pub fn checked_split_leaf(
    ctx: &CommitCtx,
    l: &Layout,
    o: &lngap_contract::Outcome,
    csv: u16,
    code: &PublicKey,
    key: &WotsPublic,
) -> Leaf {
    use lngap_lamport::gadgets::LamportExt;
    let mut b = Builder::new().csv(csv);
    b = ctx.two_of_two_verify(b);
    b = b.expect_uint(code, u32::from(o.code));
    b = b.wots_verify(key);
    b = resolution_fragment(b, l.file, l.new, o.code);
    for _ in 0..l.file / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    Leaf::new(
        format!("split_{}", o.name),
        b.push_int(1).into_script(),
        Timelock::csv(csv),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The bit mapping agrees with chess-fc's `places()` and the head's
    /// nibble order, on the values the encoding actually produces.
    #[test]
    fn place_matches_the_entry_layout() {
        // state bit 0 is the low bit of head byte 8 = digit 17, bit 0
        assert_eq!(place(0), (17, 0));
        // state bit 4 is the low bit of the high nibble of byte 8 = digit 16
        assert_eq!(place(4), (16, 0));
        // state bit 319: byte 47, bit 7 -> digit 94, nibble bit 3
        assert_eq!(place(319), (94, 3));
        // move bit 0: byte 5 bit 0 -> digit 11, nibble bit 0
        assert_eq!(place(320), (11, 0));
        // move bit 8: byte 4 bit 0 -> digit 9
        assert_eq!(place(328), (9, 0));
        // move bit 15: byte 4 bit 7 -> digit 8, nibble bit 3
        assert_eq!(place(335), (8, 3));
    }

    /// The initial head's pad decodes back to the initial state, and the
    /// side digit sits where the resolution fragment reads it.
    #[test]
    fn initial_head_round_trip() {
        let h = initial_head(7);
        let s = state_of_head(&h).unwrap();
        assert_eq!(s, ChessState::initial());
        let p = pad(&h);
        // the side nibble (white = 0) at head digit 81
        assert_eq!(p[SIDE_DIGIT], 0);
        // word0 carries (game 7, depth 0): digits 0..4 = 0x0007
        assert_eq!(&p[0..4], &[0, 0, 0, 7]);
    }
}
