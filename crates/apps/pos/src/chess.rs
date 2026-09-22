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
//!   refutation attempt is an illegal transition and is disproved), and a
//!   dead-depth false claim at `t + 2` by the mated side is countered
//!   (D44: the winner's counter "you did not move at `t + 1`" is true and
//!   unrefutable — no race on CLTV order). The last-depth
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
//! - The family judges `(prior position, move, position')` with the move
//!   read from the new head's state bytes 36..38; word1 (the duplicated
//!   move) and the state's depth byte are venue indexing, pinned by
//!   `chess_malformed` (D45) to the state's move and the layout's depth so
//!   that chess-fc's entry decode (which cross-checks both) never rejects
//!   an entry the chain upholds.
//!
//! The D41 authorship fragment covers chess's signed region (the state
//! bytes, then the move's two bytes — the D43 tied-WOTS form, 84 digits),
//! so the mover's per-depth state key is an 87-digit Winternitz key and
//! the D39 equivocation family is per depth (two full signatures convict).
//!
//! The native mirrors decode the parked heads and re-run the certificate
//! search (`find_kind`), the same oracle the chess-fc test suite uses; they
//! are defined on WELL-FORMED encodings. The family therefore ends with
//! `chess_malformed` (D45), the well-formedness leaf over the NEW head: it
//! fires on exactly the fields the native decoder rejects but no kind
//! judges — a from/to square byte >= 64 (which makes every kind's board
//! read ERROR, so no kind could fire: before D45 a signed entry with
//! from = 255 parked a state no disprove could touch while the `1 - side`
//! split still paid the mover), the castling byte's high nibble, state
//! byte 38's low nibble, the state's depth byte (pinned to the layout's
//! depth), a promotion code outside {0, N, B, R, Q}, and word1 (the move
//! duplicate the entry decode cross-checks — pinned nibble-wise to the
//! state's from/to/promotion). Board nibbles, the side, the en-passant
//! square and the castling low nibble are judged by `Board`, `Side`,
//! `EpField` and `CastlingField` already, and none of those errors on
//! garbage there. So every head the client's decoder rejects is
//! disprovable, and the judge's notion of a valid entry is a superset of
//! the client's — the client never has to claim absence over an entry
//! the chain would uphold.

use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::Leaf;
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_chess::certificate::find_kind;
use lngap_chess::leaf::{leaf_over_registers, Kind, Registers};
use lngap_chess_fc::{ChessState, STATE_BYTES};
use lngap_factchain::HEAD_BYTES;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_lamport::PublicKey;

use crate::ttt::{self, Layout, Lb, PosLeaf, Src};

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
/// (ttt's), the twelve kinds over the register file, then
/// `chess_malformed` (D45), each with its native mirror.
pub fn disprove_leaves(l: &Layout, key: &WotsPublic) -> Vec<PosLeaf> {
    let mut v = vec![ttt::wrong_slot(l, key)];
    for kind in kinds() {
        v.push(kind_leaf(l, key, kind));
    }
    v.push(malformed(l, key));
    v
}

/// The leaf name of the well-formedness leaf.
pub const MALFORMED: &str = "chess_malformed";

/// Is the head malformed in a way no kind leaf judges (D45)? The native
/// mirror of [`malformed`]'s script, field for field: from/to square bytes
/// (state bytes 36, 37) >= 64; the castling byte's (33) high nibble; state
/// byte 38's low nibble; the depth byte (39) != `depth`; a promotion code
/// (byte 38's high nibble) of 1 or >= 6; word1 (head bytes 4..8) != the
/// move's `to_u16() << 16` rebuilt from the state's from/to/promotion.
pub fn is_malformed(h: &[u8; HEAD_BYTES], depth: u32) -> bool {
    let s = &h[8..48];
    let (from, to, promo) = (s[36], s[37], s[38] >> 4);
    // word1 nibble-wise, as the script compares it (the sums may exceed a
    // nibble when a square byte is out of range — then they simply differ)
    let d = |j: usize| u32::from(if j & 1 == 0 { h[j / 2] >> 4 } else { h[j / 2] & 15 });
    let w1_ok = d(8) == u32::from(promo)
        && d(9) == u32::from(to >> 2)
        && d(10) == u32::from((to & 3) << 2) + u32::from(from >> 4)
        && d(11) == u32::from(from & 15)
        && (12..16).all(|j| d(j) == 0);
    from >= 64 || to >= 64 || s[33] >> 4 != 0 || s[38] & 15 != 0 || u32::from(s[39]) != depth || promo == 1 || promo >= 6 || !w1_ok
}

/// `chess_malformed`: fires iff [`is_malformed`] holds for the parked NEW
/// head. Pure nibble arithmetic on the register file — it never errors, so
/// a head that makes the kinds' board reads fail still has a live
/// disprove. Gathers (deepest first): the depth byte's two digits, the
/// castling high nibble, byte 38's low nibble, the promotion nibble and
/// word1's digit 8, then from (hi, lo), to (hi, lo) and word1's digits
/// 9..11, then word1's digits 12..15; folds a BOOLOR accumulator from the
/// top down.
fn malformed(l: &Layout, key: &WotsPublic) -> PosLeaf {
    // head digit j of the new head at file digit n + j; state nibble k = head digit 16 + k
    let n = l.new;
    let sd = |k: usize| Src::Dig(n + SD + k);
    let hd = |j: usize| Src::Dig(n + j);
    let f = l.file;
    let mut lb = Lb::new(key);
    lb = lb.src(f, sd(78)).src(f, sd(79)); // depth hi, lo
    lb = lb.src(f, sd(66)).src(f, sd(77)); // castling hi, byte 38 lo
    lb = lb.src(f, sd(76)).src(f, hd(8)); // promo, word1 digit 8
    lb = lb.src(f, sd(72)).src(f, sd(73)).src(f, sd(74)).src(f, sd(75)); // from hi, lo, to hi, lo
    lb = lb.src(f, hd(9)).src(f, hd(10)).src(f, hd(11)); // word1 digits 9..11
    lb = lb.src(f, hd(12)).src(f, hd(13)).src(f, hd(14)).src(f, hd(15)); // word1 digits 12..15 (zero)
    let mut b = lb.restore();
    // [.., d12, d13, d14, d15]: the zero digits
    b = b.push_opcode(OP_0NOTEQUAL);
    for _ in 0..3 {
        b = b.push_opcode(OP_SWAP).push_opcode(OP_0NOTEQUAL).push_opcode(OP_BOOLOR);
    }
    // [.., fh, fl, th, tl, d9, d10, d11, acc]: the squares' range and word1's move digits
    b = b.push_int(7).push_opcode(OP_PICK).push_int(4).push_opcode(OP_GREATERTHANOREQUAL).push_opcode(OP_BOOLOR); // from >= 64
    b = b.push_int(5).push_opcode(OP_PICK).push_int(4).push_opcode(OP_GREATERTHANOREQUAL).push_opcode(OP_BOOLOR); // to >= 64
    b = b.push_opcode(OP_TOALTSTACK); // [fh, fl, th, tl, d9, d10, d11]
    b = b.push_int(5).push_opcode(OP_PICK).push_opcode(OP_NUMNOTEQUAL); // d11 != fl -> [fh, fl, th, tl, d9, d10, b]
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLOR).push_opcode(OP_TOALTSTACK); // [fh, fl, th, tl, d9, d10]
    b = b.push_int(2).push_opcode(OP_PICK); // [.., d9, d10, tl]
    b = ttt::split4(b); // [.., d9, d10, a, bb]  (tl = 4a + bb)
    b = b.push_opcode(OP_NIP).push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_DUP).push_opcode(OP_ADD); // [.., d9, d10, 4bb]
    b = b.push_int(6).push_opcode(OP_PICK).push_opcode(OP_ADD).push_opcode(OP_NUMNOTEQUAL); // d10 != 4bb + fh -> [fh, fl, th, tl, d9, b]
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLOR).push_opcode(OP_TOALTSTACK); // [fh, fl, th, tl, d9]
    b = b.push_int(1).push_opcode(OP_PICK); // [.., d9, tl]
    b = ttt::split4(b).push_opcode(OP_DROP); // [.., d9, a]
    b = b.push_int(3).push_opcode(OP_PICK).push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_DUP).push_opcode(OP_ADD).push_opcode(OP_ADD); // [.., d9, 4th + a]
    b = b.push_opcode(OP_NUMNOTEQUAL); // [fh, fl, th, tl, b]
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLOR).push_opcode(OP_TOALTSTACK); // [fh, fl, th, tl]
    b = b.push_opcode(OP_2DROP).push_opcode(OP_2DROP).push_opcode(OP_FROMALTSTACK); // [.., promo, d8, acc]
    // the promotion code's validity and word1's digit 8
    b = b.push_opcode(OP_TOALTSTACK).push_opcode(OP_SWAP).push_opcode(OP_DUP); // [d8, promo, promo]
    b = b.push_int(1).push_opcode(OP_NUMEQUAL).push_opcode(OP_OVER).push_int(6).push_opcode(OP_GREATERTHANOREQUAL).push_opcode(OP_BOOLOR); // [d8, promo, bad]
    b = b.push_opcode(OP_ROT).push_opcode(OP_ROT).push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_BOOLOR); // [bad']
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_BOOLOR); // [dep_hi, dep_lo, cast_hi, b38_lo, acc]
    for _ in 0..2 {
        b = b.push_opcode(OP_SWAP).push_opcode(OP_0NOTEQUAL).push_opcode(OP_BOOLOR);
    }
    // [dep_hi, dep_lo, acc]: the depth byte against the layout's constant
    b = b.push_opcode(OP_SWAP).push_int(i64::from(l.depth & 15)).push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_BOOLOR);
    b = b.push_opcode(OP_SWAP).push_int(i64::from(l.depth >> 4)).push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_BOOLOR);
    let depth = l.depth;
    PosLeaf {
        name: MALFORMED.into(),
        script: ttt::finish(b, 0, l.file),
        fires: Arc::new(move |_, h| is_malformed(h, depth)),
    }
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

// ----- the authorship fragment (D41; D43 tied-WOTS form) ----

/// The signed region's positions in the register file at this head offset.
/// Chess signs state||move (the chess-fc `places()` mapping, nibble-wise):
/// the 40 state bytes sit at head digits 16..96 (message digits 0..80),
/// then the move's two bytes low-byte-first (head bytes 5 then 4 — digits
/// 10, 11 then 8, 9).
pub fn authorship_positions(head_off: usize) -> [usize; 84] {
    let mut p = [0usize; 84];
    for (j, x) in p.iter_mut().enumerate() {
        *x = match j {
            0..=79 => head_off + 16 + j,
            80 => head_off + 10,
            81 => head_off + 11,
            82 => head_off + 8,
            _ => head_off + 9,
        };
    }
    p
}

/// The off-chain side of the same convention: the state key signs the
/// head's state bytes then the move (low byte first) — 42 bytes.
pub fn auth_message(head: &[u8; HEAD_BYTES]) -> Vec<u8> {
    let mut m = head[8..48].to_vec();
    m.push(head[5]);
    m.push(head[4]);
    m
}

/// The chess authorship fragment: per parked head, the mover's state-key
/// WOTS signature over the head's signed region, the message digits PICKed
/// off the register file (ttt's fragment docs apply — the D43 tied-WOTS
/// form). 84 message + 3 checksum digits where the Lamport form carried
/// 336 preimages (~9 kvB of script per head, ~30 KB); the pair refute's
/// stack budget relaxes by the same factor (the D42 new-head-only
/// narrowing is now a size choice, not a necessity).
pub fn authorship_fragment(b: Builder, file: usize, head_off: usize, key: &WotsPublic) -> Builder {
    assert_eq!(key.params.message_digits as usize, 84, "a chess state key covers the 42 signed bytes");
    b.wots_verify_tied(key, file, &authorship_positions(head_off))
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

    /// The authorship convention: the message bytes map to the in-script
    /// positions nibble-for-nibble (the tie only holds if they agree).
    #[test]
    fn auth_message_matches_positions() {
        let h = initial_head(7);
        let m = auth_message(&h);
        assert_eq!(m.len(), 42);
        let hd = pad(&h); // the head's digits
        let pos = authorship_positions(0);
        for (j, &p) in pos.iter().enumerate() {
            let want = lngap_lamport::winternitz::message_digits(&m)[j];
            assert_eq!(hd[p] as u8, want, "message digit {j} at file position {p}");
        }
    }
}
