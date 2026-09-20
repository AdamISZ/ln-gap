//! The tic-tac-toe disprove family over the parked tuple (D35's two-head
//! refutation; plan step 4b).
//!
//! After a refutation at depth `d`, the parked data is the mover's pair-key
//! re-commitment of `head(d-1) || head(d)` — the tuple (state, move, state')
//! spans two slots, so the disprove predicates read TWO heads from the
//! register file the pair key's `wots_verify` leaves: 192 message digits,
//! digit `j` at stack depth `191 - j`, the prior head at digits 0..96 and
//! the new head at 96..192. At depth 1 there is no move 0: the refutation
//! parks the single head (96 digits) and the prior state is the constant
//! initial board (all nibbles zero — leaves that can never fire are
//! dropped, the old graph's constant-prior discipline).
//!
//! Head digit layout (the 48-byte entry head; digit `j` = nibble `j`, high
//! nibble first). word0 = `game_id(2 BE) || depth(1) || mover(1)`, word1 =
//! `mv(1) || state(3 BE)`:
//!
//! - game id: digits 0..4; depth: 4, 5; mover: 6, 7; move: 8 (hi), 9 (lo)
//! - state nibble `k` (state bits `4k..4k+4`): digit `15 - k`
//! - cell `i` = bits `2i..2i+2`: nibble `i/2`; even `i` the low half
//! - turn = bit 18 (1 = hub): nibble 4, bit 2. status = bits 19..21:
//!   nibble 4 bit 3 (low) and nibble 5 bit 0 (high)
//!
//! The family: `wrong_slot` (either head's word0 not this game's constants
//! for its slot — catches an empty-slot head, a wrong-depth head, a
//! wrong-mover head), the prior-state predicates the single-head refutation
//! could not express (`prior_closed`, `not_on_turn`, `cell_occupied_i`),
//! `cell_out_of_range`, the `board_mismatch_i` set, `turn_not_flipped`, and
//! `status_mismatch`. The old family's `code_mismatch` does not port — a
//! PoS refutation carries no code reveal — and is replaced by the
//! SELF-CHECKING split on the refuted output ([`checked_split_leaf`]): the
//! mover's split proves `code == R(parked new state)` in-leaf, so a false
//! code cannot cash a legal refutation.
//!
//! Script discipline: each leaf gathers its inputs (digit picks, or
//! constants for the depth-1 prior) onto the altstack, restores them in
//! declaration order (first deepest), computes on the gathered block alone,
//! `OP_VERIFY`s the predicate, and drops the register file (cleanstack).
//! The sim tests (tests/sim_ttt.rs) run every leaf against its native
//! mirror over legal and illegal tuples; nothing is "measured" until spent
//! on regtest (tests/pos_graph.rs).

use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use lngap_btc::script::BuilderExt;
use lngap_channel::Role;
use lngap_factchain::slot::STATE_BITS;
use lngap_factchain::HEAD_BYTES;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_lamport::PublicKey;
use lngap_tictactoe::LINES;

/// Head chunk digits per head in the file.
const HD: usize = HEAD_BYTES * 2; // 96

/// The leaf family's constants: which game, which depth, who moved.
#[derive(Clone, Copy, Debug)]
pub struct Layout {
    /// Register-file digits: 96 (depth 1, single parked head) or 192.
    pub file: usize,
    /// The prior head's digit offset; `None` at depth 1 (constant prior).
    pub prior: Option<usize>,
    /// The new head's digit offset.
    pub new: usize,
    pub game_id: u16,
    pub depth: u32,
    pub mover: Role,
}

impl Layout {
    pub fn at(depth: u32, game_id: u16, mover: Role) -> Layout {
        Layout {
            file: if depth >= 2 { 2 * HD } else { HD },
            prior: (depth >= 2).then_some(0),
            new: if depth >= 2 { HD } else { 0 },
            game_id,
            depth,
            mover,
        }
    }
    /// File digit of new-head nibble `j`.
    fn ndig(&self, j: usize) -> usize {
        self.new + j
    }
    /// The prior state's nibble `k` (bits `4k..`): a file digit, or the
    /// constant 0 of the initial board at depth 1.
    fn pnib(&self, k: usize) -> Src {
        match self.prior {
            Some(off) => Src::Dig(off + 15 - k),
            None => Src::Konst(0),
        }
    }
    /// The new state's nibble `k`.
    fn nnib(&self, k: usize) -> Src {
        Src::Dig(self.ndig(15 - k))
    }
}

/// A gathered input: a file digit or a constant.
#[derive(Clone, Copy)]
enum Src {
    Dig(usize),
    Konst(i64),
}

/// A disprove leaf with its native mirror: `fires(prior_head, new_head)` is
/// the script's semantics for tests (the prior head is zeros at depth 1).
pub struct PosLeaf {
    pub name: String,
    pub script: ScriptBuf,
    pub fires: Arc<dyn Fn(&[u8; HEAD_BYTES], &[u8; HEAD_BYTES]) -> bool + Send + Sync>,
}

impl std::fmt::Debug for PosLeaf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PosLeaf({}, {} B)", self.name, self.script.len())
    }
}

/// The disprove family for the refuted output at this layout. Depth 1 drops
/// the prior-only leaves (they cannot fire on the initial board).
pub fn disprove_leaves(l: &Layout, key: &WotsPublic) -> Vec<PosLeaf> {
    let mut v = vec![wrong_slot(l, key), cell_out_of_range(l, key)];
    if l.prior.is_some() {
        v.push(prior_closed(l, key));
        v.push(not_on_turn(l, key));
        for i in 0..9 {
            v.push(cell_occupied(l, key, i));
        }
    }
    for i in 0..9 {
        v.push(board_mismatch(l, key, i));
    }
    v.push(turn_not_flipped(l, key));
    v.push(status_mismatch(l, key));
    v
}

// ----- native mirrors -----

fn w0_of(h: &[u8; HEAD_BYTES]) -> u32 {
    u32::from_be_bytes(h[0..4].try_into().unwrap())
}
fn mv_of(h: &[u8; HEAD_BYTES]) -> u8 {
    h[4]
}
fn state_of(h: &[u8; HEAD_BYTES]) -> u32 {
    u32::from_be_bytes(h[4..8].try_into().unwrap()) & 0x00ff_ffff
}
fn cell(s: u32, i: usize) -> u32 {
    (s >> (2 * i)) & 3
}
fn turnbit(s: u32) -> u32 {
    (s >> 18) & 1
}
fn status(s: u32) -> u32 {
    (s >> 19) & 3
}
fn wins(s: u32, m: u32) -> bool {
    LINES.iter().any(|l| l.iter().all(|&i| cell(s, i) == m))
}
fn full(s: u32) -> bool {
    (0..9).all(|i| cell(s, i) != 0)
}
/// The mover's mark in a cell (X = 1, O = 2).
fn mark(r: Role) -> u32 {
    match r {
        Role::User => 1,
        Role::Hub => 2,
    }
}
/// The status code of a mover win (X_WON = 1, O_WON = 2).
fn mover_status(r: Role) -> u32 {
    mark(r)
}
/// R(s): the outcome code — terminal result, else the party on turn
/// forfeits. (The refuted output's resolution: `mover` moved at `depth`,
/// so an open state pays the mover.)
pub fn resolution(s: u32) -> u32 {
    let st = status(s);
    if st != 0 { st - 1 } else { 1 - turnbit(s) }
}
/// word0 as the venue entry packs it.
pub fn word0(game_id: u16, depth: u32, mover: Role) -> u32 {
    (u32::from(game_id) << 16) | ((depth as u32) << 8) | mover.idx() as u32
}

// ----- script gadgets -----

/// [v] -> [hi, lo]: v a nibble, v = 4*hi + lo. (No OP_DIV/OP_MUL in Script.)
fn split4(b: Builder) -> Builder {
    b.push_opcode(OP_DUP)
        .push_int(8)
        .push_opcode(OP_GREATERTHANOREQUAL) // v a
        .push_opcode(OP_SWAP)
        .push_opcode(OP_OVER) // a v a
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD)
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD)
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // a v 8a
        .push_opcode(OP_SUB) // a w
        .push_opcode(OP_DUP)
        .push_int(4)
        .push_opcode(OP_GREATERTHANOREQUAL) // a w b
        .push_opcode(OP_SWAP)
        .push_opcode(OP_OVER) // a b w b
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD)
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // a b w 4b
        .push_opcode(OP_SUB) // a b lo
        .push_opcode(OP_ROT) // b lo a
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // b lo 2a
        .push_opcode(OP_ROT) // lo 2a b
        .push_opcode(OP_ADD) // lo hi
        .push_opcode(OP_SWAP) // hi lo
}

/// [u] -> [b_hi, b_lo]: u in 0..=3.
fn split2(b: Builder) -> Builder {
    b.push_opcode(OP_DUP)
        .push_int(2)
        .push_opcode(OP_GREATERTHANOREQUAL) // u f
        .push_opcode(OP_SWAP)
        .push_opcode(OP_OVER) // f u f
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // f u 2f
        .push_opcode(OP_SUB) // f u-2f
}

/// [nib] -> [cell]: the cell in the nibble's low half (even i).
fn cell_lo(b: Builder) -> Builder {
    split4(b).push_opcode(OP_NIP)
}
/// [nib] -> [cell]: the cell in the nibble's high half (odd i).
fn cell_hi(b: Builder) -> Builder {
    split4(b).push_opcode(OP_DROP)
}
/// [nib4] -> [turn bit] (bit 2).
fn turn_of(b: Builder) -> Builder {
    let b = split4(b).push_opcode(OP_DROP); // hi2
    split2(b).push_opcode(OP_NIP) // b2
}
/// [nib4] -> [status low bit] (bit 3).
fn bit3(b: Builder) -> Builder {
    let b = split4(b).push_opcode(OP_DROP); // hi2
    split2(b).push_opcode(OP_DROP) // b3
}
/// [nib5] -> [status high bit] (bit 0).
fn bit0(b: Builder) -> Builder {
    let b = split4(b).push_opcode(OP_NIP); // lo2
    split2(b).push_opcode(OP_NIP) // b0
}

// ----- the leaf builder -----

/// Gathers inputs onto the altstack (nothing above the file during the
/// gather, so pick depths are `file - 1 - j`), restores them in declaration
/// order, then the hand-written compute tail runs on the gathered block.
struct Lb {
    b: Builder,
    gathered: usize,
}

impl Lb {
    fn new(key: &WotsPublic) -> Lb {
        Lb { b: Builder::new().wots_verify(key), gathered: 0 }
    }
    fn src(mut self, file: usize, s: Src) -> Lb {
        self.b = match s {
            Src::Dig(j) => {
                let depth = file - 1 - j;
                self.b.push_int(depth as i64).push_opcode(OP_PICK)
            }
            Src::Konst(v) => self.b.push_int(v),
        }
        .push_opcode(OP_TOALTSTACK);
        self.gathered += 1;
        self
    }
    /// The gathered block onto the main stack, first-gathered deepest.
    fn restore(mut self) -> Builder {
        for _ in 0..self.gathered {
            self.b = self.b.push_opcode(OP_FROMALTSTACK);
        }
        for i in 1..self.gathered {
            self.b = self.b.push_int(i as i64).push_opcode(OP_ROLL);
        }
        self.b
    }
}

/// `OP_VERIFY` the predicate, drop `leftover` gathered items plus the whole
/// register file, push OP_1 (cleanstack).
fn finish(mut b: Builder, leftover: usize, file: usize) -> ScriptBuf {
    b = b.push_opcode(OP_VERIFY);
    let mut n = leftover;
    if n % 2 == 1 {
        b = b.push_opcode(OP_DROP);
        n -= 1;
    }
    for _ in 0..(n + file) / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    b.push_int(1).into_script()
}

/// word0's 8 nibbles (game_id 2 BE bytes, depth, mover), most significant
/// first, as the head's digits 0..8 hold them.
fn word0_nibbles(game_id: u16, depth: u32, mover: Role) -> [i64; 8] {
    let w = word0(game_id, depth, mover);
    (0..8)
        .map(|i| ((w >> (4 * (7 - i))) & 15) as i64)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

/// `wrong_slot`: fires iff either parked head's word0 is not this game's
/// constant for its slot ((game, d-1, claimant) / (game, d, mover)). An
/// empty slot's zero head fails the game id; a wrong-depth or wrong-mover
/// entry fails its byte. (The venue's signature checks are the sig
/// exhibit's domain, deferred — this leaf binds only the head's own
/// claiming fields.)
fn wrong_slot(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut lb = Lb::new(key);
    let mut expects: Vec<i64> = Vec::new();
    if l.prior.is_some() {
        expects.extend(word0_nibbles(l.game_id, l.depth - 1, l.mover.other()));
    }
    expects.extend(word0_nibbles(l.game_id, l.depth, l.mover));
    let n = expects.len();
    if let Some(p) = l.prior {
        for j in 0..8 {
            lb = lb.src(l.file, Src::Dig(p + j));
        }
    }
    for j in 0..8 {
        lb = lb.src(l.file, Src::Dig(l.ndig(j)));
    }
    let mut b = lb.restore();
 // mismatch accumulator: compare from the top of the gathered block
 // down, folding with BOOLOR (fires iff ANY nibble differs)
 for k in (0..n).rev() {
     if k < n - 1 {
         b = b.push_opcode(OP_SWAP);
     }
     b = b.push_int(expects[k]).push_opcode(OP_NUMNOTEQUAL);
     if k < n - 1 {
         b = b.push_opcode(OP_BOOLOR);
     }
 }
    let has_prior = l.prior.is_some();
    let depth = l.depth;
    let game_id = l.game_id;
    let mover = l.mover;
    PosLeaf {
        name: "wrong_slot".into(),
        script: finish(b, 0, l.file),
        fires: Arc::new(move |p, h| {
            (has_prior && w0_of(p) != word0(game_id, depth - 1, mover.other()))
                || w0_of(h) != word0(game_id, depth, mover)
        }),
    }
}

/// `prior_closed` (d >= 2): the game was already over before the move.
fn prior_closed(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let lb = Lb::new(key).src(l.file, l.pnib(4)).src(l.file, l.pnib(5));
    let mut b = lb.restore(); // [n4, n5]
    b = bit0(b); // [n4, b20]
    b = b.push_opcode(OP_SWAP); // [b20, n4]
    b = bit3(b); // [b20, b19]
    b = b
        .push_opcode(OP_SWAP) // [b19, b20]
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // [b19, 2*b20]
        .push_opcode(OP_ADD) // [status]
        .push_opcode(OP_0NOTEQUAL);
    PosLeaf {
        name: "prior_closed".into(),
        script: finish(b, 0, l.file),
        fires: Arc::new(|p, _| status(state_of(p)) != 0),
    }
}

/// `not_on_turn` (d >= 2): the mover was not on turn in the prior state.
fn not_on_turn(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let lb = Lb::new(key).src(l.file, l.pnib(4));
    let mut b = lb.restore(); // [n4]
    b = turn_of(b); // [t]
    if l.mover == Role::Hub {
        b = b.push_opcode(OP_NOT);
    }
    let mover = l.mover;
    PosLeaf {
        name: "not_on_turn".into(),
        script: finish(b, 0, l.file),
        fires: Arc::new(move |p, _| turnbit(state_of(p)) != (mover == Role::Hub) as u32),
    }
}

/// `cell_out_of_range`: mv > 8.
fn cell_out_of_range(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let lb = Lb::new(key).src(l.file, Src::Dig(l.ndig(8))).src(l.file, Src::Dig(l.ndig(9)));
    let mut b = lb.restore(); // [hi, lo]
    b = b
        .push_opcode(OP_SWAP) // [lo, hi]
        .push_opcode(OP_0NOTEQUAL) // [lo, hi != 0]
        .push_opcode(OP_SWAP) // [b1, lo]
        .push_int(8)
        .push_opcode(OP_GREATERTHAN) // [b1, lo > 8]
        .push_opcode(OP_BOOLOR);
    PosLeaf {
        name: "cell_out_of_range".into(),
        script: finish(b, 0, l.file),
        fires: Arc::new(|_, h| mv_of(h) > 8),
    }
}

/// `cell_occupied_i` (d >= 2): mv == i and the prior cell was taken.
fn cell_occupied(l: &Layout, key: &WotsPublic, i: usize) -> PosLeaf {
    let k = i / 2;
    let lb = Lb::new(key)
        .src(l.file, l.pnib(k))
        .src(l.file, Src::Dig(l.ndig(8)))
        .src(l.file, Src::Dig(l.ndig(9)));
    let mut b = lb.restore(); // [nib, hi, lo]
    b = b
        .push_int(i as i64)
        .push_opcode(OP_NUMEQUAL) // [nib, hi, lo == i]
        .push_opcode(OP_SWAP) // [nib, b, hi]
        .push_int(0)
        .push_opcode(OP_NUMEQUAL) // [nib, b, hi == 0]
        .push_opcode(OP_BOOLAND) // [nib, mvok]
        .push_opcode(OP_SWAP); // [mvok, nib]
    b = if i % 2 == 0 { cell_lo(b) } else { cell_hi(b) }; // [mvok, cell]
    b = b.push_opcode(OP_0NOTEQUAL).push_opcode(OP_BOOLAND);
    PosLeaf {
        name: format!("cell_occupied_{i}"),
        script: finish(b, 0, l.file),
        fires: Arc::new(move |p, h| mv_of(h) as usize == i && cell(state_of(p), i) != 0),
    }
}

/// `board_mismatch_i`: the new cell i is not (mv == i ? mark : prior i).
fn board_mismatch(l: &Layout, key: &WotsPublic, i: usize) -> PosLeaf {
    let k = i / 2;
    let lb = Lb::new(key)
        .src(l.file, l.nnib(k))
        .src(l.file, l.pnib(k))
        .src(l.file, Src::Dig(l.ndig(8)))
        .src(l.file, Src::Dig(l.ndig(9)));
    let mut b = lb.restore(); // [nibN, nibP, hi, lo]
    b = b
        .push_int(i as i64)
        .push_opcode(OP_NUMEQUAL) // [nibN, nibP, hi, lo == i]
        .push_opcode(OP_SWAP) // [nibN, nibP, b, hi]
        .push_int(0)
        .push_opcode(OP_NUMEQUAL) // [nibN, nibP, b, hi == 0]
        .push_opcode(OP_BOOLAND) // [nibN, nibP, mvok]
        .push_opcode(OP_SWAP); // [nibN, mvok, nibP]
    b = if i % 2 == 0 { cell_lo(b) } else { cell_hi(b) }; // [nibN, mvok, cellP]
    b = b
        .push_opcode(OP_SWAP) // [nibN, cellP, mvok]
        .push_opcode(OP_IF)
        .push_opcode(OP_DROP)
        .push_int(i64::from(mark(l.mover))) // played cell: the mover's mark
        .push_opcode(OP_ELSE)
        .push_opcode(OP_ENDIF); // [nibN, expected]
    b = b.push_opcode(OP_SWAP); // [expected, nibN]
    b = if i % 2 == 0 { cell_lo(b) } else { cell_hi(b) }; // [expected, cellN]
    b = b.push_opcode(OP_NUMNOTEQUAL);
    let mover = l.mover;
    PosLeaf {
        name: format!("board_mismatch_{i}"),
        script: finish(b, 0, l.file),
        fires: Arc::new(move |p, h| {
            let expected = if mv_of(h) as usize == i { mark(mover) } else { cell(state_of(p), i) };
            cell(state_of(h), i) != expected
        }),
    }
}

/// `turn_not_flipped`: the new turn equals the prior turn.
fn turn_not_flipped(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let lb = Lb::new(key).src(l.file, l.pnib(4)).src(l.file, l.nnib(4));
    let mut b = lb.restore(); // [np, nn]
    b = turn_of(b); // [np, tN]
    b = b.push_opcode(OP_SWAP); // [tN, np]
    b = turn_of(b); // [tN, tP]
    b = b.push_opcode(OP_NUMEQUAL);
    PosLeaf {
        name: "turn_not_flipped".into(),
        script: finish(b, 0, l.file),
        fires: Arc::new(|p, h| turnbit(state_of(p)) == turnbit(state_of(h))),
    }
}

/// `status_mismatch`: the new status is not (mover wins ? mover_status :
/// board full ? DRAW : OPEN), computed on the new cells.
fn status_mismatch(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut lb = Lb::new(key);
    for k in 0..6 {
        lb = lb.src(l.file, l.nnib(k));
    }
    let mut b = lb.restore(); // [n0, n1, n2, n3, n4, n5]
    // extract the 9 cells; cell i reads nibble n_{i/2} (block position i/2)
    for i in 0..9 {
        let depth = (5 - i / 2) + i; // i extracted cells sit above the block
        b = b.push_int(depth as i64).push_opcode(OP_PICK);
        b = if i % 2 == 0 { cell_lo(b) } else { cell_hi(b) };
    }
    // [n0..n5, c0..c8]: the win accumulator, then the line check
    let mk = i64::from(mark(l.mover));
    b = b.push_int(0);
    for line in LINES {
        b = b
            .push_int((8 - line[0] + 1) as i64)
            .push_opcode(OP_PICK)
            .push_int(mk)
            .push_opcode(OP_NUMEQUAL)
            .push_int((8 - line[1] + 2) as i64)
            .push_opcode(OP_PICK)
            .push_int(mk)
            .push_opcode(OP_NUMEQUAL)
            .push_opcode(OP_BOOLAND)
            .push_int((8 - line[2] + 2) as i64)
            .push_opcode(OP_PICK)
            .push_int(mk)
            .push_opcode(OP_NUMEQUAL)
            .push_opcode(OP_BOOLAND)
            .push_opcode(OP_BOOLOR);
    }
    // the full accumulator
    b = b.push_int(1);
    for i in 0..9 {
        b = b
            .push_int((8 - i + 2) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_BOOLAND);
    }
    // [n0..n5, c0..c8, win, full] -> expected
    b = b
        .push_opcode(OP_SWAP)
        .push_opcode(OP_IF)
        .push_opcode(OP_DROP)
        .push_int(i64::from(mover_status(l.mover)))
        .push_opcode(OP_ELSE)
        .push_opcode(OP_IF)
        .push_int(3) // DRAW
        .push_opcode(OP_ELSE)
        .push_int(0) // OPEN
        .push_opcode(OP_ENDIF)
        .push_opcode(OP_ENDIF);
    // [n0..n5, c0..c8, expected]: the attested status from n4/n5
    b = b.push_int(11).push_opcode(OP_PICK); // n4 (16 above the file)
    b = bit3(b); // [.., expected, b19]
    b = b.push_int(11).push_opcode(OP_PICK); // n5 (17 above the file now)
    b = bit0(b); // [.., expected, b19, b20]
    b = b
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // 2*b20
        .push_opcode(OP_ADD) // status
        .push_opcode(OP_NUMNOTEQUAL);
    let mover = l.mover;
    PosLeaf {
        name: "status_mismatch".into(),
        script: finish(b, 15, l.file),
        fires: Arc::new(move |_, h| {
            let s = state_of(h);
            let expected = if wins(s, mark(mover)) { mover_status(mover) } else if full(s) { 3 } else { 0 };
            status(s) != expected
        }),
    }
}

// ----- the authorship fragment (D41) -----

/// [nib] -> [bit `b` of the nibble] (b = 0 the low bit).
fn nib_bit(b: Builder, bit: usize) -> Builder {
    match bit {
        0 => split2(split4(b).push_opcode(OP_NIP)).push_opcode(OP_NIP), // lo2, lo
        1 => split2(split4(b).push_opcode(OP_NIP)).push_opcode(OP_DROP), // lo2, hi
        2 => split2(split4(b).push_opcode(OP_DROP)).push_opcode(OP_NIP), // hi2, lo
        _ => split2(split4(b).push_opcode(OP_DROP)).push_opcode(OP_DROP), // hi2, hi
    }
}

/// The authorship fragment (D41): the refutation/exhibit must present, per
/// parked head, the 21 preimages of THAT head's mover's state key, each
/// opening the commitment of the bit value the head's claimed state has at
/// that bit. "Standing behind a head" now requires the mover's key over
/// the head's state — which is playing the move. A garbage-signed attested
/// entry supports no refutation (its author alone holds the key, and the
/// venue never had it), so the absence path proceeds; the witness's
/// preimages ride in a block right below the register file and are ROLLed
/// off one by one (constant depth `file`).
///
/// Witness order: the fragment consumes the block top-first; per head the
/// preimages are checked bit-ascending, the NEW head's block first.
///
/// Runs on the file right after the re-commitment verify: the PICK copies
/// leave the file intact for the readout (the conjunction is order-free).
pub fn authorship_fragment(mut b: Builder, file: usize, head_off: usize, key: &PublicKey) -> Builder {
    for i in 0..STATE_BITS {
        let d = head_off + 15 - i / 4; // the file digit holding state bit i
        b = b.push_int(file as i64).push_opcode(OP_ROLL).push_opcode(OP_HASH160); // [.. H(p_i)]
        b = b.push_int((file - d) as i64).push_opcode(OP_PICK); // [.. H(p_i), digit] (shifted one deep by H)
        b = nib_bit(b, i % 4); // [.. H(p_i), bit]
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

// ----- the terminal exhibit's status gate (D37) -----

/// The terminal gate on the register file: require the parked NEW head's
/// status != OPEN (state bits 19..21 — nibble 4 bit 3, nibble 5 bit 0 of
/// the head's state word; file digits `new_off + 11` / `new_off + 10`).
/// Runs on the file right after the pair key's `wots_verify`, consuming
/// only the two picked copies — the file stays intact for the readout
/// (the conjunction is order-free: a digit that fails the readout was
/// never the attested value, so the gate judges the attested state).
///
/// The gate is what keeps the exhibit from being a mid-game self-claim
/// button: without it the exhibit fires on any attested OPEN state and
/// R(open) pays the mover who just moved. Terminality is read off the
/// state itself — the leaf never models when or why the game ended, so an
/// arbitrarily complex closure rule (checkmate, stalemate, move limits)
/// comes through the same two bits.
pub fn terminal_gate_fragment(mut b: Builder, file: usize, new_off: usize) -> Builder {
    let d4 = file - 1 - (new_off + 11); // n4's depth in the file
    let d5 = file - 1 - (new_off + 10); // n5's
    b = b.push_int(d4 as i64).push_opcode(OP_PICK); // [n4]
    b = b.push_int((d5 + 1) as i64).push_opcode(OP_PICK); // [n4, n5] (one deeper after the first pick)
    b = bit0(b); // [n4, b20]
    b = b.push_opcode(OP_SWAP); // [b20, n4]
    b = bit3(b); // [b20, b19]
    b
        .push_opcode(OP_SWAP) // [b19, b20]
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // [b19, 2*b20]
        .push_opcode(OP_ADD) // [status]
        .push_opcode(OP_0NOTEQUAL)
        .push_opcode(OP_VERIFY)
}

// ----- the self-checking split (the refuted output's mover splits) -----

/// The resolution fragment over the parked file: push R(new state) and
/// require it to equal `code`. Deletes the old family's `code_mismatch`
/// leaf: the mover's split carries the correctness proof itself. Consumes
/// nothing but picks; leaves the file plus the verified compare (empty).
pub fn resolution_fragment(mut b: Builder, file: usize, new_off: usize, code: u8) -> Builder {
    let d4 = file - 1 - (new_off + 11); // n4's depth
    let d5 = file - 1 - (new_off + 10); // n5's
    b = b.push_int(d4 as i64).push_opcode(OP_PICK); // [n4]
    b = b.push_int((d5 + 1) as i64).push_opcode(OP_PICK); // [n4, n5]
    b = b.push_int((d4 + 2) as i64).push_opcode(OP_PICK); // [n4, n5, n4']
    b = turn_of(b); // [n4, n5, turn]
    b = b.push_opcode(OP_SWAP); // [n4, turn, n5]
    b = bit0(b); // [n4, turn, b20]
    b = b.push_opcode(OP_ROT); // [turn, b20, n4]
    b = bit3(b); // [turn, b20, b19]
    b = b
        .push_opcode(OP_SWAP) // [turn, b19, b20]
        .push_opcode(OP_DUP)
        .push_opcode(OP_ADD) // [turn, b19, 2*b20]
        .push_opcode(OP_ADD) // [turn, status]
        .push_opcode(OP_DUP)
        .push_opcode(OP_0NOTEQUAL) // MINIMALIF: OP_IF takes a canonical bool
        .push_opcode(OP_IF)
        .push_int(1)
        .push_opcode(OP_SUB) // status - 1
        .push_opcode(OP_SWAP)
        .push_opcode(OP_DROP)
        .push_opcode(OP_ELSE)
        .push_opcode(OP_DROP) // turn
        .push_int(1)
        .push_opcode(OP_SWAP)
        .push_opcode(OP_SUB) // 1 - turn
        .push_opcode(OP_ENDIF) // [outcome]
        .push_int(i64::from(code))
        .push_opcode(OP_NUMEQUALVERIFY);
    b
}

/// The self-checking split leaf of the refuted output at this layout: after
/// `delta + delta'` the mover splits by its revealed outcome code — and the
/// leaf itself proves `code == R(parked new state)` (the register file is
/// public once the refutation spent). A legal refutation then resolves to
/// the mover (an open state forfeits the claimant); a false code fails
/// in-leaf. This is where the old family's `code_mismatch` lives on.
///
/// Witness: `<sig_hub> <sig_user>` over the code reveal over the pair
/// reveal (wire order: pair reveal, code reveal, hub sig, user sig).
pub fn checked_split_leaf(
    ctx: &lngap_channel::CommitCtx,
    l: &Layout,
    o: &lngap_contract::Outcome,
    csv: u16,
    code: &lngap_lamport::PublicKey,
    key: &WotsPublic,
) -> lngap_btc::taptree::Leaf {
    use lngap_lamport::gadgets::LamportExt;
    let mut b = Builder::new().csv(csv);
    b = ctx.two_of_two_verify(b);
    b = b.expect_uint(code, u32::from(o.code));
    b = b.wots_verify(key);
    b = resolution_fragment(b, l.file, l.new, o.code);
    for _ in 0..l.file / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    lngap_btc::taptree::Leaf::new(
        format!("split_{}", o.name),
        b.push_int(1).into_script(),
        lngap_btc::tx::Timelock::csv(csv),
    )
}

/// The checked split's witness, wire order (bottom first): the pair reveal,
/// the code reveal, the hub signature, the user signature (consumed first).
pub fn checked_split_witness(
    sig_user: Vec<u8>,
    sig_hub: Vec<u8>,
    code: &lngap_lamport::Reveal,
    pair: &lngap_lamport::winternitz::WotsSig,
) -> Vec<Vec<u8>> {
    let mut w = crate::refute::wots_wire(pair);
    let mut c = code.consumption_order();
    c.reverse();
    w.extend(c);
    w.push(sig_hub);
    w.push(sig_user);
    w
}
