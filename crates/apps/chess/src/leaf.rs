//! The ten challenge kinds as Bitcoin Script leaf bodies.
//!
//! A leaf takes, as witness elements pushed in this order (deepest first):
//! the prior board `S` as 64 nibbles, the board after `A` as 64 nibbles, the
//! prior's fields (side, castling, ep with 64 for none, halfmove, move
//! number), the same five fields of `A`, the move (from, to, promotion code),
//! then the exhibit the challenge kind needs. It leaves exactly one element,
//! true when the statement the kind names is false, so that a challenger can
//! spend it exactly when `certificate::check` says the mover lied. In the
//! protocol these inputs are registers of a bisected claim, bound by the
//! terminal leaf; here they are plain witness elements, which is enough to
//! measure the bodies and to test them against the Rust checker.
//!
//! Script has no multiplication, division or bitwise operators on numbers,
//! so: rank and file come from seven comparisons and three doublings; a bit
//! of a nibble from gated subtractions; the j-th square on a ray from at
//! most six gated additions of a step chosen by two signs. Every read of a
//! board is one computed-index OP_PICK. Every witness index is range-checked
//! before it is used as a depth, so an exhibit cannot read outside its board.
//! Conditions fed to OP_IF are always 0/1 (tapscript MINIMALIF).

use crate::certificate::Challenge;
use crate::mv::Move;
use crate::piece::Colour;
use crate::position::Position;
use bitcoin::opcodes::all::*;
use bitcoin::script::{Builder, ScriptBuf};

/// The challenge kinds, one leaf each.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Kind {
    Mover,
    Destination,
    Ray,
    Promotion,
    Castling,
    CastlingAttacked,
    KingAttacked,
    Board,
    Side,
    CastlingField,
    EpField,
    Clock,
    MoveNumber,
}

impl Kind {
    pub const ALL: [Kind; 13] = [Kind::Mover, Kind::Destination, Kind::Ray, Kind::Promotion, Kind::Castling, Kind::CastlingAttacked, Kind::KingAttacked, Kind::Board, Kind::Side, Kind::CastlingField, Kind::EpField, Kind::Clock, Kind::MoveNumber];

    pub fn of(c: Challenge) -> Kind {
        match c {
            Challenge::Mover => Kind::Mover,
            Challenge::Destination => Kind::Destination,
            Challenge::Ray { .. } => Kind::Ray,
            Challenge::Promotion => Kind::Promotion,
            Challenge::Castling => Kind::Castling,
            Challenge::CastlingAttacked { .. } => Kind::CastlingAttacked,
            Challenge::KingAttacked { .. } => Kind::KingAttacked,
            Challenge::Board { .. } => Kind::Board,
            Challenge::Side => Kind::Side,
            Challenge::CastlingField => Kind::CastlingField,
            Challenge::EpField => Kind::EpField,
            Challenge::Clock => Kind::Clock,
            Challenge::MoveNumber => Kind::MoveNumber,
        }
    }

    /// How many exhibit elements this kind takes.
    pub fn exhibit_len(self) -> usize {
        self.exhibit().len()
    }
    /// The exhibit elements this kind takes, after the common inputs.
    fn exhibit(self) -> &'static [Name] {
        match self {
            Kind::Ray => &[Name::J],
            Kind::CastlingAttacked => &[Name::Crossed, Name::By],
            Kind::KingAttacked => &[Name::King, Name::By],
            Kind::Board => &[Name::Sq],
            _ => &[],
        }
    }
}

/// The witness elements for a challenge, in push order (deepest first).
pub fn witness(prior: &Position, mv: Move, after: &Position, c: Challenge) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::with_capacity(160);
    for p in [prior, after] {
        v.extend(crate::square::Square::all().map(|sq| i64::from(p.nibble_at(sq))));
    }
    for p in [prior, after] {
        v.push(i64::from(p.side == Colour::Black));
        v.push(i64::from(p.castling));
        v.push(p.ep.map_or(64, |s| i64::from(s.u8())));
        v.push(i64::from(p.halfmove));
        v.push(i64::from(p.fullmove));
    }
    v.push(i64::from(mv.from.u8()));
    v.push(i64::from(mv.to.u8()));
    v.push(i64::from(mv.promotion.map_or(0, |k| k.code())));
    match c {
        Challenge::Ray { j } => v.push(i64::from(j)),
        Challenge::CastlingAttacked { crossed, by } => {
            v.push(i64::from(crossed));
            v.push(i64::from(by.u8()));
        }
        Challenge::KingAttacked { king, by } => {
            v.push(i64::from(king.u8()));
            v.push(i64::from(by.u8()));
        }
        Challenge::Board { sq } => v.push(i64::from(sq.u8())),
        _ => {}
    }
    v
}

// ---- the emitter -------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Name {
    S(u8),
    A(u8),
    SSide,
    SCastling,
    SEp,
    SHalf,
    SFull,
    ASide,
    ACastling,
    AEp,
    AHalf,
    AFull,
    From,
    To,
    Promo,
    J,
    Crossed,
    By,
    King,
    Sq,
    /// Nibble `i` of a claim register file (register layouts).
    Nib(u16),
    // computed
    Side,
    Fwd,
    Ff,
    Fr,
    Tf,
    Tr,
    Df,
    Dr,
    NFrom,
    Own,
    K,
    Tmp(u8),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Board {
    S,
    A,
}

/// A script builder that tracks the stack as a list of slots (deepest
/// first), some named, so that a named value can be picked from anywhere
/// and every computed-index read knows its depth constant.
struct Emit {
    b: Builder,
    slots: Vec<Option<Name>>,
    frames: Vec<(usize, Option<usize>)>,
    /// Slot index of square 0 of the prior and of the successor.
    s_base: usize,
    a_base: usize,
}

/// Where the two positions sit in a claim's register file, in nibbles:
/// the successor (`E`) at `e_off`, the prior (`E2`) at `e2_off`, each 80
/// nibbles laid out as `lngap_chess_fc` encodes a state (64 squares, side,
/// castling, en passant, halfmove clock, from, to, promotion, depth).
#[derive(Clone, Copy, Debug)]
pub struct Registers {
    pub n_nibbles: usize,
    pub e_off: usize,
    pub e2_off: usize,
}

impl Emit {
    fn new(kind: Kind) -> Emit {
        let mut slots: Vec<Option<Name>> = Vec::with_capacity(160);
        slots.extend((0..64).map(|i| Some(Name::S(i))));
        slots.extend((0..64).map(|i| Some(Name::A(i))));
        slots.extend([Name::SSide, Name::SCastling, Name::SEp, Name::SHalf, Name::SFull, Name::ASide, Name::ACastling, Name::AEp, Name::AHalf, Name::AFull, Name::From, Name::To, Name::Promo].map(Some));
        slots.extend(kind.exhibit().iter().map(|&n| Some(n)));
        Emit { b: Builder::new(), slots, frames: vec![], s_base: 0, a_base: 64 }
    }
    /// A leaf body over a claim's register file: the exhibit's elements
    /// deepest (they are the last witness elements consumed), then the
    /// `n_nibbles` message nibbles a WOTS verification leaves (nibble 0
    /// deepest). The scalar fields are then derived from the nibbles.
    fn registers(b: Builder, kind: Kind, r: Registers) -> Emit {
        let mut slots: Vec<Option<Name>> = Vec::with_capacity(r.n_nibbles + 20);
        slots.extend(kind.exhibit().iter().map(|&n| Some(n)));
        let base = slots.len();
        slots.extend((0..r.n_nibbles).map(|i| Some(Name::Nib(i as u16))));
        let mut e = Emit { b, slots, frames: vec![], s_base: base + r.e2_off, a_base: base + r.e_off };
        // a byte's low nibble, or a whole byte, of a state
        let nib = |e: &mut Emit, off: usize| e.get(Name::Nib(off as u16));
        let byte = |e: &mut Emit, off: usize| {
            nib(e, off);
            e.times8();
            e.double();
            nib(e, off + 1);
            e.add();
        };
        for (off, side, castling, ep, half, full) in [(r.e2_off, Name::SSide, Name::SCastling, Name::SEp, Name::SHalf, Name::SFull), (r.e_off, Name::ASide, Name::ACastling, Name::AEp, Name::AHalf, Name::AFull)] {
            nib(&mut e, off + 65);
            e.name(side);
            nib(&mut e, off + 67);
            e.name(castling);
            byte(&mut e, off + 68);
            e.name(ep);
            byte(&mut e, off + 70);
            e.name(half);
            e.int(0);
            e.name(full);
        }
        byte(&mut e, r.e_off + 72);
        e.name(Name::From);
        byte(&mut e, r.e_off + 74);
        e.name(Name::To);
        nib(&mut e, r.e_off + 76);
        e.name(Name::Promo);
        e
    }
    fn raw(&mut self, op: bitcoin::opcodes::Opcode) {
        self.b = std::mem::replace(&mut self.b, Builder::new()).push_opcode(op);
    }
    fn raw_int(&mut self, v: i64) {
        self.b = if v == 0 { std::mem::replace(&mut self.b, Builder::new()).push_opcode(OP_PUSHBYTES_0) } else { std::mem::replace(&mut self.b, Builder::new()).push_int(v) };
    }
    /// Push a constant.
    fn int(&mut self, v: i64) {
        self.raw_int(v);
        self.slots.push(None);
    }
    /// An opcode consuming `pops` and producing `pushes` unnamed elements.
    fn op(&mut self, op: bitcoin::opcodes::Opcode, pops: usize, pushes: usize) {
        self.raw(op);
        for _ in 0..pops {
            self.slots.pop().expect("stack underflow in the emitter");
        }
        for _ in 0..pushes {
            self.slots.push(None);
        }
    }
    fn depth(&self, n: Name) -> usize {
        let p = self.slots.iter().rposition(|s| *s == Some(n)).unwrap_or_else(|| panic!("{n:?} is not on the stack"));
        self.slots.len() - 1 - p
    }
    /// Copy a named value to the top.
    fn get(&mut self, n: Name) {
        let d = self.depth(n);
        match d {
            0 => self.op(OP_DUP, 0, 1),
            1 => self.op(OP_OVER, 0, 1),
            _ => {
                self.raw_int(d as i64);
                self.op(OP_PICK, 0, 1);
            }
        }
    }
    /// Name the top element.
    fn name(&mut self, n: Name) {
        *self.slots.last_mut().expect("nothing to name") = Some(n);
    }
    /// Name the element at depth `d` (0 = top).
    fn name_at(&mut self, d: usize, n: Name) {
        let l = self.slots.len();
        self.slots[l - 1 - d] = Some(n);
    }
    /// OP_SWAP, keeping the slots' names with their values.
    fn swap(&mut self) {
        self.raw(OP_SWAP);
        let l = self.slots.len();
        self.slots.swap(l - 1, l - 2);
    }
    /// OP_ROT (third element to the top), keeping names with values.
    fn rot(&mut self) {
        self.raw(OP_ROT);
        let l = self.slots.len();
        let a = self.slots.remove(l - 3);
        self.slots.push(a);
    }
    fn drop(&mut self) {
        self.op(OP_DROP, 1, 0);
    }
    // arithmetic and logic over unnamed operands
    fn eq(&mut self, v: i64) {
        self.int(v);
        self.op(OP_NUMEQUAL, 2, 1);
    }
    fn ne(&mut self, v: i64) {
        self.int(v);
        self.op(OP_NUMNOTEQUAL, 2, 1);
    }
    fn numeq(&mut self) {
        self.op(OP_NUMEQUAL, 2, 1);
    }
    fn numne(&mut self) {
        self.op(OP_NUMNOTEQUAL, 2, 1);
    }
    fn and(&mut self) {
        self.op(OP_BOOLAND, 2, 1);
    }
    fn or(&mut self) {
        self.op(OP_BOOLOR, 2, 1);
    }
    fn not(&mut self) {
        self.op(OP_NOT, 1, 1);
    }
    fn add(&mut self) {
        self.op(OP_ADD, 2, 1);
    }
    fn sub(&mut self) {
        self.op(OP_SUB, 2, 1);
    }
    fn abs(&mut self) {
        self.op(OP_ABS, 1, 1);
    }
    fn nonzero(&mut self) {
        self.op(OP_0NOTEQUAL, 1, 1);
    }
    fn gte(&mut self, v: i64) {
        self.int(v);
        self.op(OP_GREATERTHANOREQUAL, 2, 1);
    }
    fn gt(&mut self, v: i64) {
        self.int(v);
        self.op(OP_GREATERTHAN, 2, 1);
    }
    fn lt(&mut self, v: i64) {
        self.int(v);
        self.op(OP_LESSTHAN, 2, 1);
    }
    fn lte(&mut self, v: i64) {
        self.int(v);
        self.op(OP_LESSTHANOREQUAL, 2, 1);
    }
    /// x -> 2x
    fn double(&mut self) {
        self.op(OP_DUP, 0, 1);
        self.add();
    }
    /// x -> 8x
    fn times8(&mut self) {
        self.double();
        self.double();
        self.double();
    }
    /// x -> sign(x)
    fn sign(&mut self) {
        self.op(OP_DUP, 0, 1);
        self.gt(0);
        self.op(OP_SWAP, 2, 2);
        self.lt(0);
        self.sub();
    }
    /// x -> rank (below), file (top)
    fn rank_file(&mut self) {
        self.op(OP_DUP, 0, 1);
        self.gte(8);
        for k in 2..8 {
            self.op(OP_OVER, 0, 1);
            self.gte(8 * k);
            self.add();
        }
        // x rank
        self.op(OP_DUP, 0, 1);
        self.times8();
        // x rank 8rank
        self.op(OP_ROT, 3, 3);
        self.op(OP_SWAP, 2, 2);
        self.sub();
        // rank file
    }
    /// nibble -> colour (0 white, 1 black; 0 for empty)
    fn colour(&mut self) {
        self.gte(8);
    }
    /// nibble -> kind (nibble minus 8 if set)
    fn kind(&mut self) {
        self.op(OP_DUP, 0, 1);
        self.gte(8);
        self.times8();
        self.sub();
    }
    /// `x` on top: fail the script unless 0 <= x < 64 (a witness index).
    fn require_square(&mut self) {
        self.op(OP_DUP, 0, 1);
        self.int(0);
        self.int(64);
        self.op(OP_WITHIN, 3, 1);
        self.op(OP_VERIFY, 1, 0);
    }
    /// Index on top -> that square's nibble of `board`.
    fn read(&mut self, board: Board) {
        let p0 = match board {
            Board::S => self.s_base,
            Board::A => self.a_base,
        };
        // at PICK time the index has been consumed: depth of square 0 is len-2-p0
        let c = (self.slots.len() - 2 - p0) as i64;
        self.raw_int(c);
        self.raw(OP_SWAP);
        self.raw(OP_SUB);
        self.raw(OP_PICK);
        // the index slot becomes the read value
    }
    fn if_(&mut self) {
        self.slots.pop().expect("condition");
        self.raw(OP_IF);
        self.frames.push((self.slots.len(), None));
    }
    fn else_(&mut self) {
        let (base, then_len) = self.frames.last_mut().expect("ELSE without IF");
        assert!(then_len.is_none(), "two ELSEs");
        *then_len = Some(self.slots.len());
        self.slots.truncate(*base);
        self.raw(OP_ELSE);
    }
    fn endif(&mut self) {
        let (base, then_len) = self.frames.pop().expect("ENDIF without IF");
        if let Some(t) = then_len {
            assert_eq!(t, self.slots.len(), "IF branches leave different stack heights");
        } else {
            assert_eq!(base, self.slots.len(), "an IF without ELSE must leave the stack height unchanged");
        }
        self.raw(OP_ENDIF);
    }
    /// The result is on top: park it, drop everything, bring it back.
    fn finish(mut self) -> ScriptBuf {
        self.raw(OP_TOALTSTACK);
        let n = self.slots.len() - 1;
        for _ in 0..n / 2 {
            self.raw(OP_2DROP);
        }
        if n % 2 == 1 {
            self.raw(OP_DROP);
        }
        self.raw(OP_FROMALTSTACK);
        self.b.into_script()
    }
}

// ---- shared pieces -------------------------------------------------------

/// side, fwd, from/to ranks and files, df, dr, S[from], own, k.
fn preamble(e: &mut Emit) {
    e.get(Name::SSide);
    e.name(Name::Side);
    e.int(1);
    e.get(Name::Side);
    e.double();
    e.sub();
    e.name(Name::Fwd);
    e.get(Name::From);
    e.rank_file();
    e.name(Name::Ff);
    e.name_at(1, Name::Fr);
    e.get(Name::To);
    e.rank_file();
    e.name(Name::Tf);
    e.name_at(1, Name::Tr);
    e.get(Name::Tf);
    e.get(Name::Ff);
    e.sub();
    e.name(Name::Df);
    e.get(Name::Tr);
    e.get(Name::Fr);
    e.sub();
    e.name(Name::Dr);
    e.get(Name::From);
    e.read(Board::S);
    e.name(Name::NFrom);
    e.get(Name::NFrom);
    e.nonzero();
    e.get(Name::NFrom);
    e.colour();
    e.get(Name::Side);
    e.numeq();
    e.and();
    e.name(Name::Own);
    e.get(Name::NFrom);
    e.kind();
    e.get(Name::Own);
    e.if_();
    e.else_();
    e.drop();
    e.int(0);
    e.endif();
    e.name(Name::K);
}

/// k == 6 && dr == 0 && |df| == 2
fn castling_shape(e: &mut Emit) {
    e.get(Name::K);
    e.eq(6);
    e.get(Name::Dr);
    e.eq(0);
    e.and();
    e.get(Name::Df);
    e.abs();
    e.eq(2);
    e.and();
}

/// 56*side + `offset` (a square on the mover's home rank): 64s - 8s
fn home_square(e: &mut Emit, offset: i64) {
    e.get(Name::Side);
    e.times8();
    e.op(OP_DUP, 0, 1);
    e.times8();
    e.op(OP_SWAP, 2, 2);
    e.sub();
    if offset != 0 {
        e.int(offset);
        e.add();
    }
}

/// With `by` and `sq` named as Tmp(0) and Tmp(1): pushes whether the piece
/// on `by` is an enemy of the mover attacking `sq` in `board`.
fn attacks(e: &mut Emit, board: Board) {
    let (by, sq) = (Name::Tmp(0), Name::Tmp(1));
    e.get(by);
    e.read(board);
    e.name(Name::Tmp(2)); // n
    e.get(Name::Tmp(2));
    e.nonzero();
    e.get(Name::Tmp(2));
    e.colour();
    e.get(Name::Side);
    e.numne();
    e.and();
    e.name(Name::Tmp(3)); // enemy
    e.get(by);
    e.rank_file();
    e.name(Name::Tmp(4)); // bf
    e.name_at(1, Name::Tmp(5)); // br
    e.get(sq);
    e.rank_file();
    e.name(Name::Tmp(6)); // qf
    e.name_at(1, Name::Tmp(7)); // qr
    e.get(Name::Tmp(6));
    e.get(Name::Tmp(4));
    e.sub();
    e.name(Name::Tmp(8)); // sf = qf - bf (signed)
    e.get(Name::Tmp(8));
    e.abs();
    e.name(Name::Tmp(9)); // f
    e.get(Name::Tmp(7));
    e.get(Name::Tmp(5));
    e.sub();
    e.name(Name::Tmp(10)); // r
    e.get(Name::Tmp(2));
    e.kind();
    e.name(Name::Tmp(11)); // kn
    // shape
    // pawn: f == 1 && r == 1 - 2*colour(n)
    e.get(Name::Tmp(11));
    e.eq(1);
    e.get(Name::Tmp(9));
    e.eq(1);
    e.and();
    e.get(Name::Tmp(10));
    e.int(1);
    e.get(Name::Tmp(2));
    e.colour();
    e.double();
    e.sub();
    e.numeq();
    e.and();
    // knight
    e.get(Name::Tmp(11));
    e.eq(2);
    e.get(Name::Tmp(9));
    e.eq(1);
    e.get(Name::Tmp(10));
    e.abs();
    e.eq(2);
    e.and();
    e.get(Name::Tmp(9));
    e.eq(2);
    e.get(Name::Tmp(10));
    e.abs();
    e.eq(1);
    e.and();
    e.or();
    e.and();
    e.or();
    // bishop: f != 0 && f == |r|
    e.get(Name::Tmp(11));
    e.eq(3);
    e.get(Name::Tmp(9));
    e.nonzero();
    e.get(Name::Tmp(9));
    e.get(Name::Tmp(10));
    e.abs();
    e.numeq();
    e.and();
    e.and();
    e.or();
    // rook: (f == 0) != (r == 0)
    e.get(Name::Tmp(11));
    e.eq(4);
    e.get(Name::Tmp(9));
    e.eq(0);
    e.get(Name::Tmp(10));
    e.eq(0);
    e.numne();
    e.and();
    e.or();
    // queen: (f != 0 || r != 0) && (f == 0 || r == 0 || f == |r|)
    e.get(Name::Tmp(11));
    e.eq(5);
    e.get(Name::Tmp(9));
    e.nonzero();
    e.get(Name::Tmp(10));
    e.nonzero();
    e.or();
    e.get(Name::Tmp(9));
    e.eq(0);
    e.get(Name::Tmp(10));
    e.eq(0);
    e.or();
    e.get(Name::Tmp(9));
    e.get(Name::Tmp(10));
    e.abs();
    e.numeq();
    e.or();
    e.and();
    e.and();
    e.or();
    // king: (f != 0 || r != 0) && f <= 1 && |r| <= 1
    e.get(Name::Tmp(11));
    e.eq(6);
    e.get(Name::Tmp(9));
    e.nonzero();
    e.get(Name::Tmp(10));
    e.nonzero();
    e.or();
    e.get(Name::Tmp(9));
    e.lte(1);
    e.and();
    e.get(Name::Tmp(10));
    e.abs();
    e.lte(1);
    e.and();
    e.and();
    e.or();
    e.name(Name::Tmp(12)); // shape
    // ray: for sliders, the squares strictly between by and sq are empty
    e.get(Name::Tmp(11));
    e.gte(3);
    e.get(Name::Tmp(11));
    e.lte(5);
    e.and();
    e.get(Name::Tmp(12));
    e.and();
    e.if_();
    {
        // dist = max(f, |r|); step = sign(sf) + 8*sign(r)
        e.get(Name::Tmp(9));
        e.get(Name::Tmp(10));
        e.abs();
        e.op(OP_MAX, 2, 1);
        e.name(Name::Tmp(13)); // dist
        e.get(Name::Tmp(8));
        e.sign();
        e.get(Name::Tmp(10));
        e.sign();
        e.times8();
        e.add();
        e.name(Name::Tmp(14)); // step
        e.int(1);
        e.name(Name::Tmp(16)); // all
        e.get(by);
        e.name(Name::Tmp(15)); // acc, on top so the addition consumes it
        for i in 1..=6 {
            e.get(Name::Tmp(14));
            e.add();
            e.name(Name::Tmp(15));
            e.int(i);
            e.get(Name::Tmp(13));
            e.op(OP_LESSTHAN, 2, 1);
            e.if_();
            e.get(Name::Tmp(15));
            e.read(board);
            e.eq(0);
            e.get(Name::Tmp(16));
            e.and();
            e.name(Name::Tmp(16));
            // stack: all acc all' -> all' acc, the old accumulator dropped
            e.rot();
            e.drop();
            e.swap();
            e.endif();
        }
        e.get(Name::Tmp(16));
        // drop the four temporaries under the result
        e.op(OP_TOALTSTACK, 1, 0);
        e.op(OP_2DROP, 2, 0);
        e.op(OP_2DROP, 2, 0);
        e.op(OP_FROMALTSTACK, 0, 1);
    }
    e.else_();
    e.int(1);
    e.endif();
    e.name(Name::Tmp(13)); // ray ok
    e.get(Name::Tmp(3));
    e.get(Name::Tmp(12));
    e.and();
    e.get(Name::Tmp(13));
    e.and();
}

// ---- the leaves ----------------------------------------------------------

fn mover(e: &mut Emit) {
    // pawn
    e.get(Name::K);
    e.eq(1);
    e.get(Name::Df);
    e.eq(0);
    e.get(Name::Dr);
    e.get(Name::Fwd);
    e.numeq();
    e.and();
    e.get(Name::Df);
    e.eq(0);
    e.get(Name::Dr);
    e.get(Name::Fwd);
    e.double();
    e.numeq();
    e.and();
    e.get(Name::Fr);
    e.int(1);
    e.get(Name::Side);
    e.int(5);
    e.op(OP_SWAP, 2, 2);
    e.if_();
    e.else_();
    e.drop();
    e.int(0);
    e.endif();
    e.add();
    e.numeq();
    e.and();
    e.or();
    e.get(Name::Df);
    e.abs();
    e.eq(1);
    e.get(Name::Dr);
    e.get(Name::Fwd);
    e.numeq();
    e.and();
    e.or();
    e.and();
    // knight
    e.get(Name::K);
    e.eq(2);
    e.get(Name::Df);
    e.abs();
    e.eq(1);
    e.get(Name::Dr);
    e.abs();
    e.eq(2);
    e.and();
    e.get(Name::Df);
    e.abs();
    e.eq(2);
    e.get(Name::Dr);
    e.abs();
    e.eq(1);
    e.and();
    e.or();
    e.and();
    e.or();
    // bishop
    e.get(Name::K);
    e.eq(3);
    e.get(Name::Df);
    e.abs();
    e.get(Name::Dr);
    e.abs();
    e.numeq();
    e.get(Name::Df);
    e.nonzero();
    e.and();
    e.and();
    e.or();
    // rook
    e.get(Name::K);
    e.eq(4);
    e.get(Name::Df);
    e.eq(0);
    e.get(Name::Dr);
    e.eq(0);
    e.numne();
    e.and();
    e.or();
    // queen
    e.get(Name::K);
    e.eq(5);
    e.get(Name::Df);
    e.nonzero();
    e.get(Name::Dr);
    e.nonzero();
    e.or();
    e.get(Name::Df);
    e.eq(0);
    e.get(Name::Dr);
    e.eq(0);
    e.or();
    e.get(Name::Df);
    e.abs();
    e.get(Name::Dr);
    e.abs();
    e.numeq();
    e.or();
    e.and();
    e.and();
    e.or();
    // king
    e.get(Name::K);
    e.eq(6);
    e.get(Name::Df);
    e.nonzero();
    e.get(Name::Dr);
    e.nonzero();
    e.or();
    e.get(Name::Df);
    e.abs();
    e.lte(1);
    e.and();
    e.get(Name::Dr);
    e.abs();
    e.lte(1);
    e.and();
    castling_shape(e);
    e.get(Name::From);
    home_square(e, 4);
    e.numeq();
    e.and();
    e.or();
    e.and();
    e.or();
    // own && ok, negated
    e.get(Name::Own);
    e.and();
    e.not();
}

fn destination(e: &mut Emit) {
    e.get(Name::To);
    e.read(Board::S);
    e.name(Name::Tmp(0)); // t
    e.get(Name::K);
    e.eq(1);
    e.if_();
    {
        e.get(Name::Df);
        e.eq(0);
        e.if_();
        e.get(Name::Tmp(0));
        e.eq(0);
        e.else_();
        e.get(Name::Tmp(0));
        e.nonzero();
        e.get(Name::Tmp(0));
        e.colour();
        e.get(Name::Side);
        e.numne();
        e.and();
        e.get(Name::Tmp(0));
        e.eq(0);
        e.get(Name::SEp);
        e.get(Name::To);
        e.numeq();
        e.and();
        e.or();
        e.endif();
    }
    e.else_();
    {
        e.get(Name::Tmp(0));
        e.nonzero();
        e.get(Name::Tmp(0));
        e.colour();
        e.get(Name::Side);
        e.numeq();
        e.and();
        e.not();
    }
    e.endif();
    e.not();
}

fn ray(e: &mut Emit) {
    // aligned && not (0,0) && k != 2 && 1 <= j < dist
    e.get(Name::Df);
    e.eq(0);
    e.get(Name::Dr);
    e.eq(0);
    e.or();
    e.get(Name::Df);
    e.abs();
    e.get(Name::Dr);
    e.abs();
    e.numeq();
    e.or();
    e.get(Name::Df);
    e.nonzero();
    e.get(Name::Dr);
    e.nonzero();
    e.or();
    e.and();
    e.get(Name::K);
    e.ne(2);
    e.and();
    e.get(Name::J);
    e.gte(1);
    e.and();
    e.get(Name::J);
    e.get(Name::Df);
    e.abs();
    e.get(Name::Dr);
    e.abs();
    e.op(OP_MAX, 2, 1);
    e.op(OP_LESSTHAN, 2, 1);
    e.and();
    e.if_();
    {
        // sq = from + j*step
        e.get(Name::Df);
        e.sign();
        e.get(Name::Dr);
        e.sign();
        e.times8();
        e.add();
        e.name(Name::Tmp(0)); // step
        e.get(Name::From);
        e.name(Name::Tmp(1)); // acc
        for i in 1..=6 {
            e.int(i);
            e.get(Name::J);
            e.op(OP_LESSTHANOREQUAL, 2, 1);
            e.if_();
            e.get(Name::Tmp(0));
            e.add();
            e.name(Name::Tmp(1));
            e.endif();
        }
        e.read(Board::S);
        e.nonzero();
        e.op(OP_SWAP, 2, 2);
        e.drop();
    }
    e.else_();
    e.int(0);
    e.endif();
}

fn promotion(e: &mut Emit) {
    e.get(Name::K);
    e.eq(1);
    e.get(Name::Tr);
    e.int(7);
    e.get(Name::Side);
    e.int(7);
    e.op(OP_SWAP, 2, 2);
    e.if_();
    e.else_();
    e.drop();
    e.int(0);
    e.endif();
    e.sub();
    e.numeq();
    e.and();
    e.get(Name::Promo);
    e.nonzero();
    e.numne();
}

fn castling(e: &mut Emit) {
    castling_shape(e);
    e.if_();
    {
        // from == home e-square
        e.get(Name::From);
        home_square(e, 4);
        e.numeq();
        // right held: bit (2*side + [df < 0]) of S.castling
        e.get(Name::SCastling);
        bits4(e); // b3 b2 b1 b0 (b0 on top)
        e.get(Name::Side);
        e.double();
        e.get(Name::Df);
        e.lt(0);
        e.add();
        // bits: b0 at depth 1 (after the index), so depth = idx + 1 ... index on top: pick depth = idx (b0 is just below the index)
        e.op(OP_PICK, 1, 1);
        e.op(OP_TOALTSTACK, 1, 0);
        e.op(OP_2DROP, 2, 0);
        e.op(OP_2DROP, 2, 0);
        e.op(OP_FROMALTSTACK, 0, 1);
        e.and();
        // rook home: S[56*side + 7*[df>0]] == 8*side + 4
        e.get(Name::Df);
        e.gt(0);
        e.if_();
        home_square(e, 7);
        e.else_();
        home_square(e, 0);
        e.endif();
        e.read(Board::S);
        e.get(Name::Side);
        e.times8();
        e.int(4);
        e.add();
        e.numeq();
        e.and();
        // destination empty
        e.get(Name::To);
        e.read(Board::S);
        e.eq(0);
        e.and();
        // queenside: b-square empty
        e.get(Name::Df);
        e.gt(0);
        home_square(e, 1);
        e.read(Board::S);
        e.eq(0);
        e.or();
        e.and();
        e.not();
    }
    e.else_();
    e.int(0);
    e.endif();
}

/// nibble on top -> its four bits, b3 deepest, b0 on top (consumes the nibble)
fn bits4(e: &mut Emit) {
    e.op(OP_DUP, 0, 1);
    e.gte(8);
    e.op(OP_TUCK, 2, 3);
    e.times8();
    e.sub();
    e.op(OP_DUP, 0, 1);
    e.gte(4);
    e.op(OP_TUCK, 2, 3);
    e.double();
    e.double();
    e.sub();
    e.op(OP_DUP, 0, 1);
    e.gte(2);
    e.op(OP_TUCK, 2, 3);
    e.double();
    e.sub();
}

fn castling_attacked(e: &mut Emit) {
    castling_shape(e);
    e.if_();
    {
        e.get(Name::By);
        e.require_square();
        e.name(Name::Tmp(0));
        e.get(Name::From);
        e.get(Name::Crossed);
        e.if_();
        e.get(Name::Df);
        e.sign();
        e.add();
        e.endif();
        e.name(Name::Tmp(1));
        attacks(e, Board::S);
        e.op(OP_TOALTSTACK, 1, 0);
        while e.slots.len() > e.frames.last().unwrap().0 {
            e.drop();
        }
        e.op(OP_FROMALTSTACK, 0, 1);
    }
    e.else_();
    e.int(0);
    e.endif();
}

fn king_attacked(e: &mut Emit) {
    e.get(Name::King);
    e.require_square();
    e.read(Board::A);
    e.get(Name::Side);
    e.times8();
    e.int(6);
    e.add();
    e.numeq();
    e.if_();
    {
        e.get(Name::By);
        e.require_square();
        e.name(Name::Tmp(0));
        e.get(Name::King);
        e.name(Name::Tmp(1));
        attacks(e, Board::A);
        e.op(OP_TOALTSTACK, 1, 0);
        while e.slots.len() > e.frames.last().unwrap().0 {
            e.drop();
        }
        e.op(OP_FROMALTSTACK, 0, 1);
    }
    e.else_();
    e.int(0);
    e.endif();
}

fn board(e: &mut Emit) {
    e.get(Name::Sq);
    e.require_square();
    // placed
    e.get(Name::Promo);
    e.eq(0);
    e.if_();
    e.get(Name::NFrom);
    e.else_();
    e.get(Name::NFrom);
    e.colour();
    e.times8();
    e.get(Name::Promo);
    e.add();
    e.endif();
    e.name(Name::Tmp(0)); // placed
    castling_shape(e);
    e.name(Name::Tmp(1)); // castling
    e.get(Name::Df);
    e.gt(0);
    e.if_();
    home_square(e, 7);
    e.else_();
    home_square(e, 0);
    e.endif();
    e.name(Name::Tmp(2)); // rook_from
    e.get(Name::Df);
    e.gt(0);
    e.if_();
    home_square(e, 5);
    e.else_();
    home_square(e, 3);
    e.endif();
    e.name(Name::Tmp(3)); // rook_to
    e.get(Name::K);
    e.eq(1);
    e.get(Name::Df);
    e.nonzero();
    e.and();
    e.get(Name::To);
    e.read(Board::S);
    e.eq(0);
    e.and();
    e.name(Name::Tmp(4)); // ep_capture
    e.get(Name::To);
    e.get(Name::Fwd);
    e.times8();
    e.sub();
    e.op(OP_DUP, 0, 1);
    e.int(0);
    e.int(64);
    e.op(OP_WITHIN, 3, 1);
    e.if_();
    e.else_();
    e.drop();
    e.get(Name::To);
    e.endif();
    e.name(Name::Tmp(5)); // ep_captured
    // emptied
    e.get(Name::Sq);
    e.get(Name::From);
    e.numeq();
    e.get(Name::Tmp(1));
    e.get(Name::Sq);
    e.get(Name::Tmp(2));
    e.numeq();
    e.and();
    e.or();
    e.get(Name::Tmp(4));
    e.get(Name::Sq);
    e.get(Name::Tmp(5));
    e.numeq();
    e.and();
    e.or();
    e.name(Name::Tmp(6)); // emptied
    // expected
    e.get(Name::Sq);
    e.get(Name::To);
    e.numeq();
    e.if_();
    e.get(Name::Tmp(0));
    e.else_();
    e.get(Name::Tmp(6));
    e.if_();
    e.int(0);
    e.else_();
    e.get(Name::Tmp(1));
    e.get(Name::Sq);
    e.get(Name::Tmp(3));
    e.numeq();
    e.and();
    e.if_();
    e.get(Name::Tmp(2));
    e.read(Board::S);
    e.else_();
    e.get(Name::Sq);
    e.read(Board::S);
    e.endif();
    e.endif();
    e.endif();
    e.get(Name::Sq);
    e.read(Board::A);
    e.numne();
}

fn side(e: &mut Emit) {
    e.get(Name::ASide);
    e.int(1);
    e.get(Name::Side);
    e.sub();
    e.numne();
}

fn castling_field(e: &mut Emit) {
    // own_k, own_q, en_k, en_q
    e.get(Name::K);
    e.eq(6);
    e.get(Name::From);
    home_square(e, 7);
    e.numeq();
    e.or();
    e.name(Name::Tmp(0));
    e.get(Name::K);
    e.eq(6);
    e.get(Name::From);
    home_square(e, 0);
    e.numeq();
    e.or();
    e.name(Name::Tmp(1));
    // enemy corners: 56*(1-side) + 7 / + 0  = 63 - 56*side / 56 - 56*side
    e.get(Name::To);
    e.int(63);
    home_square(e, 0);
    e.sub();
    e.numeq();
    e.name(Name::Tmp(2));
    e.get(Name::To);
    e.int(56);
    home_square(e, 0);
    e.sub();
    e.numeq();
    e.name(Name::Tmp(3));
    // cleared bits in field order (b0 WK, b1 WQ, b2 BK, b3 BQ)
    // white: c0 = own_k, c1 = own_q, c2 = en_k, c3 = en_q; black: c0 = en_k, c1 = en_q, c2 = own_k, c3 = own_q
    e.get(Name::Side);
    e.if_();
    e.get(Name::Tmp(2));
    e.get(Name::Tmp(3));
    e.get(Name::Tmp(0));
    e.get(Name::Tmp(1));
    e.else_();
    e.get(Name::Tmp(0));
    e.get(Name::Tmp(1));
    e.get(Name::Tmp(2));
    e.get(Name::Tmp(3));
    e.endif();
    // c0 c1 c2 c3, c3 on top
    e.name_at(3, Name::Tmp(4));
    e.name_at(2, Name::Tmp(5));
    e.name_at(1, Name::Tmp(6));
    e.name_at(0, Name::Tmp(7));
    // expected = sum over i of b_i * !c_i * 2^i
    e.get(Name::SCastling);
    bits4(e); // b3 b2 b1 b0
    // b0
    e.get(Name::Tmp(4));
    e.not();
    e.and();
    e.op(OP_SWAP, 2, 2);
    e.get(Name::Tmp(5));
    e.not();
    e.and();
    e.double();
    e.add();
    e.op(OP_SWAP, 2, 2);
    e.get(Name::Tmp(6));
    e.not();
    e.and();
    e.double();
    e.double();
    e.add();
    e.op(OP_SWAP, 2, 2);
    e.get(Name::Tmp(7));
    e.not();
    e.and();
    e.times8();
    e.add();
    e.get(Name::ACastling);
    e.numne();
}

fn ep_field(e: &mut Emit) {
    e.get(Name::K);
    e.eq(1);
    e.get(Name::Dr);
    e.get(Name::Fwd);
    e.double();
    e.numeq();
    e.and();
    e.if_();
    e.get(Name::From);
    e.get(Name::Fwd);
    e.times8();
    e.add();
    e.else_();
    e.int(64);
    e.endif();
    e.get(Name::AEp);
    e.numne();
}

fn clock(e: &mut Emit) {
    e.get(Name::K);
    e.eq(1);
    e.get(Name::To);
    e.read(Board::S);
    e.nonzero();
    e.or();
    e.if_();
    e.int(0);
    e.else_();
    e.get(Name::SHalf);
    e.op(OP_1ADD, 1, 1);
    e.int(255);
    e.op(OP_MIN, 2, 1);
    e.endif();
    e.get(Name::AHalf);
    e.numne();
}

fn move_number(e: &mut Emit) {
    e.get(Name::SFull);
    e.get(Name::Side);
    e.add();
    e.int(65535);
    e.op(OP_MIN, 2, 1);
    e.get(Name::AFull);
    e.numne();
}

/// The exhibit elements of a challenge, in the order a leaf takes them.
pub fn exhibit_values(c: Challenge) -> Vec<i64> {
    match c {
        Challenge::Ray { j } => vec![i64::from(j)],
        Challenge::CastlingAttacked { crossed, by } => vec![i64::from(crossed), i64::from(by.u8())],
        Challenge::KingAttacked { king, by } => vec![i64::from(king.u8()), i64::from(by.u8())],
        Challenge::Board { sq } => vec![i64::from(sq.u8())],
        _ => vec![],
    }
}

/// The leaf body for a challenge kind over a claim's register file,
/// appended to `b` (which has verified the WOTS end state, leaving its
/// nibbles on the stack, with the exhibit below them).
pub fn leaf_over_registers(b: Builder, kind: Kind, r: Registers) -> ScriptBuf {
    let mut e = Emit::registers(b, kind, r);
    body(&mut e, kind);
    e.finish()
}

fn body(e: &mut Emit, kind: Kind) {
    preamble(e);
    match kind {
        Kind::Mover => mover(e),
        Kind::Destination => destination(e),
        Kind::Ray => ray(e),
        Kind::Promotion => promotion(e),
        Kind::Castling => castling(e),
        Kind::CastlingAttacked => castling_attacked(e),
        Kind::KingAttacked => king_attacked(e),
        Kind::Board => board(e),
        Kind::Side => side(e),
        Kind::CastlingField => castling_field(e),
        Kind::EpField => ep_field(e),
        Kind::Clock => clock(e),
        Kind::MoveNumber => move_number(e),
    }
}

/// The leaf body for a challenge kind.
pub fn leaf(kind: Kind) -> ScriptBuf {
    let mut e = Emit::new(kind);
    preamble(&mut e);
    match kind {
        Kind::Mover => mover(&mut e),
        Kind::Destination => destination(&mut e),
        Kind::Ray => ray(&mut e),
        Kind::Promotion => promotion(&mut e),
        Kind::Castling => castling(&mut e),
        Kind::CastlingAttacked => castling_attacked(&mut e),
        Kind::KingAttacked => king_attacked(&mut e),
        Kind::Board => board(&mut e),
        Kind::Side => side(&mut e),
        Kind::CastlingField => castling_field(&mut e),
        Kind::EpField => ep_field(&mut e),
        Kind::Clock => clock(&mut e),
        Kind::MoveNumber => move_number(&mut e),
    }
    e.finish()
}

/// Run a challenge through its leaf in the simulator: `Ok(true)` when the
/// leaf would let the challenger spend.
pub fn simulate(prior: &Position, mv: Move, after: &Position, c: Challenge) -> Result<bool, String> {
    let script = leaf(Kind::of(c));
    let stack = lngap_script32::sim::run_nums(&script, witness(prior, mv, after, c))?;
    match stack.as_slice() {
        [v] => Ok(*v != 0),
        s => Err(format!("leaf left {} elements", s.len())),
    }
}
