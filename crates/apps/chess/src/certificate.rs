//! The certificate and its challenges.
//!
//! A mover's account of its move is the move and the position after it:
//! nothing else is needed. Every rule of chess is a statement about
//! (prior, move, after) that a challenger falsifies by naming a
//! [`Challenge`], which is a statement kind plus at most one exhibit (a
//! square, a ray index, an attacker). [`check`] evaluates one challenge with
//! bounded work of the kind Script can do: indexed reads of the two boards,
//! comparisons, a few additions. It never searches. [`find`] is the
//! challenger's off-chain search over the whole (finite) challenge space.
//!
//! The three properties the design needs (design doc §3):
//!
//! - TOTAL: any (prior, move, after, challenge) evaluates; nothing is
//!   undefined. Positions are already decoded, so a byte string that is no
//!   position is rejected one layer down, by `Position::from_bytes`.
//! - COMPLETE: if no challenge checks, the move is legal and `after` is its
//!   successor. Tested by fuzzing against [`crate::rules::apply`] and the
//!   move generator (tests/certificate.rs); the checker here is written
//!   without calling either, so the test is not circular.
//! - BOUND: every check reads the squares the move names, so a true
//!   statement about other squares cannot stand in.
//!
//! What is deliberately absent: attack bitboards. King safety is a universal
//! ("no attacker exists") whose falsification is one attacker square; the
//! checker verifies that attacker's geometry and ray directly in `after`.
//! A precomputed attack set would add 512 bytes and remove no work.

use crate::mv::Move;
use crate::piece::Colour;
use crate::position::{castle_bit, Position};
use crate::square::Square;

/// A statement the mover made, implicitly, by publishing (move, after), and
/// the exhibit that falsifies it. `check` returns `true` when the statement
/// is false, that is, when the challenger wins.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Challenge {
    /// The piece on `from` is the mover's and moves from `from` to `to`
    /// that way (pawn push, double push or capture shape; knight; slider
    /// line; king step or castling shape).
    Mover,
    /// The destination is acceptable for that piece: not the mover's own
    /// piece; for a pawn, empty on a push, an enemy or the en passant square
    /// on a capture.
    Destination,
    /// The `j`-th square from `from` towards `to` (1 <= j < distance) is
    /// empty. Covers sliders, the double push and the castling king's path.
    Ray { j: u8 },
    /// A pawn reaching the last rank names a promotion piece, and nothing
    /// else does.
    Promotion,
    /// Castling: the king is on its home square with the right still held,
    /// its rook is home, the destination is empty (a castle captures
    /// nothing) and, queenside, so is the b-file square.
    Castling,
    /// Castling: the king's square (`crossed == false`) or the square it
    /// crosses is not attacked in the prior by the piece on `by`.
    CastlingAttacked { crossed: bool, by: Square },
    /// After the move, the mover's king on `king` is not attacked by the
    /// piece on `by`.
    KingAttacked { king: Square, by: Square },
    /// `after[sq]` is what the move makes it: the moved (or promoted) piece
    /// on `to`, empty on `from` and on a captured en passant pawn's square,
    /// the rook moved on a castle, `prior[sq]` everywhere else.
    Board { sq: Square },
    /// The side to move flipped.
    Side,
    /// Castling rights dropped exactly for the king and corners the move
    /// touched.
    CastlingField,
    /// The en passant square is set after a double push and cleared
    /// otherwise.
    EpField,
    /// The halfmove clock reset on a pawn move or capture and advanced
    /// otherwise.
    Clock,
    /// The move number advanced after Black's move.
    MoveNumber,
}

impl Challenge {
    /// The whole challenge space: what a challenger searches and what the
    /// soundness test enumerates. About 4,400 entries.
    pub fn all() -> Vec<Challenge> {
        let mut v = vec![Challenge::Mover, Challenge::Destination, Challenge::Promotion, Challenge::Castling, Challenge::Side, Challenge::CastlingField, Challenge::EpField, Challenge::Clock, Challenge::MoveNumber];
        v.extend((1..=6).map(|j| Challenge::Ray { j }));
        v.extend(Square::all().map(|sq| Challenge::Board { sq }));
        for by in Square::all() {
            v.push(Challenge::CastlingAttacked { crossed: false, by });
            v.push(Challenge::CastlingAttacked { crossed: true, by });
        }
        for king in Square::all() {
            v.extend(Square::all().map(|by| Challenge::KingAttacked { king, by }));
        }
        v
    }
}

// ---- the Script-shaped primitives -------------------------------------

/// The colour bit of a nibble; meaningless for 0, so callers test emptiness first.
fn colour_of(n: u8) -> Colour {
    if n & 8 != 0 {
        Colour::Black
    } else {
        Colour::White
    }
}
fn kind_of(n: u8) -> u8 {
    n & 7
}
fn is_own(n: u8, side: Colour) -> bool {
    n != 0 && colour_of(n) == side
}
fn is_enemy(n: u8, side: Colour) -> bool {
    n != 0 && colour_of(n) != side
}
fn df(a: Square, b: Square) -> i8 {
    b.file() as i8 - a.file() as i8
}
fn dr(a: Square, b: Square) -> i8 {
    b.rank() as i8 - a.rank() as i8
}
/// The step along the line from `a` to `b` as a square-index delta, and the
/// number of steps; `None` if not aligned.
fn line(a: Square, b: Square) -> Option<(i8, i8)> {
    let (f, r) = (df(a, b), dr(a, b));
    if (f == 0 && r == 0) || !(f == 0 || r == 0 || f.abs() == r.abs()) {
        return None;
    }
    Some((f.signum() + 8 * r.signum(), f.abs().max(r.abs())))
}
fn step(a: Square, delta: i8, j: i8) -> Square {
    Square::new((a.u8() as i8 + delta * j) as u8).expect("a square on the line between two squares")
}

/// Whether a piece nibble `n` standing on `from` attacks `to` by geometry.
fn attack_shape(n: u8, from: Square, to: Square) -> bool {
    let (f, r) = (df(from, to).abs(), dr(from, to));
    match kind_of(n) {
        1 => f == 1 && r == colour_of(n).forward(),
        2 => (f == 1 && r.abs() == 2) || (f == 2 && r.abs() == 1),
        3 => f != 0 && f == r.abs(),
        4 => (f == 0) != (r == 0),
        5 => (f != 0 || r != 0) && (f == 0 || r == 0 || f == r.abs()),
        6 => (f != 0 || r != 0) && f <= 1 && r.abs() <= 1,
        _ => false,
    }
}

/// Whether the piece on `by` attacks `sq` in `pos`: an enemy of `side`
/// with the right shape and, for sliders, an empty ray. Bounded: at most
/// six reads along the ray.
fn attacks(pos: &Position, side: Colour, by: Square, sq: Square) -> bool {
    let n = pos.nibble_at(by);
    if !is_enemy(n, side) || !attack_shape(n, by, sq) {
        return false;
    }
    match kind_of(n) {
        3..=5 => {
            let (delta, dist) = line(by, sq).expect("shape implies a line");
            (1..dist).all(|j| pos.is_empty(step(by, delta, j)))
        }
        _ => true,
    }
}

/// The shape the mover's move has, as far as the statements need it.
struct Shape {
    kind: u8,
    f: i8,
    r: i8,
    castling: bool,
    rook_from: Square,
    rook_to: Square,
    /// A pawn moving diagonally onto an empty square: an en passant capture
    /// by shape (whether or not the field allows it).
    ep_capture: bool,
    ep_captured: Square,
}

fn shape(prior: &Position, mv: Move) -> Shape {
    let side = prior.side;
    let n = prior.nibble_at(mv.from);
    let kind = if is_own(n, side) { kind_of(n) } else { 0 };
    let (f, r) = (df(mv.from, mv.to), dr(mv.from, mv.to));
    let home = side.home_rank();
    let castling = kind == 6 && r == 0 && f.abs() == 2;
    let kingside = f > 0;
    let ep_capture = kind == 1 && f != 0 && prior.is_empty(mv.to);
    Shape {
        kind,
        f,
        r,
        castling,
        rook_from: Square::from_fr(if kingside { 7 } else { 0 }, home),
        rook_to: Square::from_fr(if kingside { 5 } else { 3 }, home),
        ep_capture,
        ep_captured: mv.to.offset(0, -side.forward()).unwrap_or(mv.to),
    }
}

/// `true` when the statement `c` names is false for (prior, move, after).
pub fn check(prior: &Position, mv: Move, after: &Position, c: Challenge) -> bool {
    let side = prior.side;
    let s = shape(prior, mv);
    let fwd = side.forward();
    let target = prior.nibble_at(mv.to);
    match c {
        Challenge::Mover => {
            let ok = match s.kind {
                1 => (s.f == 0 && s.r == fwd) || (s.f == 0 && s.r == 2 * fwd && mv.from.rank() == side.pawn_rank()) || (s.f.abs() == 1 && s.r == fwd),
                6 => attack_shape(s.kind, mv.from, mv.to) || (s.castling && mv.from == Square::from_fr(4, side.home_rank())),
                0 => false,
                k => attack_shape(k, mv.from, mv.to),
            };
            !ok
        }
        Challenge::Destination => {
            let ok = if s.kind == 1 {
                if s.f == 0 {
                    target == 0
                } else {
                    is_enemy(target, side) || (target == 0 && prior.ep == Some(mv.to))
                }
            } else {
                !is_own(target, side)
            };
            !ok
        }
        Challenge::Ray { j } => match line(mv.from, mv.to) {
            Some((delta, dist)) if s.kind != 2 && (1..dist).contains(&(j as i8)) => !prior.is_empty(step(mv.from, delta, j as i8)),
            _ => false,
        },
        Challenge::Promotion => (s.kind == 1 && mv.to.rank() == side.last_rank()) != mv.promotion.is_some(),
        Challenge::Castling => {
            if !s.castling {
                return false;
            }
            let rook = prior.nibble_at(s.rook_from);
            let ok = mv.from == Square::from_fr(4, side.home_rank())
                && prior.can_castle(side, s.f > 0)
                && is_own(rook, side)
                && kind_of(rook) == 4
                && prior.is_empty(mv.to)
                && (s.f > 0 || prior.is_empty(Square::from_fr(1, side.home_rank())));
            !ok
        }
        Challenge::CastlingAttacked { crossed, by } => {
            if !s.castling {
                return false;
            }
            let sq = if crossed { step(mv.from, s.f.signum(), 1) } else { mv.from };
            attacks(prior, side, by, sq)
        }
        Challenge::KingAttacked { king, by } => {
            let k = after.nibble_at(king);
            is_own(k, side) && kind_of(k) == 6 && attacks(after, side, by, king)
        }
        Challenge::Board { sq } => {
            let moved = prior.nibble_at(mv.from);
            let placed = match mv.promotion {
                Some(p) => (moved & 8) | p.code(),
                None => moved,
            };
            let emptied = sq == mv.from || (s.castling && sq == s.rook_from) || (s.ep_capture && sq == s.ep_captured);
            let expected = if sq == mv.to {
                placed
            } else if emptied {
                0
            } else if s.castling && sq == s.rook_to {
                prior.nibble_at(s.rook_from)
            } else {
                prior.nibble_at(sq)
            };
            after.nibble_at(sq) != expected
        }
        Challenge::Side => after.side != side.other(),
        Challenge::CastlingField => {
            let mut cleared = 0;
            if s.kind == 6 {
                cleared |= castle_bit(side, true) | castle_bit(side, false);
            }
            for (sq, c, kingside) in [(mv.from, side, true), (mv.from, side, false), (mv.to, side.other(), true), (mv.to, side.other(), false)] {
                if sq == Square::from_fr(if kingside { 7 } else { 0 }, c.home_rank()) {
                    cleared |= castle_bit(c, kingside);
                }
            }
            after.castling != prior.castling & !cleared
        }
        Challenge::EpField => {
            let expected = if s.kind == 1 && s.r == 2 * fwd { Some(step(mv.from, 8 * fwd, 1)) } else { None };
            after.ep != expected
        }
        Challenge::Clock => {
            let expected = if s.kind == 1 || target != 0 { 0 } else { prior.halfmove.saturating_add(1) };
            after.halfmove != expected
        }
        Challenge::MoveNumber => after.fullmove != prior.fullmove.saturating_add(u16::from(side == Colour::Black)),
    }
}

/// The challenger's search: the first challenge that checks, if any.
pub fn find(prior: &Position, mv: Move, after: &Position) -> Option<Challenge> {
    Challenge::all().into_iter().find(|&c| check(prior, mv, after, c))
}

/// The first challenge of the given kind that checks, if any.
pub fn find_kind(prior: &Position, mv: Move, after: &Position, kind: crate::leaf::Kind) -> Option<Challenge> {
    Challenge::all().into_iter().filter(|&c| crate::leaf::Kind::of(c) == kind).find(|&c| check(prior, mv, after, c))
}

/// What a cheating mover would plausibly publish for an illegal move: the
/// board updated mechanically as if the move were legal, fields updated by
/// the same rules. Used by the completeness test; not part of the protocol.
pub fn mechanical_successor(prior: &Position, mv: Move) -> Position {
    let side = prior.side;
    let s = shape(prior, mv);
    let mut n = prior.clone();
    let moved = prior.piece_at(mv.from);
    n.set(mv.from, None);
    n.set(mv.to, moved.map(|p| mv.promotion.map_or(p, |k| crate::piece::Piece::new(p.colour, k))));
    if s.castling {
        let rook = prior.piece_at(s.rook_from);
        n.set(s.rook_from, None);
        n.set(s.rook_to, rook);
    }
    if s.ep_capture {
        n.set(s.ep_captured, None);
    }
    if s.kind == 6 {
        n.castling &= !(castle_bit(side, true) | castle_bit(side, false));
    }
    for (sq, c, kingside) in [(mv.from, side, true), (mv.from, side, false), (mv.to, side.other(), true), (mv.to, side.other(), false)] {
        if sq == Square::from_fr(if kingside { 7 } else { 0 }, c.home_rank()) {
            n.castling &= !castle_bit(c, kingside);
        }
    }
    n.ep = if s.kind == 1 && s.r == 2 * side.forward() { mv.from.offset(0, side.forward()) } else { None };
    n.halfmove = if s.kind == 1 || !prior.is_empty(mv.to) { 0 } else { prior.halfmove.saturating_add(1) };
    n.fullmove = prior.fullmove.saturating_add(u16::from(side == Colour::Black));
    n.side = side.other();
    n
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::apply;

    fn pos(fen: &str) -> Position {
        Position::from_fen(fen).unwrap()
    }
    fn mv(s: &str) -> Move {
        Move::parse(s).unwrap()
    }
    fn sq(s: &str) -> Square {
        Square::parse(s).unwrap()
    }

    #[test]
    fn legal_moves_have_no_challenge() {
        let s = Position::start();
        for m in ["e2e4", "g1f3", "b2b4"] {
            let n = apply(&s, mv(m)).unwrap();
            assert_eq!(find(&s, mv(m), &n), None, "{m}");
        }
    }

    #[test]
    fn each_lie_names_its_exhibit() {
        let s = Position::start();
        // a blocked ray: the bishop jumps over the d2 pawn
        let m = mv("c1e3");
        assert_eq!(find(&s, m, &mechanical_successor(&s, m)), Some(Challenge::Ray { j: 1 }));
        // wrong geometry
        let m = mv("e2e5");
        assert_eq!(find(&s, m, &mechanical_successor(&s, m)), Some(Challenge::Mover));
        // a legal move with a corrupted board: the mover also removes h8
        let m = mv("e2e4");
        let mut n = apply(&s, m).unwrap();
        n.set(sq("h8"), None);
        assert_eq!(find(&s, m, &n), Some(Challenge::Board { sq: sq("h8") }));
        // moving into check: the exhibit is the attacker
        let s = pos("4k3/8/8/8/8/8/8/4K2r w - - 0 1");
        let m = mv("e1f1");
        assert_eq!(find(&s, m, &mechanical_successor(&s, m)), Some(Challenge::KingAttacked { king: sq("f1"), by: sq("h1") }));
        // castling through check
        let s = pos("r4rk1/8/8/8/8/8/8/R3K2R w KQ - 0 1");
        let m = mv("e1g1");
        assert_eq!(find(&s, m, &mechanical_successor(&s, m)), Some(Challenge::CastlingAttacked { crossed: true, by: sq("f8") }));
        // castling onto an enemy piece (found by the fuzz test, 2026-09-16)
        let s = pos("r1B1k1nr/pp3ppp/n2b4/2pp4/8/q1PP2P1/PP1N1P2/RNBQK2R b KQkq - 1 10");
        let m = mv("e8c8");
        assert_eq!(find(&s, m, &mechanical_successor(&s, m)), Some(Challenge::Castling));
        // the wrong side to move afterwards
        let s = Position::start();
        let mut n = apply(&s, mv("e2e4")).unwrap();
        n.side = Colour::White;
        assert_eq!(find(&s, mv("e2e4"), &n), Some(Challenge::Side));
    }
}
