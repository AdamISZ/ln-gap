//! Legality as a sequence of named statements, mirroring the certificate
//! table of the design doc (§3). [`apply`] checks a move against the prior
//! position and computes the successor; [`verify`] checks a claimed
//! successor field by field. Every failure is a [`Violation`] carrying its
//! exhibit: the square, attacker or ray square a challenger would name.
//!
//! Nothing here judges the game's end. [`terminal`] tells a client whether
//! the side to move is checkmated (resign, or stall and lose) or stalemated
//! (publish a stalemate claim); neither is a statement of the mover's
//! certificate.

use crate::attack::{attackers, in_check, is_attacked};
use crate::movegen::legal_moves;
use crate::mv::Move;
use crate::piece::{Colour, Piece, PieceType};
use crate::position::{castle_bit, Position};
use crate::square::{between, Square};
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Violation {
    /// `from` does not hold a piece of the mover.
    NoPieceOfMover { from: Square },
    /// `to` holds a piece of the mover.
    DestinationOwnPiece { to: Square },
    /// The piece on `from` does not move to `to` that way.
    BadGeometry { from: Square, to: Square },
    /// A square strictly between `from` and `to` is occupied.
    RayBlocked { sq: Square },
    /// A pawn moved straight onto an occupied square.
    PawnPushOccupied { to: Square },
    /// A pawn moved diagonally onto an empty square that is not the en
    /// passant square.
    PawnCaptureNoTarget { to: Square },
    /// A pawn reached the last rank without a promotion piece.
    PromotionRequired,
    /// A promotion piece was given where none applies.
    PromotionNotAllowed,
    /// Castling without the right, or with the rook missing.
    CastlingRights,
    /// A square between the king and the rook is occupied.
    CastlingPathBlocked { sq: Square },
    /// The king's square, or a square it crosses or lands on, is attacked.
    CastlingThroughCheck { sq: Square, by: Square },
    /// After the move the mover's king on `king` is attacked from `by`.
    KingAttacked { king: Square, by: Square },
    /// A claimed successor differs from the computed one at `sq`.
    BoardMismatch { sq: Square },
    SideMismatch,
    CastlingFieldMismatch,
    EpFieldMismatch,
    ClockMismatch,
    MoveNumberMismatch,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Violation {}

/// What the move does, decided by the rules against the prior position.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Normal,
    /// A capture of the piece on `to`.
    Capture,
    DoublePush,
    /// The captured pawn stands on `captured`.
    EnPassant { captured: Square },
    /// The rook moves from `rook_from` to `rook_to`.
    Castle { rook_from: Square, rook_to: Square },
}

/// The move's kind and, for pawns, the checks specific to it; everything
/// about geometry, rays and castling but not king safety.
fn classify(pos: &Position, mv: Move, piece: Piece) -> Result<Kind, Violation> {
    let (from, to) = (mv.from, mv.to);
    let us = piece.colour;
    let target = pos.piece_at(to);
    if target.is_some_and(|t| t.colour == us) {
        return Err(Violation::DestinationOwnPiece { to });
    }
    let df = to.file() as i8 - from.file() as i8;
    let dr = to.rank() as i8 - from.rank() as i8;
    let geometry = Violation::BadGeometry { from, to };

    if piece.kind == PieceType::Pawn {
        let fwd = us.forward();
        let kind = if df == 0 && dr == fwd {
            if target.is_some() {
                return Err(Violation::PawnPushOccupied { to });
            }
            Kind::Normal
        } else if df == 0 && dr == 2 * fwd && from.rank() == us.pawn_rank() {
            let mid = from.offset(0, fwd).expect("on the board");
            if !pos.is_empty(mid) {
                return Err(Violation::RayBlocked { sq: mid });
            }
            if target.is_some() {
                return Err(Violation::PawnPushOccupied { to });
            }
            Kind::DoublePush
        } else if df.abs() == 1 && dr == fwd {
            if target.is_some() {
                Kind::Capture
            } else if pos.ep == Some(to) {
                Kind::EnPassant { captured: to.offset(0, -fwd).expect("on the board") }
            } else {
                return Err(Violation::PawnCaptureNoTarget { to });
            }
        } else {
            return Err(geometry);
        };
        let promoting = to.rank() == us.last_rank();
        match (promoting, mv.promotion) {
            (true, None) => return Err(Violation::PromotionRequired),
            (false, Some(_)) => return Err(Violation::PromotionNotAllowed),
            (true, Some(k)) if !k.is_promotion_piece() => return Err(Violation::PromotionNotAllowed),
            _ => {}
        }
        return Ok(kind);
    }
    if mv.promotion.is_some() {
        return Err(Violation::PromotionNotAllowed);
    }

    let ok = match piece.kind {
        PieceType::Knight => (df.abs() == 1 && dr.abs() == 2) || (df.abs() == 2 && dr.abs() == 1),
        PieceType::Bishop => df != 0 && df.abs() == dr.abs(),
        PieceType::Rook => (df == 0) != (dr == 0),
        PieceType::Queen => (df != 0 || dr != 0) && (df == 0 || dr == 0 || df.abs() == dr.abs()),
        PieceType::King => {
            if dr == 0 && df.abs() == 2 {
                return castle(pos, from, to, us, df > 0);
            }
            (df != 0 || dr != 0) && df.abs() <= 1 && dr.abs() <= 1
        }
        PieceType::Pawn => unreachable!(),
    };
    if !ok {
        return Err(geometry);
    }
    if let Some(sq) = between(from, to).into_iter().find(|&s| !pos.is_empty(s)) {
        return Err(Violation::RayBlocked { sq });
    }
    Ok(if target.is_some() { Kind::Capture } else { Kind::Normal })
}

fn castle(pos: &Position, from: Square, to: Square, us: Colour, kingside: bool) -> Result<Kind, Violation> {
    let home = us.home_rank();
    if from != Square::from_fr(4, home) || !pos.can_castle(us, kingside) {
        return Err(Violation::CastlingRights);
    }
    let rook_from = Square::from_fr(if kingside { 7 } else { 0 }, home);
    let rook_to = Square::from_fr(if kingside { 5 } else { 3 }, home);
    if pos.piece_at(rook_from) != Some(Piece::new(us, PieceType::Rook)) {
        return Err(Violation::CastlingRights);
    }
    if let Some(sq) = between(from, rook_from).into_iter().find(|&s| !pos.is_empty(s)) {
        return Err(Violation::CastlingPathBlocked { sq });
    }
    let them = us.other();
    for sq in [from, rook_to, to] {
        if let Some(&by) = attackers(pos, sq, them).first() {
            return Err(Violation::CastlingThroughCheck { sq, by });
        }
    }
    Ok(Kind::Castle { rook_from, rook_to })
}

/// The successor of `pos` by `mv`, or the first statement that fails.
pub fn apply(pos: &Position, mv: Move) -> Result<Position, Violation> {
    let us = pos.side;
    let piece = match pos.piece_at(mv.from) {
        Some(p) if p.colour == us => p,
        _ => return Err(Violation::NoPieceOfMover { from: mv.from }),
    };
    let kind = classify(pos, mv, piece)?;

    let mut n = pos.clone();
    n.set(mv.from, None);
    n.set(mv.to, Some(mv.promotion.map_or(piece, |k| Piece::new(us, k))));
    match kind {
        Kind::EnPassant { captured } => n.set(captured, None),
        Kind::Castle { rook_from, rook_to } => {
            n.set(rook_from, None);
            n.set(rook_to, Some(Piece::new(us, PieceType::Rook)));
        }
        _ => {}
    }
    if let Some(king) = n.king_square(us) {
        if let Some(&by) = attackers(&n, king, us.other()).first() {
            return Err(Violation::KingAttacked { king, by });
        }
    }

    // Castling rights: a king move clears both; a rook leaving or a capture
    // arriving on a home corner clears that corner's right.
    if piece.kind == PieceType::King {
        n.castling &= !(castle_bit(us, true) | castle_bit(us, false));
    }
    for (sq, c, kingside) in [(mv.from, us, true), (mv.from, us, false), (mv.to, us.other(), true), (mv.to, us.other(), false)] {
        if sq == Square::from_fr(if kingside { 7 } else { 0 }, c.home_rank()) {
            n.castling &= !castle_bit(c, kingside);
        }
    }
    n.ep = match kind {
        Kind::DoublePush => Some(mv.from.offset(0, us.forward()).expect("on the board")),
        _ => None,
    };
    let irreversible = piece.kind == PieceType::Pawn || matches!(kind, Kind::Capture | Kind::EnPassant { .. });
    n.halfmove = if irreversible { 0 } else { n.halfmove.saturating_add(1) };
    if us == Colour::Black {
        n.fullmove = n.fullmove.saturating_add(1);
    }
    n.side = us.other();
    Ok(n)
}

/// How a position with no legal move ends.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Terminal {
    /// The side to move is in check with no legal move: it resigns or stalls,
    /// and loses either way. Nothing is proven.
    Checkmate,
    /// The side to move has no legal move and is not in check: it publishes
    /// a stalemate claim, falsified by one legal move, which the claimer
    /// answers with one attacker of its king.
    Stalemate,
}

/// Whether the side to move has no legal move, and why. Advice for a client
/// and the content of a stalemate claim; not part of any certificate.
pub fn terminal(pos: &Position) -> Option<Terminal> {
    if !legal_moves(pos).is_empty() {
        return None;
    }
    Some(if in_check(pos, pos.side) { Terminal::Checkmate } else { Terminal::Stalemate })
}

/// Checks a claimed successor against the computed one, naming the first
/// field, or square, that differs.
pub fn verify(pos: &Position, mv: Move, claimed: &Position) -> Result<(), Violation> {
    let n = apply(pos, mv)?;
    if let Some(sq) = Square::all().find(|&s| n.nibble_at(s) != claimed.nibble_at(s)) {
        return Err(Violation::BoardMismatch { sq });
    }
    if n.side != claimed.side {
        return Err(Violation::SideMismatch);
    }
    if n.castling != claimed.castling {
        return Err(Violation::CastlingFieldMismatch);
    }
    if n.ep != claimed.ep {
        return Err(Violation::EpFieldMismatch);
    }
    if n.halfmove != claimed.halfmove {
        return Err(Violation::ClockMismatch);
    }
    if n.fullmove != claimed.fullmove {
        return Err(Violation::MoveNumberMismatch);
    }
    Ok(())
}

/// Whether `sq` is attacked by `by` in `pos`; re-exported here so rule
/// callers have one import.
pub fn attacked(pos: &Position, sq: Square, by: Colour) -> bool {
    is_attacked(pos, sq, by)
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn opening_moves() {
        let s = Position::start();
        let s1 = apply(&s, mv("e2e4")).unwrap();
        assert_eq!(s1.to_fen(), "rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1");
        let s2 = apply(&s1, mv("g8f6")).unwrap();
        assert_eq!(s2.to_fen(), "rnbqkb1r/pppppppp/5n2/8/4P3/8/PPPP1PPP/RNBQKBNR w KQkq - 1 2");
        assert_eq!(apply(&s, mv("e2e5")), Err(Violation::BadGeometry { from: sq("e2"), to: sq("e5") }));
        assert_eq!(apply(&s, mv("a1a3")), Err(Violation::RayBlocked { sq: sq("a2") }));
        assert_eq!(apply(&s, mv("e7e5")), Err(Violation::NoPieceOfMover { from: sq("e7") }));
        assert_eq!(apply(&s, mv("d1e1")), Err(Violation::DestinationOwnPiece { to: sq("e1") }));
        assert_eq!(apply(&s, mv("e2d3")), Err(Violation::PawnCaptureNoTarget { to: sq("d3") }));
    }

    #[test]
    fn en_passant() {
        let s = pos("rnbqkbnr/ppp1pppp/8/3pP3/8/8/PPPP1PPP/RNBQKBNR w KQkq d6 0 3");
        let n = apply(&s, mv("e5d6")).unwrap();
        assert_eq!(n.to_fen(), "rnbqkbnr/ppp1pppp/3P4/8/8/8/PPPP1PPP/RNBQKBNR b KQkq - 0 3");
        // the same capture without the ep square is a capture of nothing
        let s = pos("rnbqkbnr/ppp1pppp/8/3pP3/8/8/PPPP1PPP/RNBQKBNR w KQkq - 0 3");
        assert_eq!(apply(&s, mv("e5d6")), Err(Violation::PawnCaptureNoTarget { to: sq("d6") }));
        // the horizontal pin: ep exposes the king along the rank
        let s = pos("8/8/8/KPp4r/8/8/8/4k3 w - c6 0 1");
        assert!(matches!(apply(&s, mv("b5c6")), Err(Violation::KingAttacked { by, .. }) if by == sq("h5")));
    }

    #[test]
    fn castling() {
        let s = pos("r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1");
        let n = apply(&s, mv("e1g1")).unwrap();
        assert_eq!(n.to_fen(), "r3k2r/8/8/8/8/8/8/R4RK1 b kq - 1 1");
        let n = apply(&s, mv("e1c1")).unwrap();
        assert_eq!(n.to_fen(), "r3k2r/8/8/8/8/8/8/2KR3R b kq - 1 1");
        let s = pos("r3k2r/8/8/8/8/8/8/R3K2R w Kkq - 0 1");
        assert_eq!(apply(&s, mv("e1c1")), Err(Violation::CastlingRights));
        let s = pos("r3k2r/8/8/8/8/8/8/RN2K2R w KQkq - 0 1");
        assert_eq!(apply(&s, mv("e1c1")), Err(Violation::CastlingPathBlocked { sq: sq("b1") }));
        // through check: f1 attacked by the rook on f8
        let s = pos("r4rk1/8/8/8/8/8/8/R3K2R w KQ - 0 1");
        assert_eq!(apply(&s, mv("e1g1")), Err(Violation::CastlingThroughCheck { sq: sq("f1"), by: sq("f8") }));
        assert!(apply(&s, mv("e1c1")).is_ok());
        // out of check
        let s = pos("4r1k1/8/8/8/8/8/8/R3K2R w KQ - 0 1");
        assert_eq!(apply(&s, mv("e1g1")), Err(Violation::CastlingThroughCheck { sq: sq("e1"), by: sq("e8") }));
        // b1 attacked does not stop queenside castling
        let s = pos("1r4k1/8/8/8/8/8/8/R3K2R w KQ - 0 1");
        assert!(apply(&s, mv("e1c1")).is_ok());
        // a rook capture on h8 removes black's kingside right
        let s = pos("r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1");
        let n = apply(&s, mv("h1h8")).unwrap();
        assert_eq!(n.castling, crate::position::CASTLE_WQ | crate::position::CASTLE_BQ);
    }

    #[test]
    fn promotion_and_terminal() {
        let s = pos("8/P6k/8/8/8/8/8/K7 w - - 0 1");
        assert_eq!(apply(&s, mv("a7a8")), Err(Violation::PromotionRequired));
        let n = apply(&s, mv("a7a8q")).unwrap();
        assert_eq!(terminal(&n), None);
        assert_eq!(apply(&Position::start(), mv("e2e4q")), Err(Violation::PromotionNotAllowed));
        // fool's mate
        let mut s = Position::start();
        for m in ["f2f3", "e7e5", "g2g4"] {
            s = apply(&s, mv(m)).unwrap();
        }
        let n = apply(&s, mv("d8h4")).unwrap();
        assert_eq!(terminal(&n), Some(Terminal::Checkmate));
        assert!(matches!(apply(&n, mv("e1f2")), Err(Violation::KingAttacked { .. })));
        // the queen on c7 stalemates the king on a8, on c8 mates it
        let s = pos("k7/8/1K6/8/8/8/8/2Q5 w - - 0 1");
        assert_eq!(terminal(&apply(&s, mv("c1c7")).unwrap()), Some(Terminal::Stalemate));
        assert_eq!(terminal(&apply(&s, mv("c1c8")).unwrap()), Some(Terminal::Checkmate));
        assert_eq!(terminal(&apply(&s, mv("c1c6")).unwrap()), None);
    }

    #[test]
    fn verify_names_the_field() {
        let s = Position::start();
        let mut claimed = apply(&s, mv("e2e4")).unwrap();
        assert_eq!(verify(&s, mv("e2e4"), &claimed), Ok(()));
        claimed.set(sq("e4"), None);
        assert_eq!(verify(&s, mv("e2e4"), &claimed), Err(Violation::BoardMismatch { sq: sq("e4") }));
        let mut claimed = apply(&s, mv("e2e4")).unwrap();
        claimed.halfmove = 3;
        assert_eq!(verify(&s, mv("e2e4"), &claimed), Err(Violation::ClockMismatch));
        let mut claimed = apply(&s, mv("e2e4")).unwrap();
        claimed.ep = None;
        assert_eq!(verify(&s, mv("e2e4"), &claimed), Err(Violation::EpFieldMismatch));
    }
}
