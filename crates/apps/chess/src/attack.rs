//! Square-centric attacks: which pieces of a colour attack a square. This
//! is the content of the certificate's attack bitboards ("square s is
//! attacked by this set of pieces"), and the shape of the exhibit against
//! a king-safety statement: one attacker square, whose geometry and ray
//! the checker verifies.

use crate::piece::{Colour, Piece, PieceType};
use crate::position::Position;
use crate::square::{between, Square};

/// Whether a piece on `from` attacks `to` by geometry alone (blockers
/// ignored). For pawns this is the capture geometry, not the push.
pub fn attacks_geometrically(p: Piece, from: Square, to: Square) -> bool {
    if from == to {
        return false;
    }
    let df = (to.file() as i8 - from.file() as i8).abs();
    let dr = to.rank() as i8 - from.rank() as i8;
    match p.kind {
        PieceType::Pawn => df == 1 && dr == p.colour.forward(),
        PieceType::Knight => (df == 1 && dr.abs() == 2) || (df == 2 && dr.abs() == 1),
        PieceType::Bishop => df == dr.abs(),
        PieceType::Rook => df == 0 || dr == 0,
        PieceType::Queen => df == dr.abs() || df == 0 || dr == 0,
        PieceType::King => df <= 1 && dr.abs() <= 1,
    }
}

/// Whether the piece on `from` in `pos` attacks `to`: geometry plus, for
/// sliders, an empty ray.
pub fn attacks(pos: &Position, from: Square, to: Square) -> bool {
    match pos.piece_at(from) {
        Some(p) if attacks_geometrically(p, from, to) => between(from, to).iter().all(|&s| pos.is_empty(s)),
        _ => false,
    }
}

/// The squares holding pieces of `by` that attack `sq`.
pub fn attackers(pos: &Position, sq: Square, by: Colour) -> Vec<Square> {
    pos.pieces_of(by).filter(|&(from, _)| attacks(pos, from, sq)).map(|(from, _)| from).collect()
}

/// The same as a 64-bit mask, the certificate's entry for `sq`.
pub fn attacker_mask(pos: &Position, sq: Square, by: Colour) -> u64 {
    attackers(pos, sq, by).into_iter().fold(0, |m, s| m | s.mask())
}

pub fn is_attacked(pos: &Position, sq: Square, by: Colour) -> bool {
    pos.pieces_of(by).any(|(from, _)| attacks(pos, from, sq))
}

/// Whether the king of `c` is attacked; `false` if `c` has no king.
pub fn in_check(pos: &Position, c: Colour) -> bool {
    pos.king_square(c).is_some_and(|k| is_attacked(pos, k, c.other()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sq(s: &str) -> Square {
        Square::parse(s).unwrap()
    }

    #[test]
    fn attackers_of_a_square() {
        let p = Position::from_fen("r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1").unwrap();
        let mut a = attackers(&p, sq("d5"), Colour::Black);
        a.sort();
        assert_eq!(a, vec![sq("b6"), sq("e6"), sq("f6")]);
        assert_eq!(attackers(&p, sq("d5"), Colour::White), vec![sq("c3"), sq("e4")], "the pawn on d5 does not attack its own square");
        assert!(!is_attacked(&p, sq("e1"), Colour::Black));
        assert!(!in_check(&p, Colour::White));
        assert!(!in_check(&p, Colour::Black));
        // a slider behind a blocker does not attack
        let p = Position::start();
        assert!(!attacks(&p, sq("a1"), sq("a3")));
        assert!(attacks(&p, sq("b1"), sq("c3")));
        assert!(attacks(&p, sq("e2"), sq("d3")));
        assert!(!attacks(&p, sq("e2"), sq("e3")), "a pawn push is not an attack");
    }
}
