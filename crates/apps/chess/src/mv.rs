//! A move in 16 bits: from (bits 0..6), to (6..12), promotion piece code
//! (12..15: 0 none, 2 knight, 3 bishop, 4 rook, 5 queen), bit 15 zero.
//! Castling is the king moving two files; en passant is a pawn moving
//! diagonally onto the en passant square. What the move means is decided by
//! the rules against the prior position, never by the move itself.

use crate::piece::PieceType;
use crate::square::Square;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Move {
    pub from: Square,
    pub to: Square,
    pub promotion: Option<PieceType>,
}

impl Move {
    pub const fn new(from: Square, to: Square) -> Move {
        Move { from, to, promotion: None }
    }
    pub const fn promote(from: Square, to: Square, kind: PieceType) -> Move {
        Move { from, to, promotion: Some(kind) }
    }

    pub fn to_u16(self) -> u16 {
        u16::from(self.from.u8()) | (u16::from(self.to.u8()) << 6) | (u16::from(self.promotion.map_or(0, PieceType::code)) << 12)
    }

    /// `Err` names the offending field for a word that is not a move.
    pub fn from_u16(w: u16) -> Result<Move, &'static str> {
        let from = Square::new((w & 63) as u8).expect("6 bits");
        let to = Square::new(((w >> 6) & 63) as u8).expect("6 bits");
        let promotion = match (w >> 12) & 7 {
            0 => None,
            c => match PieceType::from_code(c as u8) {
                Some(k) if k.is_promotion_piece() => Some(k),
                _ => return Err("promotion code"),
            },
        };
        if w >> 15 != 0 {
            return Err("spare bit");
        }
        Ok(Move { from, to, promotion })
    }

    /// UCI form: `e2e4`, `e7e8q`.
    pub fn parse(s: &str) -> Option<Move> {
        if s.len() != 4 && s.len() != 5 {
            return None;
        }
        let from = Square::parse(&s[0..2])?;
        let to = Square::parse(&s[2..4])?;
        let promotion = match s.len() {
            5 => Some(PieceType::from_letter(s.chars().nth(4)?).filter(|k| k.is_promotion_piece())?),
            _ => None,
        };
        Some(Move { from, to, promotion })
    }
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.from, self.to)?;
        if let Some(k) = self.promotion {
            let c = match k {
                PieceType::Knight => 'n',
                PieceType::Bishop => 'b',
                PieceType::Rook => 'r',
                _ => 'q',
            };
            write!(f, "{c}")?;
        }
        Ok(())
    }
}
impl fmt::Debug for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn word_round_trip() {
        for s in ["e2e4", "e7e8q", "a7a8n", "e1g1"] {
            let m = Move::parse(s).unwrap();
            assert_eq!(m.to_string(), s);
            assert_eq!(Move::from_u16(m.to_u16()).unwrap(), m);
        }
        assert_eq!(Move::parse("e7e8k"), None);
        assert_eq!(Move::from_u16(1 << 12), Err("promotion code"));
        assert_eq!(Move::from_u16(6 << 12), Err("promotion code"));
        assert_eq!(Move::from_u16(1 << 15), Err("spare bit"));
    }
}
