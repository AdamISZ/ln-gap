//! The position: what a mover publishes after its move, in 40 bytes.
//!
//! Byte layout (`to_bytes`):
//!
//! ```text
//!     0..32   the 64 squares as nibbles, square 2k in the high nibble of
//!             byte k and square 2k+1 in the low nibble (piece.rs)
//!     32      side to move: 0 white, 1 black
//!     33      castling rights: 1 WK, 2 WQ, 4 BK, 8 BQ
//!     34      en passant square (0..64), 64 for none
//!     35      halfmove clock (0..=255; informational for the PoC)
//!     36..38  move number, big endian
//!     38..40  zero
//!
//! There is no status field. A checkmated party resigns (a fold) or stalls,
//! and either way loses without any mate being proven; a stalemated party
//! publishes a stalemate claim, which is an entry kind of the venue, not a
//! field of the position (design doc §3).
//! ```
//!
//! Every field is a fixed-width value with an explicit range, so that a
//! published position that decodes to nothing is a false statement rather
//! than an undefined one. `from_bytes` reports the first offending byte.

use crate::piece::{Colour, Piece, PieceType};
use crate::square::Square;
use std::fmt;

pub const CASTLE_WK: u8 = 1;
pub const CASTLE_WQ: u8 = 2;
pub const CASTLE_BK: u8 = 4;
pub const CASTLE_BQ: u8 = 8;

pub const START_FEN: &str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Position {
    squares: [u8; 64],
    pub side: Colour,
    pub castling: u8,
    pub ep: Option<Square>,
    pub halfmove: u8,
    pub fullmove: u16,
}

/// A byte string that is not a position: the byte offset and its value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Malformed {
    pub offset: usize,
    pub value: u8,
}

impl fmt::Display for Malformed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "byte {} has value {:#x}", self.offset, self.value)
    }
}
impl std::error::Error for Malformed {}

impl Position {
    pub fn empty() -> Position {
        Position { squares: [0; 64], side: Colour::White, castling: 0, ep: None, halfmove: 0, fullmove: 1 }
    }
    pub fn start() -> Position {
        Position::from_fen(START_FEN).expect("the start position parses")
    }

    pub fn piece_at(&self, sq: Square) -> Option<Piece> {
        Piece::from_nibble(self.squares[sq.index()]).expect("a Position holds only valid nibbles")
    }
    pub fn nibble_at(&self, sq: Square) -> u8 {
        self.squares[sq.index()]
    }
    pub fn set(&mut self, sq: Square, p: Option<Piece>) {
        self.squares[sq.index()] = p.map_or(0, Piece::nibble);
    }
    pub fn is_empty(&self, sq: Square) -> bool {
        self.squares[sq.index()] == 0
    }
    /// The squares holding pieces of `c`.
    pub fn pieces_of(&self, c: Colour) -> impl Iterator<Item = (Square, Piece)> + '_ {
        Square::all().filter_map(move |sq| self.piece_at(sq).filter(|p| p.colour == c).map(|p| (sq, p)))
    }
    /// The first king of `c` found; `None` in a position without one.
    pub fn king_square(&self, c: Colour) -> Option<Square> {
        self.pieces_of(c).find(|(_, p)| p.kind == PieceType::King).map(|(s, _)| s)
    }
    pub fn can_castle(&self, c: Colour, kingside: bool) -> bool {
        self.castling & castle_bit(c, kingside) != 0
    }

    pub fn to_bytes(&self) -> [u8; 40] {
        let mut b = [0u8; 40];
        for (k, byte) in b.iter_mut().enumerate().take(32) {
            *byte = (self.squares[2 * k] << 4) | self.squares[2 * k + 1];
        }
        b[32] = match self.side {
            Colour::White => 0,
            Colour::Black => 1,
        };
        b[33] = self.castling;
        b[34] = self.ep.map_or(64, Square::u8);
        b[35] = self.halfmove;
        b[36..38].copy_from_slice(&self.fullmove.to_be_bytes());
        b
    }

    pub fn from_bytes(b: &[u8; 40]) -> Result<Position, Malformed> {
        let mut p = Position::empty();
        for (k, &byte) in b.iter().enumerate().take(32) {
            for (j, n) in [byte >> 4, byte & 15].into_iter().enumerate() {
                Piece::from_nibble(n).map_err(|_| Malformed { offset: k, value: byte })?;
                p.squares[2 * k + j] = n;
            }
        }
        p.side = match b[32] {
            0 => Colour::White,
            1 => Colour::Black,
            v => return Err(Malformed { offset: 32, value: v }),
        };
        if b[33] > 15 {
            return Err(Malformed { offset: 33, value: b[33] });
        }
        p.castling = b[33];
        p.ep = match b[34] {
            64 => None,
            v => Some(Square::new(v).ok_or(Malformed { offset: 34, value: v })?),
        };
        p.halfmove = b[35];
        p.fullmove = u16::from_be_bytes([b[36], b[37]]);
        if let Some((offset, &value)) = b.iter().enumerate().skip(38).find(|(_, &v)| v != 0) {
            return Err(Malformed { offset, value });
        }
        Ok(p)
    }

    /// Standard FEN.
    pub fn from_fen(fen: &str) -> Result<Position, String> {
        let fields: Vec<&str> = fen.split_whitespace().collect();
        if fields.len() < 4 || fields.len() > 6 {
            return Err(format!("FEN has {} fields", fields.len()));
        }
        let mut p = Position::empty();
        let ranks: Vec<&str> = fields[0].split('/').collect();
        if ranks.len() != 8 {
            return Err(format!("FEN has {} ranks", ranks.len()));
        }
        for (i, r) in ranks.iter().enumerate() {
            let rank = 7 - i as u8;
            let mut file = 0u8;
            for c in r.chars() {
                if let Some(d) = c.to_digit(10) {
                    file += d as u8;
                } else {
                    let piece = Piece::from_fen_char(c).ok_or_else(|| format!("bad piece {c:?}"))?;
                    if file > 7 {
                        return Err(format!("rank {} overflows", rank + 1));
                    }
                    p.set(Square::from_fr(file, rank), Some(piece));
                    file += 1;
                }
            }
            if file != 8 {
                return Err(format!("rank {} has {file} files", rank + 1));
            }
        }
        p.side = match fields[1] {
            "w" => Colour::White,
            "b" => Colour::Black,
            s => return Err(format!("bad side {s:?}")),
        };
        if fields[2] != "-" {
            for c in fields[2].chars() {
                p.castling |= match c {
                    'K' => CASTLE_WK,
                    'Q' => CASTLE_WQ,
                    'k' => CASTLE_BK,
                    'q' => CASTLE_BQ,
                    _ => return Err(format!("bad castling {c:?}")),
                };
            }
        }
        if fields[3] != "-" {
            p.ep = Some(Square::parse(fields[3]).ok_or_else(|| format!("bad ep square {:?}", fields[3]))?);
        }
        if let Some(h) = fields.get(4) {
            p.halfmove = h.parse().map_err(|_| format!("bad halfmove clock {h:?}"))?;
        }
        if let Some(m) = fields.get(5) {
            p.fullmove = m.parse().map_err(|_| format!("bad move number {m:?}"))?;
        }
        Ok(p)
    }

    pub fn to_fen(&self) -> String {
        let mut s = String::new();
        for rank in (0..8).rev() {
            let mut run = 0;
            for file in 0..8 {
                match self.piece_at(Square::from_fr(file, rank)) {
                    Some(p) => {
                        if run > 0 {
                            s.push(char::from(b'0' + run));
                            run = 0;
                        }
                        s.push(p.fen_char());
                    }
                    None => run += 1,
                }
            }
            if run > 0 {
                s.push(char::from(b'0' + run));
            }
            if rank > 0 {
                s.push('/');
            }
        }
        s.push(' ');
        s.push(match self.side {
            Colour::White => 'w',
            Colour::Black => 'b',
        });
        s.push(' ');
        if self.castling == 0 {
            s.push('-');
        } else {
            for (bit, c) in [(CASTLE_WK, 'K'), (CASTLE_WQ, 'Q'), (CASTLE_BK, 'k'), (CASTLE_BQ, 'q')] {
                if self.castling & bit != 0 {
                    s.push(c);
                }
            }
        }
        s.push(' ');
        match self.ep {
            Some(sq) => s.push_str(&sq.to_string()),
            None => s.push('-'),
        }
        s.push_str(&format!(" {} {}", self.halfmove, self.fullmove));
        s
    }
}

pub fn castle_bit(c: Colour, kingside: bool) -> u8 {
    match (c, kingside) {
        (Colour::White, true) => CASTLE_WK,
        (Colour::White, false) => CASTLE_WQ,
        (Colour::Black, true) => CASTLE_BK,
        (Colour::Black, false) => CASTLE_BQ,
    }
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_fen())
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for rank in (0..8).rev() {
            for file in 0..8 {
                let c = self.piece_at(Square::from_fr(file, rank)).map_or('.', Piece::fen_char);
                write!(f, "{c}")?;
            }
            writeln!(f)?;
        }
        write!(f, "{:?}", self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fen_and_bytes_round_trip() {
        for fen in [
            START_FEN,
            "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
            "rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR b KQkq e3 0 1",
            "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1",
        ] {
            let p = Position::from_fen(fen).unwrap();
            assert_eq!(p.to_fen(), fen);
            let b = p.to_bytes();
            assert_eq!(Position::from_bytes(&b).unwrap(), p);
        }
        let p = Position::start();
        assert_eq!(p.piece_at(Square::parse("e1").unwrap()), Some(Piece::new(Colour::White, PieceType::King)));
        assert_eq!(p.king_square(Colour::Black), Square::parse("e8"));
    }

    #[test]
    fn malformed_bytes_name_the_byte() {
        let mut b = Position::start().to_bytes();
        b[3] = 0x77;
        assert_eq!(Position::from_bytes(&b).unwrap_err(), Malformed { offset: 3, value: 0x77 });
        let mut b = Position::start().to_bytes();
        b[34] = 65;
        assert_eq!(Position::from_bytes(&b).unwrap_err().offset, 34);
        for offset in [38, 39] {
            let mut b = Position::start().to_bytes();
            b[offset] = 1;
            assert_eq!(Position::from_bytes(&b).unwrap_err().offset, offset);
        }
    }
}
