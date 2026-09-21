//! Pieces and their nibble encoding: bit 3 is the colour (0 white, 1 black),
//! bits 0..3 the kind (1 pawn .. 6 king); 0 is an empty square. The values
//! 7, 8 and 15 decode to nothing and are false statements wherever they
//! appear in a published position.

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Colour {
    White,
    Black,
}

impl Colour {
    pub fn other(self) -> Colour {
        match self {
            Colour::White => Colour::Black,
            Colour::Black => Colour::White,
        }
    }
    /// The direction a pawn of this colour advances in ranks.
    pub fn forward(self) -> i8 {
        match self {
            Colour::White => 1,
            Colour::Black => -1,
        }
    }
    /// The rank pawns of this colour start on (0-based).
    pub fn pawn_rank(self) -> u8 {
        match self {
            Colour::White => 1,
            Colour::Black => 6,
        }
    }
    /// The rank this colour's king and rooks start on (0-based).
    pub fn home_rank(self) -> u8 {
        match self {
            Colour::White => 0,
            Colour::Black => 7,
        }
    }
    /// The rank a pawn of this colour promotes on (0-based).
    pub fn last_rank(self) -> u8 {
        self.other().home_rank()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum PieceType {
    Pawn = 1,
    Knight = 2,
    Bishop = 3,
    Rook = 4,
    Queen = 5,
    King = 6,
}

impl PieceType {
    pub fn from_code(c: u8) -> Option<PieceType> {
        Some(match c {
            1 => PieceType::Pawn,
            2 => PieceType::Knight,
            3 => PieceType::Bishop,
            4 => PieceType::Rook,
            5 => PieceType::Queen,
            6 => PieceType::King,
            _ => return None,
        })
    }
    pub fn code(self) -> u8 {
        self as u8
    }
    pub fn is_promotion_piece(self) -> bool {
        matches!(self, PieceType::Knight | PieceType::Bishop | PieceType::Rook | PieceType::Queen)
    }
    fn letter(self) -> char {
        match self {
            PieceType::Pawn => 'p',
            PieceType::Knight => 'n',
            PieceType::Bishop => 'b',
            PieceType::Rook => 'r',
            PieceType::Queen => 'q',
            PieceType::King => 'k',
        }
    }
    pub fn from_letter(c: char) -> Option<PieceType> {
        Some(match c.to_ascii_lowercase() {
            'p' => PieceType::Pawn,
            'n' => PieceType::Knight,
            'b' => PieceType::Bishop,
            'r' => PieceType::Rook,
            'q' => PieceType::Queen,
            'k' => PieceType::King,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Piece {
    pub colour: Colour,
    pub kind: PieceType,
}

impl Piece {
    pub const fn new(colour: Colour, kind: PieceType) -> Piece {
        Piece { colour, kind }
    }
    pub fn nibble(self) -> u8 {
        let c = match self.colour {
            Colour::White => 0,
            Colour::Black => 8,
        };
        c | self.kind.code()
    }
    /// `Ok(None)` for 0 (empty), `Err` for the three values that are no piece.
    pub fn from_nibble(n: u8) -> Result<Option<Piece>, u8> {
        if n == 0 {
            return Ok(None);
        }
        let colour = if n & 8 != 0 { Colour::Black } else { Colour::White };
        match PieceType::from_code(n & 7) {
            Some(kind) => Ok(Some(Piece { colour, kind })),
            None => Err(n),
        }
    }
    /// FEN letter: upper case white, lower case black.
    pub fn fen_char(self) -> char {
        let c = self.kind.letter();
        match self.colour {
            Colour::White => c.to_ascii_uppercase(),
            Colour::Black => c,
        }
    }
    pub fn from_fen_char(c: char) -> Option<Piece> {
        let kind = PieceType::from_letter(c)?;
        let colour = if c.is_ascii_uppercase() { Colour::White } else { Colour::Black };
        Some(Piece { colour, kind })
    }
}
