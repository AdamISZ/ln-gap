//! Squares, indexed a1 = 0, b1 = 1, ..., h8 = 63 (file + 8 * rank), and rays
//! between them. This index is the certificate's square index: "read square
//! i" is one computed-index pick over the 64 nibbles of a board.

use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Square(u8);

impl Square {
    pub const fn new(i: u8) -> Option<Square> {
        if i < 64 {
            Some(Square(i))
        } else {
            None
        }
    }
    /// `file` and `rank` in 0..8 (a = 0, rank 1 = 0).
    pub const fn from_fr(file: u8, rank: u8) -> Square {
        Square(file + 8 * rank)
    }
    pub const fn index(self) -> usize {
        self.0 as usize
    }
    pub const fn u8(self) -> u8 {
        self.0
    }
    pub const fn file(self) -> u8 {
        self.0 & 7
    }
    pub const fn rank(self) -> u8 {
        self.0 >> 3
    }
    /// The square `df` files and `dr` ranks away, if on the board.
    pub fn offset(self, df: i8, dr: i8) -> Option<Square> {
        let f = self.file() as i8 + df;
        let r = self.rank() as i8 + dr;
        if (0..8).contains(&f) && (0..8).contains(&r) {
            Some(Square::from_fr(f as u8, r as u8))
        } else {
            None
        }
    }
    pub fn all() -> impl Iterator<Item = Square> {
        (0..64).map(Square)
    }
    pub fn parse(s: &str) -> Option<Square> {
        let b = s.as_bytes();
        if b.len() != 2 || !(b'a'..=b'h').contains(&b[0]) || !(b'1'..=b'8').contains(&b[1]) {
            return None;
        }
        Some(Square::from_fr(b[0] - b'a', b[1] - b'1'))
    }
    pub const fn mask(self) -> u64 {
        1u64 << self.0
    }
}

impl fmt::Display for Square {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", (b'a' + self.file()) as char, self.rank() + 1)
    }
}
impl fmt::Debug for Square {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// The unit step from `a` towards `b` if they share a rank, file or diagonal
/// and differ; `None` otherwise.
pub fn direction(a: Square, b: Square) -> Option<(i8, i8)> {
    let df = b.file() as i8 - a.file() as i8;
    let dr = b.rank() as i8 - a.rank() as i8;
    if (df == 0 && dr == 0) || !(df == 0 || dr == 0 || df.abs() == dr.abs()) {
        return None;
    }
    Some((df.signum(), dr.signum()))
}

/// The squares strictly between `a` and `b` along their common line, in
/// order from `a`; `None` if they are not aligned. Empty for adjacent squares
/// and knight-like pairs.
pub fn between(a: Square, b: Square) -> Vec<Square> {
    let Some((df, dr)) = direction(a, b) else { return vec![] };
    let mut v = Vec::new();
    let mut s = a;
    loop {
        s = s.offset(df, dr).expect("ray stays on the board until b");
        if s == b {
            return v;
        }
        v.push(s);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_and_rays() {
        let e4 = Square::parse("e4").unwrap();
        assert_eq!(e4.index(), 4 + 8 * 3);
        assert_eq!(e4.to_string(), "e4");
        assert_eq!(Square::parse("i1"), None);
        let a1 = Square::parse("a1").unwrap();
        let h8 = Square::parse("h8").unwrap();
        let ray: Vec<String> = between(a1, h8).iter().map(|s| s.to_string()).collect();
        assert_eq!(ray, ["b2", "c3", "d4", "e5", "f6", "g7"]);
        assert!(between(a1, Square::parse("b3").unwrap()).is_empty());
        assert_eq!(direction(a1, Square::parse("b3").unwrap()), None);
        assert!(between(a1, Square::parse("a2").unwrap()).is_empty());
    }
}
