//! Chess as a state machine for the fact-chain venue (docs/planning/
//! CHESS_ON_FACTCHAIN.md). Standalone: no dependency on the contract
//! machinery, because chess lie proofs are claims over a certificate, not
//! disprove leaves, and that machinery is built after the format is fixed.
//!
//! What this crate fixes:
//!
//! - [`Position`]: the 40-byte position a mover publishes after its move:
//!   64 squares as nibbles, side to move, castling rights, en passant
//!   square, halfmove clock, move number. [`Position::to_bytes`] /
//!   [`Position::from_bytes`] are the venue encoding; FEN is for humans and
//!   tests.
//! - [`Move`]: 16 bits, from, to, promotion. Castling is the king's two-square
//!   move; en passant is a pawn capture onto the en passant square.
//! - [`rules`]: legality as a sequence of named statements. Every failure is a
//!   [`Violation`] that names its exhibit (a square, an attacker, a ray
//!   square), the shape a certificate challenge takes. [`rules::apply`]
//!   computes the successor; [`rules::verify`] checks a claimed successor
//!   field by field.
//! - [`certificate`]: the challenge space. A mover's account of its move is
//!   the move and the position after it; every rule is a [`Challenge`] a
//!   challenger names with at most one exhibit, and [`check`] evaluates it
//!   with bounded, Script-shaped work. Written independently of [`rules`]
//!   and fuzzed against it.
//! - [`leaf`]: the ten challenge kinds as Bitcoin Script leaf bodies over the
//!   same inputs (the two boards as 64 nibbles each, the fields, the move,
//!   the exhibit), each leaving true exactly when [`check`] does. Measured in
//!   the script simulator and on regtest; the chess "one step of logic on
//!   Bitcoin" of the design doc.
//! - [`attack`]: square-centric attack computation, "which pieces of colour c
//!   attack square s", used by the rules and by clients.
//! - [`movegen`]: legal move generation, used only for [`terminal`] (mate
//!   and stalemate detection, advice to a client) and for perft verification
//!   against the reference counts.
//!
//! Not here: the end of the game. A checkmated party resigns (a fold, the
//! generic cooperative close) or stalls, and loses either way with nothing
//! proven; a stalemated party publishes a stalemate claim, an entry kind of
//! the venue, falsified by one legal move and defended by one attacker.
//! Also not here: threefold repetition (a history rule, decided outside the
//! position, see the design doc §3), draw offers, insufficient material and
//! the 50-move rule (all cooperative for the PoC; the halfmove clock is
//! maintained but no draw is derived from it).

pub mod attack;
pub mod certificate;
pub mod leaf;
pub mod movegen;
pub mod mv;
pub mod piece;
pub mod position;
pub mod rules;
pub mod square;

pub use attack::{attackers, is_attacked};
pub use certificate::{check, find, Challenge};
pub use movegen::{legal_moves, perft};
pub use mv::Move;
pub use piece::{Colour, Piece, PieceType};
pub use position::Position;
pub use rules::{apply, terminal, verify, Terminal, Violation};
pub use square::Square;
