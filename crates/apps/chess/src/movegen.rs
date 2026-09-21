//! Legal move generation: geometric candidates from each piece of the side
//! to move, filtered by the rules. Exists for mate and stalemate detection
//! and for perft; play and search are not this crate's business.

use crate::mv::Move;
use crate::piece::PieceType;
use crate::position::Position;
use crate::rules::apply;
use crate::square::Square;

const KNIGHT: [(i8, i8); 8] = [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)];
const KING: [(i8, i8); 8] = [(0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)];
const BISHOP: [(i8, i8); 4] = [(1, 1), (1, -1), (-1, -1), (-1, 1)];
const ROOK: [(i8, i8); 4] = [(0, 1), (1, 0), (0, -1), (-1, 0)];
const PROMOTIONS: [PieceType; 4] = [PieceType::Queen, PieceType::Rook, PieceType::Bishop, PieceType::Knight];

fn slide(pos: &Position, from: Square, dirs: &[(i8, i8)], out: &mut Vec<Move>) {
    for &(df, dr) in dirs {
        let mut s = from;
        while let Some(t) = s.offset(df, dr) {
            out.push(Move::new(from, t));
            if !pos.is_empty(t) {
                break;
            }
            s = t;
        }
    }
}

/// Candidate moves by geometry alone; the rules reject the rest. Public
/// for the certificate's completeness test, which needs near-misses.
pub fn candidates(pos: &Position) -> Vec<Move> {
    let us = pos.side;
    let mut out = Vec::with_capacity(64);
    for (from, p) in pos.pieces_of(us) {
        match p.kind {
            PieceType::Pawn => {
                let fwd = us.forward();
                let mut targets = Vec::with_capacity(4);
                if let Some(t) = from.offset(0, fwd) {
                    targets.push(t);
                    if from.rank() == us.pawn_rank() {
                        targets.push(from.offset(0, 2 * fwd).expect("on the board"));
                    }
                }
                targets.extend(from.offset(-1, fwd));
                targets.extend(from.offset(1, fwd));
                for t in targets {
                    if t.rank() == us.last_rank() {
                        out.extend(PROMOTIONS.iter().map(|&k| Move::promote(from, t, k)));
                    } else {
                        out.push(Move::new(from, t));
                    }
                }
            }
            PieceType::Knight => out.extend(KNIGHT.iter().filter_map(|&(df, dr)| from.offset(df, dr)).map(|t| Move::new(from, t))),
            PieceType::Bishop => slide(pos, from, &BISHOP, &mut out),
            PieceType::Rook => slide(pos, from, &ROOK, &mut out),
            PieceType::Queen => {
                slide(pos, from, &BISHOP, &mut out);
                slide(pos, from, &ROOK, &mut out);
            }
            PieceType::King => {
                out.extend(KING.iter().filter_map(|&(df, dr)| from.offset(df, dr)).map(|t| Move::new(from, t)));
                out.extend([2, -2].iter().filter_map(|&df| from.offset(df, 0)).map(|t| Move::new(from, t)));
            }
        }
    }
    out
}

/// Every legal move from `pos`, with its successor.
pub fn legal_moves_with(pos: &Position) -> Vec<(Move, Position)> {
    candidates(pos).into_iter().filter_map(|m| apply(pos, m).ok().map(|n| (m, n))).collect()
}

pub fn legal_moves(pos: &Position) -> Vec<Move> {
    legal_moves_with(pos).into_iter().map(|(m, _)| m).collect()
}

/// The number of leaf nodes at `depth` plies, the standard correctness
/// test for move generation.
pub fn perft(pos: &Position, depth: u32) -> u64 {
    if depth == 0 {
        return 1;
    }
    let next = legal_moves_with(pos);
    if depth == 1 {
        return next.len() as u64;
    }
    next.iter().map(|(_, n)| perft(n, depth - 1)).sum()
}

/// Per-move counts at `depth`, for locating a perft discrepancy.
pub fn perft_divide(pos: &Position, depth: u32) -> Vec<(Move, u64)> {
    legal_moves_with(pos).into_iter().map(|(m, n)| (m, perft(&n, depth - 1))).collect()
}
