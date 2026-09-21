//! The certificate's soundness and completeness, fuzzed against the rules.
//!
//! Soundness: an honest mover cannot be framed. For every legal move from a
//! sampled position, no challenge in the whole space checks.
//! Completeness: a liar is always caught. For rejected candidates, random
//! move words, corrupted successors and lazy successors, some challenge
//! checks.
//! Totality: on random positions, moves and challenges, `check` evaluates.
//!
//! The default tests use a small sample; the ignored ones a large one
//! (`cargo test --release -p lngap-chess --test certificate -- --ignored`).

use lngap_chess::certificate::{check, find, mechanical_successor, Challenge};
use lngap_chess::movegen::candidates;
use lngap_chess::piece::Colour;
use lngap_chess::{apply, legal_moves, Move, Position, Square};

const SEEDS: [&str; 6] = [
    "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
    "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
    "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1",
    "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1",
    "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8",
    "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10",
];

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Positions reached by random play from the seeds, all with a legal move.
fn sample(rng: &mut Rng, playouts: usize, plies: usize) -> Vec<Position> {
    let mut out = Vec::new();
    for fen in SEEDS {
        for _ in 0..playouts {
            let mut p = Position::from_fen(fen).unwrap();
            for _ in 0..plies {
                let moves = legal_moves(&p);
                if moves.is_empty() {
                    break;
                }
                out.push(p.clone());
                p = apply(&p, moves[rng.below(moves.len())]).unwrap();
            }
        }
    }
    out
}

fn soundness(positions: &[Position]) -> usize {
    let mut n = 0;
    for p in positions {
        for m in legal_moves(p) {
            let after = apply(p, m).unwrap();
            if let Some(c) = find(p, m, &after) {
                panic!("legal move {m} from {} challenged by {c:?}", p.to_fen());
            }
            n += 1;
        }
    }
    n
}

fn must_catch(p: &Position, m: Move, after: &Position, what: &str) {
    match find(p, m, after) {
        Some(c) => assert!(check(p, m, after, c)),
        None => panic!("{what}: move {m} from {} to {} not challenged", p.to_fen(), after.to_fen()),
    }
}

fn random_nibble(rng: &mut Rng) -> u8 {
    const VALID: [u8; 13] = [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12, 13, 14];
    VALID[rng.below(13)]
}

fn completeness(rng: &mut Rng, positions: &[Position]) -> usize {
    let mut n = 0;
    for p in positions {
        // near misses: geometric candidates the rules reject
        for m in candidates(p) {
            if apply(p, m).is_err() {
                must_catch(p, m, &mechanical_successor(p, m), "rejected candidate");
                n += 1;
            }
        }
        // random move words
        for _ in 0..16 {
            if let Ok(m) = Move::from_u16(rng.next() as u16) {
                if apply(p, m).is_err() {
                    must_catch(p, m, &mechanical_successor(p, m), "random word");
                    n += 1;
                }
            }
        }
        let legal = legal_moves(p);
        for &m in &legal {
            let after = apply(p, m).unwrap();
            // the lazy liar publishes the prior again
            must_catch(p, m, p, "lazy");
            // a corrupted square
            let mut bad = after.clone();
            let sq = Square::new(rng.below(64) as u8).unwrap();
            let mut nib = random_nibble(rng);
            while nib == after.nibble_at(sq) {
                nib = random_nibble(rng);
            }
            bad.set(sq, lngap_chess::Piece::from_nibble(nib).unwrap());
            must_catch(p, m, &bad, "corrupted square");
            // each field
            let mut bad = after.clone();
            bad.side = bad.side.other();
            must_catch(p, m, &bad, "side");
            let mut bad = after.clone();
            bad.castling ^= 1 << rng.below(4);
            must_catch(p, m, &bad, "castling");
            let mut bad = after.clone();
            bad.ep = match after.ep {
                None => Some(Square::new(rng.below(64) as u8).unwrap()),
                Some(_) => None,
            };
            must_catch(p, m, &bad, "ep");
            let mut bad = after.clone();
            bad.halfmove = bad.halfmove.wrapping_add(1);
            must_catch(p, m, &bad, "clock");
            let mut bad = after.clone();
            bad.fullmove = bad.fullmove.wrapping_add(1);
            must_catch(p, m, &bad, "move number");
            // the successor of a different legal move
            let other = legal[rng.below(legal.len())];
            if other != m {
                let bad = apply(p, other).unwrap();
                if bad != after {
                    must_catch(p, m, &bad, "other move's successor");
                }
            }
            n += 8;
        }
    }
    n
}

fn random_position(rng: &mut Rng) -> Position {
    let mut b = [0u8; 40];
    for byte in b.iter_mut().take(32) {
        *byte = (random_nibble(rng) << 4) | random_nibble(rng);
    }
    b[32] = rng.below(2) as u8;
    b[33] = rng.below(16) as u8;
    b[34] = rng.below(65) as u8;
    b[35] = rng.next() as u8;
    b[36] = rng.next() as u8;
    b[37] = rng.next() as u8;
    Position::from_bytes(&b).unwrap()
}

fn totality(rng: &mut Rng, rounds: usize) {
    let all = Challenge::all();
    for _ in 0..rounds {
        let p = random_position(rng);
        let after = if rng.below(2) == 0 { random_position(rng) } else { p.clone() };
        for _ in 0..4 {
            let Ok(m) = Move::from_u16(rng.next() as u16) else { continue };
            for &c in &all {
                let _ = check(&p, m, &after, c);
            }
            let _ = mechanical_successor(&p, m);
        }
    }
    let _ = Colour::White;
}

#[test]
fn sound_on_a_small_sample() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let positions = sample(&mut rng, 1, 8);
    let n = soundness(&positions);
    assert!(n > 500, "{n} legal moves checked");
}

#[test]
fn complete_on_a_small_sample() {
    let mut rng = Rng(0xd1b54a32d192ed03);
    let positions = sample(&mut rng, 1, 8);
    let n = completeness(&mut rng, &positions);
    assert!(n > 2_000, "{n} lies caught");
}

#[test]
fn total_on_random_positions() {
    let mut rng = Rng(0x2545f4914f6cdd1d);
    totality(&mut rng, 20);
}

#[test]
#[ignore]
fn sound_on_a_large_sample() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let positions = sample(&mut rng, 40, 60);
    let n = soundness(&positions);
    println!("soundness: {} positions, {n} legal moves, no challenge", positions.len());
}

#[test]
#[ignore]
fn complete_on_a_large_sample() {
    let mut rng = Rng(0xd1b54a32d192ed03);
    let positions = sample(&mut rng, 40, 60);
    let n = completeness(&mut rng, &positions);
    println!("completeness: {} positions, {n} lies caught", positions.len());
}

#[test]
#[ignore]
fn total_on_many_random_positions() {
    let mut rng = Rng(0x2545f4914f6cdd1d);
    totality(&mut rng, 2_000);
}
