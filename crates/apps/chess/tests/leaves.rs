//! The Script leaves against the Rust checker, through the simulator: for
//! every (prior, move, after, challenge) tried, the leaf leaves true exactly
//! when `certificate::check` does. Also prints each leaf's size.

use lngap_chess::certificate::{check, find, mechanical_successor, Challenge};
use lngap_chess::leaf::{leaf, simulate, witness, Kind};
use lngap_chess::movegen::candidates;
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
    fn square(&mut self) -> Square {
        Square::new(self.below(64) as u8).unwrap()
    }
}

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

/// The challenges worth trying on one triple: every exhibit-free kind, every
/// ray index and board square, the attack kinds with the squares that could
/// matter plus a few random ones, and whatever the Rust search finds.
fn challenges(rng: &mut Rng, prior: &Position, mv: Move, after: &Position) -> Vec<Challenge> {
    let mut v = vec![Challenge::Mover, Challenge::Destination, Challenge::Promotion, Challenge::Castling, Challenge::Side, Challenge::CastlingField, Challenge::EpField, Challenge::Clock, Challenge::MoveNumber];
    v.extend((1..=6).map(|j| Challenge::Ray { j }));
    v.extend(Square::all().map(|sq| Challenge::Board { sq }));
    let mut kings: Vec<Square> = after.pieces_of(prior.side).filter(|(_, p)| p.kind == lngap_chess::PieceType::King).map(|(s, _)| s).collect();
    kings.push(rng.square());
    for king in kings {
        for by in Square::all() {
            v.push(Challenge::KingAttacked { king, by });
        }
    }
    let castling_shape = prior.piece_at(mv.from).is_some_and(|p| p.kind == lngap_chess::PieceType::King) && (mv.to.file() as i8 - mv.from.file() as i8).abs() == 2 && mv.to.rank() == mv.from.rank();
    let bys: Vec<Square> = if castling_shape { Square::all().collect() } else { (0..3).map(|_| rng.square()).collect() };
    for by in bys {
        v.push(Challenge::CastlingAttacked { crossed: false, by });
        v.push(Challenge::CastlingAttacked { crossed: true, by });
    }
    v.extend(find(prior, mv, after));
    v
}

fn parity(rng: &mut Rng, prior: &Position, mv: Move, after: &Position) -> usize {
    let cs = challenges(rng, prior, mv, after);
    for &c in &cs {
        let want = check(prior, mv, after, c);
        match simulate(prior, mv, after, c) {
            Ok(got) => assert_eq!(got, want, "{c:?} on {mv} from {} to {}", prior.to_fen(), after.to_fen()),
            Err(e) => panic!("{c:?} on {mv} from {} to {}: script error {e}", prior.to_fen(), after.to_fen()),
        }
    }
    cs.len()
}

fn triples(rng: &mut Rng, positions: &[Position]) -> Vec<(Position, Move, Position)> {
    let mut out = Vec::new();
    for p in positions {
        let legal = legal_moves(p);
        // one legal move with its true successor, one with a corrupted square
        let m = legal[rng.below(legal.len())];
        let after = apply(p, m).unwrap();
        out.push((p.clone(), m, after.clone()));
        let mut bad = after.clone();
        let sq = rng.square();
        bad.set(sq, lngap_chess::Piece::from_nibble([0, 1, 4, 9, 14][rng.below(5)]).unwrap());
        out.push((p.clone(), m, bad));
        // two rejected candidates
        let rejected: Vec<Move> = candidates(p).into_iter().filter(|&m| apply(p, m).is_err()).collect();
        for _ in 0..2 {
            if !rejected.is_empty() {
                let m = rejected[rng.below(rejected.len())];
                out.push((p.clone(), m, mechanical_successor(p, m)));
            }
        }
        // a random move word
        if let Ok(m) = Move::from_u16(rng.next() as u16) {
            out.push((p.clone(), m, mechanical_successor(p, m)));
        }
    }
    out
}

#[test]
fn leaf_sizes() {
    let mut total = 0;
    for k in Kind::ALL {
        let l = leaf(k);
        println!("SIZE leaf {k:?}: {} B", l.len());
        total += l.len();
    }
    println!("SIZE all thirteen leaves: {total} B");
}

#[test]
fn leaves_match_checker_small() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let positions = sample(&mut rng, 1, 6);
    let mut n = 0;
    for (p, m, a) in triples(&mut rng, &positions) {
        n += parity(&mut rng, &p, m, &a);
    }
    println!("{n} challenges simulated");
    assert!(n > 5_000);
}

#[test]
fn out_of_range_exhibits_fail() {
    let p = Position::start();
    let m = Move::parse("e2e4").unwrap();
    let a = apply(&p, m).unwrap();
    for (c, idx) in [(Challenge::Board { sq: Square::new(0).unwrap() }, 0), (Challenge::KingAttacked { king: Square::new(4).unwrap(), by: Square::new(0).unwrap() }, 1)] {
        let mut w = witness(&p, m, &a, c);
        let l = w.len();
        w[l - 1 - idx] = 64;
        assert!(lngap_script32::sim::run_nums(&leaf(Kind::of(c)), w).is_err(), "{c:?} with an index of 64 must fail");
    }
}

#[test]
#[ignore]
fn leaves_match_checker_large() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let positions = sample(&mut rng, 20, 40);
    let mut n = 0;
    for (p, m, a) in triples(&mut rng, &positions) {
        n += parity(&mut rng, &p, m, &a);
    }
    println!("{n} challenges simulated");
}

#[test]
#[ignore]
fn full_space_on_a_few_positions() {
    let mut rng = Rng(0xfeed_beef_dead_f00d);
    let positions = sample(&mut rng, 1, 3);
    let all = Challenge::all();
    for p in positions.iter().take(6) {
        let legal = legal_moves(p);
        let m = legal[rng.below(legal.len())];
        let a = apply(p, m).unwrap();
        for &c in &all {
            assert_eq!(simulate(p, m, &a, c).unwrap(), check(p, m, &a, c), "{c:?} on {m} from {}", p.to_fen());
        }
    }
}
