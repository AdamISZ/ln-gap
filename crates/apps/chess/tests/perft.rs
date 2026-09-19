//! Reference perft counts from https://www.chessprogramming.org/Perft_Results.
//! Depth 4 and beyond for the larger positions run only with `--ignored`
//! (`cargo test --release -p lngap-chess -- --ignored`).

use lngap_chess::{perft, Position};

const CASES: [(&str, [u64; 5]); 6] = [
    ("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", [20, 400, 8_902, 197_281, 4_865_609]),
    ("r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", [48, 2_039, 97_862, 4_085_603, 193_690_690]),
    ("8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", [14, 191, 2_812, 43_238, 674_624]),
    ("r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", [6, 264, 9_467, 422_333, 15_833_292]),
    ("rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", [44, 1_486, 62_379, 2_103_487, 89_941_194]),
    ("r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", [46, 2_079, 89_890, 3_894_594, 164_075_551]),
];

fn check(max_depth: u32) {
    for (fen, counts) in CASES {
        let p = Position::from_fen(fen).unwrap();
        for d in 1..=max_depth {
            assert_eq!(perft(&p, d), counts[d as usize - 1], "perft({d}) of {fen}");
        }
    }
}

#[test]
fn perft_to_depth_3() {
    check(3);
}

#[test]
fn perft_start_and_endgame_depth_4() {
    for i in [0, 2] {
        let (fen, counts) = CASES[i];
        assert_eq!(perft(&Position::from_fen(fen).unwrap(), 4), counts[3], "perft(4) of {fen}");
    }
}

#[test]
#[ignore]
fn perft_depth_4_all() {
    check(4);
}

#[test]
#[ignore]
fn perft_depth_5_all() {
    check(5);
}
