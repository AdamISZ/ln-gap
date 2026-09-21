//! The chess challenge leaves as real tapscript spends on regtest: for a
//! handful of lies, the challenger's spend through the right leaf is
//! accepted, and the same leaf with an honest move (or a wrong exhibit) is
//! rejected. Prints the vsize of each accepted spend.

use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_chess::certificate::{check, mechanical_successor, Challenge};
use lngap_chess::leaf::{leaf, witness, Kind};
use lngap_chess::{apply, Move, Position, Square};
use lngap_script32::sim::encode;

fn spend(rt: &Regtest, sink: &ScriptBuf, script: &ScriptBuf, args: &[i64]) -> Result<u64, String> {
    let tree = TapTree::new(vec![Leaf::new("c", script.clone(), Timelock::NONE)]).unwrap();
    let (op, _) = rt.fund(&tree.script_pubkey(), Amount::from_sat(100_000)).unwrap();
    let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(80_000), script_pubkey: sink.clone() }]);
    let mut w = WitnessStack::new();
    // consumption order: the last-pushed element first
    for v in args.iter().rev() {
        w.push(encode(*v));
    }
    tx.input[0].witness = w.build(script, &tree.control_block("c").unwrap());
    rt.test_accept(&tx)
}

#[test]
fn chess_leaves_on_regtest() {
    let rt = Regtest::start().unwrap();
    let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
    let pos = |f: &str| Position::from_fen(f).unwrap();
    let mv = |s: &str| Move::parse(s).unwrap();
    let sq = |s: &str| Square::parse(s).unwrap();

    let start = Position::start();
    let e4 = apply(&start, mv("e2e4")).unwrap();
    let mut e4_bad = e4.clone();
    e4_bad.set(sq("h8"), None);
    let castle_pos = pos("r4rk1/8/8/8/8/8/8/R3K2R w KQ - 0 1");
    let check_pos = pos("4k3/8/8/8/8/8/8/4K2r w - - 0 1");
    let cases: Vec<(&str, &Position, Move, Position, Challenge)> = vec![
        ("bishop jumps a pawn", &start, mv("c1e3"), mechanical_successor(&start, mv("c1e3")), Challenge::Ray { j: 1 }),
        ("pawn moves three", &start, mv("e2e5"), mechanical_successor(&start, mv("e2e5")), Challenge::Mover),
        ("h8 vanishes", &start, mv("e2e4"), e4_bad.clone(), Challenge::Board { sq: sq("h8") }),
        ("castles through check", &castle_pos, mv("e1g1"), mechanical_successor(&castle_pos, mv("e1g1")), Challenge::CastlingAttacked { crossed: true, by: sq("f8") }),
        ("king walks into a rook", &check_pos, mv("e1f1"), mechanical_successor(&check_pos, mv("e1f1")), Challenge::KingAttacked { king: sq("f1"), by: sq("h1") }),
        ("forgets to flip the side", &start, mv("e2e4"), { let mut b = e4.clone(); b.side = lngap_chess::Colour::White; b }, Challenge::Side),
    ];
    for (name, prior, m, after, c) in &cases {
        assert!(check(prior, *m, after, *c), "{name}: the Rust checker must agree it is a lie");
        let script = leaf(Kind::of(*c));
        let vs = spend(&rt, &sink, &script, &witness(prior, *m, after, *c)).unwrap_or_else(|e| panic!("{name}: honest challenge rejected: {e}"));
        println!("REGTEST {name}: {:?} leaf {} B, spend vsize {vs}", Kind::of(*c), script.len());
    }
    // the honest move through each of those leaves: rejected
    for c in [Challenge::Ray { j: 1 }, Challenge::Mover, Challenge::Board { sq: sq("h8") }, Challenge::Side, Challenge::KingAttacked { king: sq("e1"), by: sq("d8") }] {
        assert!(!check(&start, mv("e2e4"), &e4, c));
        let r = spend(&rt, &sink, &leaf(Kind::of(c)), &witness(&start, mv("e2e4"), &e4, c));
        assert!(r.is_err(), "{c:?} against an honest move must be rejected");
    }
    // an exhibit index outside the board: rejected
    let mut w = witness(&start, mv("e2e4"), &e4_bad, Challenge::Board { sq: sq("h8") });
    let l = w.len();
    w[l - 1] = 64;
    assert!(spend(&rt, &sink, &leaf(Kind::Board), &w).is_err(), "an index of 64 must be rejected");
}
