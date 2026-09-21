//! Stack-choreography checks of the chess disprove family over the parked
//! pair (the D29 discipline: script passes must match native passes;
//! regtest remains the source of truth for the crypto) — sim_ttt.rs's
//! chess sibling.
//!
//! Every leaf runs against its native mirror (the certificate search over
//! the decoded tuple) over legal and illegal lines: the safety direction
//! (no leaf fires on a legal move) keeps the graph safe for honest
//! players; the completeness direction (every wrong claimed transition
//! fires some leaf) makes the parked tuple judgeable. Depth 1 exercises
//! the constant-prior pad.

use lngap_channel::Role;
use lngap_chess::certificate::{find_kind, mechanical_successor};
use lngap_chess::leaf::exhibit_values;
use lngap_chess::{apply, Move};
use lngap_chess_fc::ChessState;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::chess;
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{self, pair_key, refute_key};
use lngap_pos::ttt::{Layout, PosLeaf};

const GAME: u16 = 1;

/// The state after the UCI line from the start (all moves legal).
fn game(ucis: &[&str]) -> ChessState {
    let mut s = ChessState::initial();
    for u in ucis {
        s = play(&s, u).expect("a legal scripted line");
    }
    s
}

/// Play `uci` from `s` (natively), if legal.
fn play(s: &ChessState, uci: &str) -> Option<ChessState> {
    let mv = Move::parse(uci)?;
    let mut pos = apply(&s.pos, mv).ok()?;
    pos.fullmove = 0;
    Some(ChessState { pos, mv, depth: s.depth + 1 })
}

/// The move played, ignoring legality (an illegal-but-well-formed
/// successor for the completeness corpus).
fn pretend(s: &ChessState, uci: &str) -> ChessState {
    let mv = Move::parse(uci).unwrap();
    let mut pos = mechanical_successor(&s.pos, mv);
    pos.fullmove = 0;
    ChessState { pos, mv, depth: s.depth + 1 }
}

struct Family {
    depth: u32,
    leaves: Vec<PosLeaf>,
}

/// The disprove family for `depth` (the mover by parity).
fn family_at(sk: &WotsSecret, depth: u32) -> Family {
    let l = Layout::at(depth, GAME, mover_at(depth));
    Family { depth, leaves: chess::disprove_leaves(&l, &sk.public()) }
}

impl Family {
    /// Run every leaf on the tuple; return the names that fired. Asserts
    /// script outcome == native mirror for every leaf. The witness is the
    /// re-commitment reveal over the kind's exhibit (deepest), real where
    /// the kind finds a challenge, zeros otherwise.
    fn fired(&self, sk: &WotsSecret, prior: &[u8; 48], new: &[u8; 48]) -> Vec<String> {
        let sig = if self.depth >= 2 {
            let mut msg = prior.to_vec();
            msg.extend_from_slice(new);
            sk.sign(&msg).unwrap()
        } else {
            sk.sign(new).unwrap()
        };
        let pr = if self.depth == 1 { ChessState::initial() } else { chess_state(prior).unwrap() };
        let af = chess_state(new).unwrap();
        let mut out = Vec::new();
        for (i, leaf) in self.leaves.iter().enumerate() {
            let exhibit = if i == 0 {
                vec![] // wrong_slot takes none
            } else {
                let kind = chess::kinds()[i - 1];
                find_kind(&pr.pos, af.mv, &af.pos, kind).map_or_else(|| vec![0; kind.exhibit_len()], |c| exhibit_values(c))
            };
            // Witness, bottom-first: the kind's exhibit elements IN ORDER
            // (the emitter's slots model takes Kind::exhibit()[0] deepest),
            // then the re-commitment reveal. NOTE the order is load-bearing
            // for the two 2-element exhibits (CastlingAttacked,
            // KingAttacked): the contract crate's witness_args_with appends
            // the exhibit AFTER the end signature (so its .rev() stack
            // bottoms at the LAST exhibit element — swapped). Upstream
            // never fired a 2-element exhibit (the C-suite's one disprove
            // was a Ray, one element); this suite's KingAttacked case does.
            let mut w: Vec<Vec<u8>> = exhibit.iter().map(|&v| lngap_script32::sim::encode(v)).collect();
            w.extend(refute::disprove_witness(&sig));
            let ran = if i == 0 {
                // wrong_slot is a ttt-shaped leaf: OP_VERIFY the predicate,
                // so a non-firing tuple ERRORS
                lngap_script32::sim::run(leaf.script.as_script(), w).is_ok()
            } else {
                // a chess kind body leaves its verdict as the single
                // remaining stack element (leaf_over_registers's finish):
                // "fired" is a truthy verdict; an in-body failure (a
                // range-check VERIFY) would be a bug — panic, as chess-fc's
                // sweep does
                let out = lngap_script32::sim::run(leaf.script.as_script(), w)
                    .unwrap_or_else(|e| panic!("{} errors: {e}", leaf.name));
                out.len() == 1 && !out[0].is_empty()
            };
            let native = (leaf.fires)(prior, new);
            assert_eq!(ran, native, "leaf {} disagrees with its native mirror", leaf.name);
            if ran {
                out.push(leaf.name.clone());
            }
        }
        out
    }
}

/// Decode a head's state region.
fn chess_state(h: &[u8; 48]) -> std::result::Result<ChessState, String> {
    ChessState::from_e(h[8..48].try_into().unwrap()).map_err(|e| e.to_string())
}

/// The pair of heads for a move: `prior`'s state at `depth - 1`, `new`'s
/// at `depth`, with the parity movers.
fn heads(prior: &ChessState, new: &ChessState) -> ([u8; 48], [u8; 48]) {
    let d = new.depth as u32;
    (chess::head(GAME, d as u8 - 1, mover_at(d - 1), prior), chess::head(GAME, d as u8, mover_at(d), new))
}

#[test]
fn legal_moves_are_not_disprovable() {
    let sk = pair_key([9u8; 32]);
    // depth 1: every legal opening is safe (the constant-prior pad)
    let (sk1, fam1) = (refute_key([9u8; 32]), family_at(&refute_key([9u8; 32]), 1));
    for uci in ["e2e4", "g1f3", "b1c3", "a2a4", "h2h3"] {
        let new = play(&ChessState::initial(), uci).unwrap();
        let f = fam1.fired(&sk1, &[0; 48], &chess::head(GAME, 1, Role::User, &new));
        assert!(f.is_empty(), "a legal opening at {uci} must not be disprovable: {f:?}");
    }
    // mid-game: a sweep of lines, every legal reply safe
    for line in [&["e2e4"][..], &["e2e4", "e7e5"][..], &["e2e4", "e7e5", "g1f3"][..]] {
        let prior = game(line);
        let d = line.len() as u32 + 1;
        let fam = family_at(&sk, d);
        for uci in ["e7e5", "c7c5", "b8c6", "g8f6", "d2d4", "c2c3", "f1c4", "d8h4"] {
            let Some(new) = play(&prior, uci) else { continue };
            let (p, n) = heads(&prior, &new);
            let f = fam.fired(&sk, &p, &n);
            assert!(f.is_empty(), "a legal move {uci} at depth {d} must not be disprovable: {f:?}");
        }
    }
    // a legal king-side castle, and the fool's-mate mate move
    let prior = game(&["e2e4", "e7e5", "g1f3", "b8c6", "f1c4", "g8f6"]);
    let new = play(&prior, "e1g1").unwrap();
    let (p, n) = heads(&prior, &new);
    assert!(family_at(&sk, 7).fired(&sk, &p, &n).is_empty(), "a legal castle must not be disprovable");
    let prior = game(&["f2f3", "e7e5", "g2g4"]);
    let new = play(&prior, "d8h4").unwrap(); // mate
    let (p, n) = heads(&prior, &new);
    assert!(family_at(&sk, 4).fired(&sk, &p, &n).is_empty(), "a legal mate must not be disprovable");
}

#[test]
fn each_illegal_line_fires_some_leaf() {
    let sk = pair_key([9u8; 32]);
    let (sk1, fam1) = (refute_key([9u8; 32]), family_at(&refute_key([9u8; 32]), 1));
    let s0 = ChessState::initial();
    let d1 = |new: &ChessState| fam1.fired(&sk1, &[0; 48], &chess::head(GAME, 1, Role::User, new));
    // the pawn's triple push
    assert!(!d1(&pretend(&s0, "e2e5")).is_empty());
    // the king onto its own pawn
    assert!(!d1(&pretend(&s0, "e1e2")).is_empty());
    // a bishop through its own pawn
    assert!(!d1(&pretend(&s0, "c1e3")).is_empty());
    // a rook through its own pawn
    assert!(!d1(&pretend(&s0, "a1a3")).is_empty());
    // a legal move with a corrupted successor square
    let mut bad = play(&s0, "e2e4").unwrap();
    bad.pos.set(lngap_chess::Square::parse("h8").unwrap(), None);
    assert!(!d1(&bad).is_empty());
    // .. with the side not flipped
    let mut bad = play(&s0, "e2e4").unwrap();
    bad.pos.side = lngap_chess::Colour::White;
    assert!(!d1(&bad).is_empty());
    // .. with the en-passant square dropped
    let mut bad = play(&s0, "e2e4").unwrap();
    bad.pos.ep = None;
    assert!(!d1(&bad).is_empty());
    // .. with the halfmove clock bumped
    let mut bad = play(&s0, "e2e4").unwrap();
    bad.pos.halfmove = 1;
    assert!(!d1(&bad).is_empty());
    // .. with the castling rights dropped
    let mut bad = play(&s0, "e2e4").unwrap();
    bad.pos.castling = 0;
    assert!(!d1(&bad).is_empty());
    // moving the opponent's piece (after 1.e4, black "plays" the e4 pawn)
    let prior = game(&["e2e4"]);
    let bad = pretend(&prior, "e4e5");
    let (p, n) = heads(&prior, &bad);
    assert!(!family_at(&sk, 2).fired(&sk, &p, &n).is_empty());
    // castling through pieces
    let prior = game(&["e2e4", "e7e5"]);
    let bad = pretend(&prior, "e1g1");
    let (p, n) = heads(&prior, &bad);
    assert!(!family_at(&sk, 3).fired(&sk, &p, &n).is_empty());
    // ignoring the mate-in-one's check: from the mated position any
    // claimed successor leaves the king attacked
    let mated = game(&["f2f3", "e7e5", "g2g4", "d8h4"]);
    assert!(lngap_chess::terminal(&mated.pos).is_some(), "the fixture must be terminal");
    let bad = pretend(&mated, "g4g5");
    let (p, n) = heads(&mated, &bad);
    let f = family_at(&sk, 5).fired(&sk, &p, &n);
    assert!(f.contains(&"chess_kingattacked".to_string()), "{f:?}");
}

#[test]
fn wrong_slot_fires_on_bad_word0() {
    let sk = pair_key([9u8; 32]);
    let prior = game(&["e2e4"]);
    let new = play(&prior, "e7e5").unwrap();
    let (p, n) = heads(&prior, &new);
    // honest: nothing fires
    assert!(family_at(&sk, 2).fired(&sk, &p, &n).is_empty());
    let fam = family_at(&sk, 2);
    // wrong game id on the new head
    let mut bad = n;
    bad[0..4].copy_from_slice(&ttt_word0(9, 2, 1).to_be_bytes());
    assert_eq!(fam.fired(&sk, &p, &bad), vec!["wrong_slot".to_string()]);
    // wrong depth on the prior head
    let mut badp = p;
    badp[0..4].copy_from_slice(&ttt_word0(GAME as u32 as u16, 9, 0).to_be_bytes());
    assert_eq!(fam.fired(&sk, &badp, &n), vec!["wrong_slot".to_string()]);
    // wrong mover on the new head
    let mut badm = n;
    badm[0..4].copy_from_slice(&ttt_word0(GAME, 2, 0).to_be_bytes());
    assert_eq!(fam.fired(&sk, &p, &badm), vec!["wrong_slot".to_string()]);
    // an empty slot's zero head: wrong_slot, among others (the zero head
    // decodes to a degenerate position the transition kinds also judge)
    let f = fam.fired(&sk, &p, &[0; 48]);
    assert!(f.contains(&"wrong_slot".to_string()), "{f:?}");
}

fn ttt_word0(game: u16, depth: u8, mover: u8) -> u32 {
    (u32::from(game) << 16) | (u32::from(depth) << 8) | u32::from(mover)
}

#[test]
fn resolution_fragment_checks_the_code() {
    // the checked split's core (minus the CSV / 2-of-2 / code-gate prefix,
    // which the simulator does not stub): R(parked new) = side-to-move
    // forfeits, and the Draw code can never pass
    let sk = pair_key([9u8; 32]);
    let l = Layout::at(2, GAME, mover_at(2));
    let prior = game(&["e2e4"]);
    let p_head = chess::head(GAME, 1, Role::User, &prior);
    let cases = [
        (play(&prior, "e7e5").unwrap(), 1u8), // black just moved: white (user) to move forfeits -> HubWins
        (game(&["f2f3", "e7e5", "g2g4", "d8h4"]), 1u8), // white mated: the side to move loses -> HubWins
    ];
    for (s, want) in cases {
        let n_head = chess::head(GAME, 2, mover_at(2), &s);
        let mut msg = p_head.to_vec();
        msg.extend_from_slice(&n_head);
        let sig = sk.sign(&msg).unwrap();
        for c in [0u8, 1, 2] {
            let mut bd = lngap_lamport::winternitz::WotsExt::wots_verify(bitcoin::script::Builder::new(), &sk.public());
            bd = chess::resolution_fragment(bd, l.file, l.new, c);
            for _ in 0..l.file / 2 {
                bd = bd.push_opcode(bitcoin::opcodes::all::OP_2DROP);
            }
            let res = lngap_script32::sim::run(bd.push_int(1).into_script().as_script(), refute::disprove_witness(&sig));
            assert_eq!(res.is_ok(), c == want, "R = {want}, code {c}");
        }
    }
}

/// Dummy 64-byte sigs for the readout's possession proofs: the simulator's
/// CHECKSIG stub pops both elements and continues (sim_refute.rs's
/// discipline); the WOTS re-commitment and the authorship checks run for
/// real.
const DUMMY_SIG: [u8; 64] = [0x30; 64];

#[test]
fn refute_leaf_runs_only_with_true_authorship() {
    // the FULL pair refute leaf: the D41 authorship fragments (per parked
    // head, the mover's 336-bit state-key preimages checked against the
    // claimed state||move) plus the two-head readout over the two slots'
    // epoch tables (the tables' points embedded; the possession sigs
    // dummies under the sim's CHECKSIG stub)
    let att = lngap_ec_wots::Attester::new([7u8; 32]);
    let t1 = att.epoch_table(1, lngap_pos::HEADER_CHUNKS);
    let t2 = att.epoch_table(2, lngap_pos::HEADER_CHUNKS);
    let key = pair_key([9u8; 32]);
    let l = Layout::at(2, GAME, mover_at(2));
    let prior = game(&["e2e4"]);
    let new = play(&prior, "e7e5").unwrap();
    let p_head = chess::head(GAME, 1, Role::User, &prior);
    let n_head = chess::head(GAME, 2, Role::Hub, &new);
    let sk_new = lngap_lamport::winternitz::WotsSecret::from_entropy(lngap_lamport::winternitz::WotsParams::for_bytes(42), [0x51; 32]);
    let sigs: Vec<Vec<u8>> = (0..refute::HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    let leaf = refute::refute_leaf_pair_gated(&t1, &t2, &key.public(), |bd| {
        chess::authorship_fragment(bd, l.file, l.new, &sk_new.public())
    });
    let mut msg = p_head.to_vec();
    msg.extend_from_slice(&n_head);
    let sig = key.sign(&msg).unwrap();
    let sig_new = sk_new.sign(&chess::auth_message(&n_head)).unwrap();
    let good = refute::refute_witness_pair(&sigs, &sigs, &sig, &[&sig_new]);
    assert!(lngap_script32::sim::run(leaf.as_script(), good).is_ok(), "true authorship must pass");
    // a garbage-signed entry: a signature over a DIFFERENT successor's
    // region must fail the fragment (the tie forces the file's digits)
    let wrong = play(&prior, "c7c5").unwrap();
    let bad_sig = sk_new.sign(&chess::auth_message(&chess::head(GAME, 2, Role::Hub, &wrong))).unwrap();
    let bad = refute::refute_witness_pair(&sigs, &sigs, &sig, &[&bad_sig]);
    assert!(lngap_script32::sim::run(leaf.as_script(), bad).is_err(), "garbage authorship must be rejected");
}

/// Sizes for the record (no chain needed).
#[test]
fn print_family_sizes() {
    let sk = pair_key([9u8; 32]);
    let fam = family_at(&sk, 2);
    let total: usize = fam.leaves.iter().map(|l| l.script.len()).sum();
    println!("POS-CHESS depth >= 2 disprove family: {} leaves, {total} B of script", fam.leaves.len());
    for l in &fam.leaves {
        println!("  {:<24} {} B", l.name, l.script.len());
    }
    let sk1 = refute_key([9u8; 32]);
    let fam1 = family_at(&sk1, 1);
    let total1: usize = fam1.leaves.iter().map(|l| l.script.len()).sum();
    println!("POS-CHESS depth 1 disprove family: {} leaves, {total1} B of script", fam1.leaves.len());
}
