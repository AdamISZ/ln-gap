//! Stack-choreography checks of the two-head refutation's tic-tac-toe
//! disprove family through the script32 simulator (the D29 discipline:
//! script passes must match native passes; regtest remains the source of
//! truth for the crypto).
//!
//! Every leaf is run against its native mirror over legal and illegal
//! tuples. The safety direction (no leaf fires on a legal move) keeps the
//! graph safe for honest players; the completeness direction (every wrong
//! claimed transition fires some leaf) makes the parked tuple judgeable.

use lngap_channel::Role;
use lngap_contract::Contract;
use lngap_lamport::winternitz::WotsSecret;
use lngap_lamport::bits_to_uint;
use lngap_pos::refute::{self, pair_key, refute_key};
use lngap_pos::ttt::{self, Layout};
use lngap_tictactoe::{Board, TicTacToe};

fn head(game: u16, depth: u8, mover: u8, mv: u8, state: u32) -> [u8; 48] {
    let mut h = [0u8; 48];
    h[0..4].copy_from_slice(&((u32::from(game) << 16) | (u32::from(depth) << 8) | u32::from(mover)).to_be_bytes());
    h[4..8].copy_from_slice(&((u32::from(mv) << 24) | state).to_be_bytes());
    h
}

fn state_u32(b: &Board) -> u32 {
    bits_to_uint(&TicTacToe.state_bits(b))
}

/// Play `mv` from `b` (natively), if legal.
fn play(b: &Board, mv: u8) -> Option<Board> {
    let mover = TicTacToe.turn(b)?;
    TicTacToe.transition(b, &mv, mover).ok()
}

/// The board after the moves `cells` from the empty board.
fn after(cells: &[u8]) -> Board {
    let mut b = Board::empty();
    for &m in cells {
        b = play(&b, m).expect("a legal scripted line");
    }
    b
}

struct Family {
    layout: Layout,
    leaves: Vec<ttt::PosLeaf>,
}

/// The disprove family for depth 2 (the two-head pair key, mover = hub).
fn pair_family() -> (Family, WotsSecret) {
    let sk = pair_key([9u8; 32]);
    (family_at(&sk, 2, Role::Hub), sk)
}

/// The disprove family for one depth/mover (the word0 constants are
/// per-depth).
fn family_at(sk: &WotsSecret, depth: u32, mover: Role) -> Family {
    let layout = Layout::at(depth, 1, mover);
    let leaves = ttt::disprove_leaves(&layout, &sk.public());
    Family { layout, leaves }
}

/// The family for depth 1 (single head, constant prior, mover = user).
fn single_family() -> (Family, WotsSecret) {
    let sk = refute_key([9u8; 32]);
    let layout = Layout::at(1, 1, Role::User);
    let leaves = ttt::disprove_leaves(&layout, &sk.public());
    (Family { layout, leaves }, sk)
}

impl Family {
    /// Run every leaf on the tuple; return the names that fired. Asserts
    /// script outcome == native mirror for every leaf.
    fn fired(&self, sk: &WotsSecret, prior: &[u8; 48], new: &[u8; 48]) -> Vec<String> {
        let sig = if self.layout.prior.is_some() {
            let mut msg = prior.to_vec();
            msg.extend_from_slice(new);
            sk.sign(&msg).unwrap()
        } else {
            sk.sign(new).unwrap()
        };
        let w = refute::disprove_witness(&sig);
        let mut out = Vec::new();
        for leaf in &self.leaves {
            let ran = lngap_script32::sim::run(leaf.script.as_script(), w.clone()).is_ok();
            let native = (leaf.fires)(prior, new);
            assert_eq!(ran, native, "leaf {} disagrees with its native mirror", leaf.name);
            if ran {
                out.push(leaf.name.clone());
            }
        }
        out
    }
}

#[test]
fn legal_moves_are_not_disprovable() {
    // the safety sweep: from several mid-game priors, every legal move with
    // the honest new state fires NO leaf
    let sk = pair_key([9u8; 32]);
    for line in [&[4u8][..], &[4, 0][..], &[4, 0, 8][..]] {
        let prior = after(line);
        if TicTacToe.turn(&prior) != Some(Role::Hub) {
            continue; // the pair family here judges a hub move
        }
        let d = line.len() as u8 + 1;
        let fam = family_at(&sk, d as u32, Role::Hub);
        let p_head = head(1, d - 1, 0, *line.last().unwrap(), state_u32(&prior));
        for mv in 0..9u8 {
            let Some(new) = play(&prior, mv) else { continue };
            let n_head = head(1, d, 1, mv, state_u32(&new));
            assert!(fam.fired(&sk, &p_head, &n_head).is_empty(), "a legal move at {mv} must not be disprovable");
        }
    }
    // depth 1: every legal opening
    let (fam1, sk1) = single_family();
    for mv in 0..9u8 {
        let new = play(&Board::empty(), mv).unwrap();
        let n_head = head(1, 1, 0, mv, state_u32(&new));
        assert!(fam1.fired(&sk1, &[0; 48], &n_head).is_empty(), "a legal opening at {mv} must not be disprovable");
    }
}

#[test]
fn each_illegal_kind_fires_its_leaf() {
    let (fam, sk) = pair_family();
    let prior = after(&[4]); // X@4; hub on turn
    let p_head = head(1, 1, 0, 4, state_u32(&prior));
    let fire = |mv: u8, new: &Board| {
        let n_head = head(1, 2, 1, mv, state_u32(new));
        fam.fired(&sk, &p_head, &n_head)
    };
    // hub plays the occupied cell 4, claiming the overwrite honestly
    let mut claimed = prior.clone();
    claimed.cells[4] = 2; // O over X
    claimed.turn = Role::User;
    let f = fire(4, &claimed);
    assert!(f.contains(&"cell_occupied_4".to_string()), "{f:?}");

    // out of range, the claim otherwise honest (board unchanged, turn flipped)
    let mut honestish = prior.clone();
    honestish.turn = Role::User;
    let f = fire(11, &honestish);
    assert_eq!(f, vec!["cell_out_of_range".to_string()], "{f:?}");

    // not on turn: the prior claims it was user's turn all along
    let mut wrong_turn_prior = prior.clone();
    wrong_turn_prior.turn = Role::User;
    let n = play(&prior, 0).unwrap();
    let f = fam.fired(&sk, &head(1, 1, 0, 4, state_u32(&wrong_turn_prior)), &head(1, 2, 1, 0, state_u32(&n)));
    assert!(f.contains(&"not_on_turn".to_string()), "{f:?}");

    // board mismatch: hub plays 0 but claims cell 1 as well
    let mut bad = play(&prior, 0).unwrap();
    bad.cells[1] = 2;
    let f = fire(0, &bad);
    assert!(f.contains(&"board_mismatch_1".to_string()), "{f:?}");

    // turn not flipped
    let mut bad = play(&prior, 0).unwrap();
    bad.turn = Role::Hub;
    let f = fire(0, &bad);
    assert_eq!(f, vec!["turn_not_flipped".to_string()], "{f:?}");

    // status lie: hub claims a win on an open board
    let mut bad = play(&prior, 0).unwrap();
    bad.status = 2; // O_WON
    let f = fire(0, &bad);
    assert_eq!(f, vec!["status_mismatch".to_string()], "{f:?}");

    // prior closed: the game was already over (X@0,1,2 — the top row)
    let term = after(&[0, 3, 1, 4, 2]);
    assert_eq!(TicTacToe.turn(&term), None, "the scripted line must be terminal");
    let p_term = head(1, 5, 0, 2, state_u32(&term));
    let n_head = head(1, 6, 1, 5, state_u32(&term));
    let f = fam.fired(&sk, &p_term, &n_head);
    assert!(f.contains(&"prior_closed".to_string()), "{f:?}");
}

#[test]
fn any_wrong_new_state_fires_some_leaf() {
    // the completeness sweep: a legal move with a WRONG claimed new state
    // always fires at least one leaf
    let (fam, sk) = pair_family();
    let prior = after(&[4]); // hub on turn
    let p_head = head(1, 1, 0, 4, state_u32(&prior));
    for mv in [0u8, 1, 8] {
        let honest = play(&prior, mv).unwrap();
        let mut variants: Vec<Board> = Vec::new();
        for cell in [0usize, 4, 8] {
            for v in 0..=2u8 {
                let mut m = honest.clone();
                m.cells[cell] = v;
                variants.push(m);
            }
        }
        for st in 0..=3u8 {
            let mut m = honest.clone();
            m.status = st;
            variants.push(m);
        }
        let mut m = honest.clone();
        m.turn = m.turn.other();
        variants.push(m);
        for bad in variants {
            if bad == honest {
                continue;
            }
            let n_head = head(1, 2, 1, mv, state_u32(&bad));
            assert!(!fam.fired(&sk, &p_head, &n_head).is_empty(), "the wrong claim {bad:?} after mv {mv} must fire some leaf");
        }
    }
}

#[test]
fn wrong_slot_fields_fire() {
    let (fam, sk) = pair_family();
    let prior = after(&[4]);
    let p_head = head(1, 1, 0, 4, state_u32(&prior));
    let new = play(&prior, 0).unwrap();
    let good = head(1, 2, 1, 0, state_u32(&new));
    assert!(fam.fired(&sk, &p_head, &good).is_empty());
    for (game, depth, mover) in [(2u16, 2u8, 1u8), (1, 3, 1), (1, 2, 0)] {
        let bad = head(game, depth, mover, 0, state_u32(&new));
        let f = fam.fired(&sk, &p_head, &bad);
        assert_eq!(f, vec!["wrong_slot".to_string()], "{f:?}");
    }
    // an empty slot's zero head (the mover never published)
    let f = fam.fired(&sk, &p_head, &[0; 48]);
    assert!(f.contains(&"wrong_slot".to_string()), "{f:?}");
    // and a wrong prior head
    let f = fam.fired(&sk, &[0; 48], &good);
    assert!(f.contains(&"wrong_slot".to_string()), "{f:?}");
}

#[test]
fn depth_one_family() {
    let (fam, sk) = single_family();
    // user plays 4 but claims the board unchanged
    let n_head = head(1, 1, 0, 4, 0);
    let f = fam.fired(&sk, &[0; 48], &n_head);
    assert!(f.contains(&"board_mismatch_4".to_string()), "{f:?}");
    // out of range at depth 1 (the claim lies about the board too: mv = 12
    // writes nowhere, so the claimed cell also mismatches)
    let honest = play(&Board::empty(), 0).unwrap();
    let n_head = head(1, 1, 0, 12, state_u32(&honest));
    let f = fam.fired(&sk, &[0; 48], &n_head);
    assert!(f.contains(&"cell_out_of_range".to_string()), "{f:?}");
    // turn not flipped at depth 1
    let mut bad = honest.clone();
    bad.turn = Role::User;
    let n_head = head(1, 1, 0, 0, state_u32(&bad));
    let f = fam.fired(&sk, &[0; 48], &n_head);
    assert_eq!(f, vec!["turn_not_flipped".to_string()], "{f:?}");
    // a one-move "win"
    let mut bad = honest;
    bad.status = 1;
    let n_head = head(1, 1, 0, 0, state_u32(&bad));
    let f = fam.fired(&sk, &[0; 48], &n_head);
    assert_eq!(f, vec!["status_mismatch".to_string()], "{f:?}");
}

#[test]
fn resolution_fragment_checks_the_code() {
    // the checked split's core (minus the CSV / 2-of-2 / code-gate prefix,
    // which the simulator does not stub): R(parked new) must equal the code
    let sk = pair_key([9u8; 32]);
    let l = Layout::at(2, 1, Role::Hub);
    let prior = after(&[4]);
    let p_head = head(1, 1, 0, 4, state_u32(&prior));
    let cases = [
        play(&prior, 0).unwrap(),          // open: R = HubWins (claimant's forfeit)
        after(&[0, 3, 1, 4, 2]),           // X won
        after(&[0, 1, 3, 4, 2, 5, 7, 6, 8]), // the drawn board XOX/XOO/OXX
    ];
    assert_eq!(state_u32(&cases[2]) >> 19, 3, "the third case must be a draw");
    for b in cases {
        let s = state_u32(&b);
        let code = ttt::resolution(s) as u8;
        let n_head = head(1, 2, 1, 0, s);
        let mut msg = p_head.to_vec();
        msg.extend_from_slice(&n_head);
        let sig = sk.sign(&msg).unwrap();
        for &c in &[0u8, 1, 2] {
            let script = {
                let mut bd = lngap_lamport::winternitz::WotsExt::wots_verify(bitcoin::script::Builder::new(), &sk.public());
                bd = ttt::resolution_fragment(bd, l.file, l.new, c);
                for _ in 0..l.file / 2 {
                    bd = bd.push_opcode(bitcoin::opcodes::all::OP_2DROP);
                }
                bd.push_int(1).into_script()
            };
            let res = lngap_script32::sim::run(script.as_script(), refute::disprove_witness(&sig));
            assert_eq!(res.is_ok(), c == code, "R = {code}, code {c}, state {s:#x}");
        }
    }
}

// ----- the terminal exhibit's status gate (D37) -----

/// Dummy 64-byte sigs for the readout's possession proofs: the simulator's
/// CHECKSIG stub pops both elements and continues (sim_refute.rs's
/// discipline); the WOTS re-commitment work runs for real.
const DUMMY_SIG: [u8; 64] = [0x30; 64];

#[test]
fn terminal_gate_admits_only_terminal_states() {
    // the gate fragment over the pair file (the readout follows it in the
    // real leaf; here the file is dropped instead): runs iff
    // status(new) != OPEN
    let sk = pair_key([9u8; 32]);
    let l = Layout::at(5, 1, Role::User);
    let prior = after(&[0, 3, 1, 4]); // X@0, O@3, X@1, O@4 — user on turn
    let p_head = head(1, 4, 1, 4, state_u32(&prior));
    let cases: Vec<(Board, bool)> = vec![
        (play(&prior, 2).unwrap(), true),            // X@2 completes the top row
        (after(&[0, 1, 3, 4, 2, 5, 7, 6, 8]), true), // the drawn board
        (play(&prior, 8).unwrap(), false),           // still open
        (after(&[4]), false),                        // one move in
    ];
    for (b, terminal) in cases {
        let n_head = head(1, 5, 0, 2, state_u32(&b)); // the mv field is not the gate's business
        let mut msg = p_head.to_vec();
        msg.extend_from_slice(&n_head);
        let sig = sk.sign(&msg).unwrap();
        let mut bd = lngap_lamport::winternitz::WotsExt::wots_verify(bitcoin::script::Builder::new(), &sk.public());
        bd = ttt::terminal_gate_fragment(bd, l.file, l.new);
        for _ in 0..l.file / 2 {
            bd = bd.push_opcode(bitcoin::opcodes::all::OP_2DROP);
        }
        let res = lngap_script32::sim::run(bd.push_int(1).into_script().as_script(), refute::disprove_witness(&sig));
        assert_eq!(res.is_ok(), terminal, "the gate must admit exactly the terminal states: {b:?}");
    }
}

#[test]
fn exhibit_leaf_runs_only_when_terminal() {
    // the FULL exhibit leaf: the D41 authorship fragments (per parked head,
    // the mover's state-key preimages checked against the claimed state)
    // plus the gated two-head readout over the two slots' epoch tables (the
    // tables' points are embedded; the possession sigs are dummies under
    // the sim's CHECKSIG stub)
    let att = lngap_ec_wots::Attester::new([7u8; 32]);
    let t4 = att.epoch_table(4, lngap_pos::HEADER_CHUNKS);
    let t5 = att.epoch_table(5, lngap_pos::HEADER_CHUNKS);
    let key = pair_key([9u8; 32]);
    let l = Layout::at(5, 1, Role::User);
    let prior = after(&[0, 3, 1, 4]);
    let p_head = head(1, 4, 1, 4, state_u32(&prior));
    // the per-head state keys (fixture): the prior head is the hub's move
    // at depth 4, the new the user's at depth 5 (D43: WOTS over the 3
    // state bytes)
    let sk_prev = lngap_lamport::winternitz::WotsSecret::from_entropy(lngap_lamport::winternitz::WotsParams::for_bytes(3), [0x52; 32]);
    let sk_new = lngap_lamport::winternitz::WotsSecret::from_entropy(lngap_lamport::winternitz::WotsParams::for_bytes(3), [0x51; 32]);
    let sig_prev = sk_prev.sign(&ttt::auth_message(&p_head)).unwrap();
    let sigs: Vec<Vec<u8>> = (0..refute::HEAD_CHUNKS).map(|_| DUMMY_SIG.to_vec()).collect();
    for (b, terminal) in [(play(&prior, 2).unwrap(), true), (play(&prior, 8).unwrap(), false)] {
        let n_head = head(1, 5, 0, 2, state_u32(&b));
        let mut msg = p_head.to_vec();
        msg.extend_from_slice(&n_head);
        let sig = key.sign(&msg).unwrap();
        let sig_new = sk_new.sign(&ttt::auth_message(&n_head)).unwrap();
        let leaf = refute::refute_leaf_pair_gated(&t4, &t5, &key.public(), |bd| {
            let bd = ttt::authorship_fragment(bd, l.file, l.new, &sk_new.public());
            let bd = ttt::authorship_fragment(bd, l.file, 0, &sk_prev.public());
            ttt::terminal_gate_fragment(bd, l.file, l.new)
        });
        let res = lngap_script32::sim::run(leaf.as_script(), refute::refute_witness_pair(&sigs, &sigs, &sig, &[&sig_new, &sig_prev]));
        assert_eq!(res.is_ok(), terminal, "the exhibit leaf must admit exactly the terminal state");
    }
}

/// Sizes for the record (no chain needed).
#[test]
fn print_family_sizes() {
    let (fam, _sk) = pair_family();
    let total: usize = fam.leaves.iter().map(|l| l.script.len()).sum();
    println!("POS-TTT depth >= 2 disprove family: {} leaves, {total} B of script", fam.leaves.len());
    for l in &fam.leaves {
        println!("  {:<18} {} B", l.name, l.script.len());
    }
    let (fam1, _sk1) = single_family();
    let total1: usize = fam1.leaves.iter().map(|l| l.script.len()).sum();
    println!("POS-TTT depth 1 disprove family: {} leaves, {total1} B of script", fam1.leaves.len());
}
