//! Every tic-tac-toe disprove leaf against the interpreter, at depth 1 and
//! depth 2, for honest moves and for each way of cheating the scenarios use
//! (occupied cell, extra mark, wrong code) plus more.

use std::sync::Arc;

use bitcoin::Amount;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_contract::testing::{check_disprove_leaves, depth_secrets};
use lngap_contract::{Claim, ContractInstance, Program};
use lngap_tictactoe::{Board, TicTacToe, X_WON, O_WON, DRAW};

fn bits(b: &Board) -> Vec<bool> {
    lngap_contract::Contract::state_bits(&TicTacToe, b)
}
fn mv(c: u8) -> Vec<bool> {
    lngap_contract::Contract::move_bits(&TicTacToe, &c)
}
fn board(cells: [u8; 9], turn: Role, status: u8) -> Board {
    Board { cells, turn, status }
}

#[test]
fn tictactoe_disprove_leaves_match_native_checks() {
    let rt = Regtest::start().unwrap();
    let prog: Arc<dyn Program> = Arc::new(TicTacToe);
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
    let pubs = [user.public(), hub.public()];
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::Hub, seq: 5, rev_hash: [3u8; 20] };

    // the scenario's state 6: after U:4 H:1 U:0 H:8, user on turn
    let s6 = board([1, 2, 0, 0, 1, 0, 0, 0, 2], Role::User, 0);
    let (s1, k1) = depth_secrets(Role::User, 30, &*prog);
    let (s2, k2) = depth_secrets(Role::Hub, 40, &*prog);
    let (s3, k3) = depth_secrets(Role::User, 50, &*prog);
    let mut keys = vec![k1, k2, k3];
    // remaining depth keys (5 empty cells → M = 5)
    let (_, k4) = depth_secrets(Role::Hub, 60, &*prog);
    let (_, k5) = depth_secrets(Role::User, 70, &*prog);
    keys.push(k4);
    keys.push(k5);
    let inst = ContractInstance::new(1, prog.clone(), Amount::from_sat(20_000), bits(&s6), 300, 5, keys, vec![]).unwrap();

    // depth 1: user plays 6 (honest), and various frauds
    let after6 = board([1, 2, 0, 0, 1, 0, 1, 0, 2], Role::Hub, 0);
    let d1: Vec<(&str, Claim)> = vec![
        ("honest U:6", Claim { prior: bits(&s6), mv: mv(6), new: bits(&after6), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("honest U:2 no win yet", Claim { prior: bits(&s6), mv: mv(2), new: bits(&board([1, 2, 1, 0, 1, 0, 0, 0, 2], Role::Hub, 0)), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("U plays occupied 4", Claim { prior: bits(&s6), mv: mv(4), new: bits(&board([1, 2, 0, 0, 1, 0, 0, 0, 2], Role::Hub, 0)), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("U plays 9", Claim { prior: bits(&s6), mv: mv(9), new: bits(&after6), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("U claims win", Claim { prior: bits(&s6), mv: mv(6), new: bits(&board([1, 2, 0, 0, 1, 0, 1, 0, 2], Role::Hub, X_WON)), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("U forgets to flip turn", Claim { prior: bits(&s6), mv: mv(6), new: bits(&board([1, 2, 0, 0, 1, 0, 1, 0, 2], Role::User, 0)), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("U places O", Claim { prior: bits(&s6), mv: mv(6), new: bits(&board([1, 2, 0, 0, 1, 0, 2, 0, 2], Role::Hub, 0)), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("U erases O on 1", Claim { prior: bits(&s6), mv: mv(6), new: bits(&board([1, 0, 0, 0, 1, 0, 1, 0, 2], Role::Hub, 0)), code: TicTacToe::USER_WINS, mover: Role::User }),
        ("U wrong code", Claim { prior: bits(&s6), mv: mv(6), new: bits(&after6), code: TicTacToe::HUB_WINS, mover: Role::User }),
    ];
    let sizes1 = check_disprove_leaves(&rt, &inst, &ctx, 1, &s1, None, &hub, &d1);

    // depth 2: hub plays from after6; scenarios T4/T5/T6 frauds
    let after3 = board([1, 2, 0, 2, 1, 0, 1, 0, 2], Role::User, 0);
    let d2: Vec<(&str, Claim)> = vec![
        ("honest H:3", Claim { prior: bits(&after6), mv: mv(3), new: bits(&after3), code: TicTacToe::HUB_WINS, mover: Role::Hub }),
        ("T4 H plays occupied 6", Claim { prior: bits(&after6), mv: mv(6), new: bits(&board([1, 2, 0, 0, 1, 0, 2, 0, 2], Role::User, 0)), code: TicTacToe::HUB_WINS, mover: Role::Hub }),
        ("T5 extra O on 5", Claim { prior: bits(&after6), mv: mv(3), new: bits(&board([1, 2, 0, 2, 1, 2, 1, 0, 2], Role::User, 0)), code: TicTacToe::HUB_WINS, mover: Role::Hub }),
        ("T6 legal but code HubWins-as-terminal", Claim { prior: bits(&after6), mv: mv(3), new: bits(&board([1, 2, 0, 2, 1, 0, 1, 0, 2], Role::User, O_WON)), code: TicTacToe::HUB_WINS, mover: Role::Hub }),
        ("T6' legal, code UserWins", Claim { prior: bits(&after6), mv: mv(3), new: bits(&after3), code: TicTacToe::USER_WINS, mover: Role::Hub }),
        ("H moves on prior with user turn", Claim { prior: bits(&s6), mv: mv(3), new: bits(&board([1, 2, 0, 2, 1, 0, 0, 0, 2], Role::Hub, 0)), code: TicTacToe::USER_WINS, mover: Role::Hub }),
        ("H moves after game over", Claim { prior: bits(&board([1, 2, 1, 2, 1, 0, 1, 0, 2], Role::Hub, X_WON)), mv: mv(5), new: bits(&board([1, 2, 1, 2, 1, 2, 1, 0, 2], Role::User, X_WON)), code: TicTacToe::USER_WINS, mover: Role::Hub }),
        ("H honest draw", Claim { prior: bits(&board([1, 2, 1, 1, 2, 2, 2, 1, 0], Role::Hub, 0)), mv: mv(8), new: bits(&board([1, 2, 1, 1, 2, 2, 2, 1, 2], Role::User, DRAW)), code: TicTacToe::DRAW, mover: Role::Hub }),
        ("H claims open on full board", Claim { prior: bits(&board([1, 2, 1, 1, 2, 2, 2, 1, 0], Role::Hub, 0)), mv: mv(8), new: bits(&board([1, 2, 1, 1, 2, 2, 2, 1, 2], Role::User, 0)), code: TicTacToe::USER_WINS, mover: Role::Hub }),
        ("H honest win", Claim { prior: bits(&board([1, 1, 0, 2, 2, 0, 1, 0, 0], Role::Hub, 0)), mv: mv(5), new: bits(&board([1, 1, 0, 2, 2, 2, 1, 0, 0], Role::User, O_WON)), code: TicTacToe::HUB_WINS, mover: Role::Hub }),
        ("H hides own win", Claim { prior: bits(&board([1, 1, 0, 2, 2, 0, 1, 0, 0], Role::Hub, 0)), mv: mv(5), new: bits(&board([1, 1, 0, 2, 2, 2, 1, 0, 0], Role::User, 0)), code: TicTacToe::HUB_WINS, mover: Role::Hub }),
    ];
    let sizes2 = check_disprove_leaves(&rt, &inst, &ctx, 2, &s2, Some(&s1), &user, &d2);
    let _ = s3;
    for (n, s, w) in sizes1.iter().chain(&sizes2) {
        eprintln!("SIZE {n}: script {s} B, witness {w} B");
    }
}
