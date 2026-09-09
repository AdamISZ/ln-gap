//! Tic-tac-toe as an LN-GAP contract. The user plays X and moves first.
//!
//! State (21 bits): cells 0..8 × 2 bits (0 empty, 1 X, 2 O) at bits
//! `[2i, 2i+2)`, turn at bit 18 (0 user, 1 hub), status at bits 19..21
//! (0 open, 1 user won, 2 hub won, 3 draw). Move: 4 bits, the cell.
//! The turn bit flips on every move, terminal or not (keeps the leaf simple).

use anyhow::{ensure, Result};
use lngap_contract::prelude::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Board {
    pub cells: [u8; 9],
    pub turn: Role,
    pub status: u8,
}

pub const OPEN: u8 = 0;
pub const X_WON: u8 = 1;
pub const O_WON: u8 = 2;
pub const DRAW: u8 = 3;

pub const LINES: [[usize; 3]; 8] = [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]];

pub fn mark(r: Role) -> u8 {
    match r {
        Role::User => 1,
        Role::Hub => 2,
    }
}

impl Board {
    pub fn empty() -> Board {
        Board { cells: [0; 9], turn: Role::User, status: OPEN }
    }
    pub fn wins(&self, m: u8) -> bool {
        LINES.iter().any(|l| l.iter().all(|&i| self.cells[i] == m))
    }
    pub fn full(&self) -> bool {
        self.cells.iter().all(|&c| c != 0)
    }
    pub fn render(&self) -> String {
        let ch = |c: u8| match c {
            1 => 'X',
            2 => 'O',
            _ => '.',
        };
        (0..3).map(|r| (0..3).map(|c| ch(self.cells[3 * r + c])).collect::<String>()).collect::<Vec<_>>().join("/")
    }
}

#[derive(Debug, Default)]
pub struct TicTacToe;

impl TicTacToe {
    pub const NAME: &'static str = "tictactoe";
    pub const USER_WINS: u8 = 0;
    pub const HUB_WINS: u8 = 1;
    pub const DRAW: u8 = 2;
    const TURN_BIT: usize = 18;
    const STATUS_BITS: std::ops::Range<usize> = 19..21;
    fn cell_bits(i: usize) -> std::ops::Range<usize> {
        2 * i..2 * i + 2
    }
}

impl Contract for TicTacToe {
    type State = Board;
    type Move = u8;

    fn name(&self) -> &str {
        Self::NAME
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![
            Outcome::new(Self::USER_WINS, "UserWins", Payout::UserAll),
            Outcome::new(Self::HUB_WINS, "HubWins", Payout::HubAll),
            Outcome::new(Self::DRAW, "Draw", Payout::Even),
        ]
    }
    fn initial(&self) -> Board {
        Board::empty()
    }
    fn turn(&self, s: &Board) -> Option<Role> {
        (s.status == OPEN).then_some(s.turn)
    }
    fn transition(&self, s: &Board, m: &u8, mover: Role) -> Result<Board, Invalid> {
        if s.status != OPEN {
            return Err(Invalid("game over".into()));
        }
        if s.turn != mover {
            return Err(Invalid(format!("{mover} is not on turn")));
        }
        let cell = *m as usize;
        if cell > 8 {
            return Err(Invalid(format!("cell {cell} out of range")));
        }
        if s.cells[cell] != 0 {
            return Err(Invalid(format!("cell {cell} occupied")));
        }
        let mut n = s.clone();
        n.cells[cell] = mark(mover);
        n.turn = mover.other();
        n.status = if n.wins(mark(mover)) {
            match mover {
                Role::User => X_WON,
                Role::Hub => O_WON,
            }
        } else if n.full() {
            DRAW
        } else {
            OPEN
        };
        Ok(n)
    }
    fn resolution(&self, s: &Board) -> Outcome {
        let code = match s.status {
            X_WON => Self::USER_WINS,
            O_WON => Self::HUB_WINS,
            DRAW => Self::DRAW,
            _ => match s.turn {
                Role::User => Self::HUB_WINS, // user on turn forfeits
                Role::Hub => Self::USER_WINS,
            },
        };
        self.outcomes().into_iter().find(|o| o.code == code).unwrap()
    }
    fn max_depth_from(&self, s: &Board) -> u32 {
        if s.status != OPEN {
            0
        } else {
            s.cells.iter().filter(|&&c| c == 0).count() as u32
        }
    }
    fn n_state_bits(&self) -> usize {
        21
    }
    fn n_move_bits(&self) -> usize {
        4
    }
    fn state_bits(&self, s: &Board) -> Vec<bool> {
        let mut b = Vec::with_capacity(21);
        for c in s.cells {
            b.extend(uint_to_bits(u32::from(c), 2));
        }
        b.push(s.turn == Role::Hub);
        b.extend(uint_to_bits(u32::from(s.status), 2));
        b
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<Board> {
        ensure!(b.len() == 21, "tic-tac-toe state is 21 bits");
        let mut cells = [0u8; 9];
        for (i, c) in cells.iter_mut().enumerate() {
            *c = bits_to_uint(&b[Self::cell_bits(i)]) as u8;
            ensure!(*c <= 2, "cell {i} has value {c}");
        }
        Ok(Board { cells, turn: if b[Self::TURN_BIT] { Role::Hub } else { Role::User }, status: bits_to_uint(&b[Self::STATUS_BITS]) as u8 })
    }
    fn move_bits(&self, m: &u8) -> Vec<bool> {
        uint_to_bits(u32::from(*m), 4)
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<u8> {
        ensure!(b.len() == 4, "tic-tac-toe move is 4 bits");
        Ok(bits_to_uint(b) as u8)
    }
    fn describe_state(&self, s: &Board) -> String {
        let st = match s.status {
            X_WON => "X won",
            O_WON => "O won",
            DRAW => "draw",
            _ => "open",
        };
        format!("{} turn={} {st}", s.render(), s.turn)
    }
    fn describe_move(&self, m: &u8) -> String {
        format!("cell {m}")
    }

    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        let p = ctx.prover;
        let mk = i64::from(mark(p));
        let mover_status = i64::from(match p {
            Role::User => X_WON,
            Role::Hub => O_WON,
        });
        let mut v = Vec::new();

        // prior game already over
        v.push(LeafBuilder::new(ctx).prior_uint(Self::STATUS_BITS).finish("prior_closed", |c| bits_to_uint(&c.prior[Self::STATUS_BITS]) != 0));

        // prover not on turn
        let b = LeafBuilder::new(ctx).prior_uint(Self::TURN_BIT..Self::TURN_BIT + 1);
        v.push(match p {
            Role::User => b.finish("not_on_turn", |c| c.prior[Self::TURN_BIT]),
            Role::Hub => b.op(OP_NOT).finish("not_on_turn", |c| !c.prior[Self::TURN_BIT]),
        });

        // cell out of range
        v.push(LeafBuilder::new(ctx).mv_uint(0..4).int(8).op(OP_GREATERTHAN).finish("cell_out_of_range", |c| bits_to_uint(&c.mv) > 8));

        // cell occupied, one leaf per cell: mv == i and prior[i] != 0
        for i in 0..9 {
            v.push(
                LeafBuilder::new(ctx)
                    .mv_uint(0..4)
                    .prior_uint(Self::cell_bits(i))
                    .op(OP_0NOTEQUAL)
                    .op(OP_SWAP)
                    .int(i as i64)
                    .op(OP_NUMEQUAL)
                    .op(OP_BOOLAND)
                    .finish(&format!("cell_occupied_{i}"), move |c| bits_to_uint(&c.mv) as usize == i && bits_to_uint(&c.prior[Self::cell_bits(i)]) != 0),
            );
        }

        // board mismatch, one leaf per cell: new[i] != (mv == i ? mark : prior[i])
        for i in 0..9 {
            v.push(
                LeafBuilder::new(ctx)
                    .prior_uint(Self::cell_bits(i))
                    .mv_uint(0..4)
                    .new_uint(Self::cell_bits(i))
                    // stack: prior_i mv new_i
                    .op(OP_TOALTSTACK)
                    .int(i as i64)
                    .op(OP_NUMEQUAL)
                    .op(OP_IF)
                    .op(OP_DROP)
                    .int(mk)
                    .op(OP_ENDIF)
                    .op(OP_FROMALTSTACK)
                    .op(OP_NUMNOTEQUAL)
                    .finish(&format!("board_mismatch_{i}"), move |c| {
                        let expected = if bits_to_uint(&c.mv) as usize == i { mk as u32 } else { bits_to_uint(&c.prior[Self::cell_bits(i)]) };
                        bits_to_uint(&c.new[Self::cell_bits(i)]) != expected
                    }),
            );
        }

        // turn not flipped
        v.push(
            LeafBuilder::new(ctx)
                .prior_uint(Self::TURN_BIT..Self::TURN_BIT + 1)
                .new_uint(Self::TURN_BIT..Self::TURN_BIT + 1)
                .op(OP_NUMEQUAL)
                .finish("turn_not_flipped", |c| c.prior[Self::TURN_BIT] == c.new[Self::TURN_BIT]),
        );

        // status mismatch: new status != (mover wins ? mover_status : full ? DRAW : OPEN), computed on the new board
        let mut b = LeafBuilder::new(ctx).new_uint(Self::STATUS_BITS);
        for i in 0..9 {
            b = b.new_uint(Self::cell_bits(i));
        }
        // stack: status c0 .. c8
        b = b.int(0); // win accumulator
        for line in LINES {
            // pick depth of cell x when `extra` items sit above c8: (8 - x) + extra
            b = b.int(8 - line[0] as i64 + 1).op(OP_PICK).int(mk).op(OP_NUMEQUAL);
            b = b.int(8 - line[1] as i64 + 2).op(OP_PICK).int(mk).op(OP_NUMEQUAL).op(OP_BOOLAND);
            b = b.int(8 - line[2] as i64 + 2).op(OP_PICK).int(mk).op(OP_NUMEQUAL).op(OP_BOOLAND);
            b = b.op(OP_BOOLOR);
        }
        // stack: status c0..c8 win
        b = b.int(1); // full accumulator
        for i in 0..9 {
            b = b.int(8 - i as i64 + 2).op(OP_PICK).op(OP_0NOTEQUAL).op(OP_BOOLAND);
        }
        // stack: status c0..c8 win full
        b = b.op(OP_SWAP).op(OP_IF).op(OP_DROP).int(mover_status).op(OP_ELSE).op(OP_IF).int(i64::from(DRAW)).op(OP_ELSE).int(0).op(OP_ENDIF).op(OP_ENDIF);
        // stack: status c0..c8 expected
        b = b.op(OP_TOALTSTACK);
        for _ in 0..4 {
            b = b.op(OP_2DROP);
        }
        b = b.op(OP_DROP).op(OP_FROMALTSTACK).op(OP_NUMNOTEQUAL);
        v.push(b.finish("status_mismatch", move |c| {
            let cells: Vec<u32> = (0..9).map(|i| bits_to_uint(&c.new[Self::cell_bits(i)])).collect();
            let win = LINES.iter().any(|l| l.iter().all(|&i| cells[i] == mk as u32));
            let full = cells.iter().all(|&x| x != 0);
            let expected = if win { mover_status as u32 } else if full { u32::from(DRAW) } else { 0 };
            bits_to_uint(&c.new[Self::STATUS_BITS]) != expected
        }));

        // code mismatch: code != R(new)
        v.push(
            LeafBuilder::new(ctx)
                .new_uint(Self::TURN_BIT..Self::TURN_BIT + 1)
                .new_uint(Self::STATUS_BITS)
                .code_uint()
                // stack: turn status code
                .op(OP_TOALTSTACK)
                .op(OP_DUP)
                .op(OP_0NOTEQUAL)
                .op(OP_IF)
                .op(OP_NIP)
                .int(1)
                .op(OP_SUB) // status 1,2,3 -> codes 0,1,2
                .op(OP_ELSE)
                .op(OP_DROP)
                .op(OP_NOT) // open: turn user(0) -> HubWins(1); turn hub(1) -> UserWins(0)
                .op(OP_ENDIF)
                .op(OP_FROMALTSTACK)
                .op(OP_NUMNOTEQUAL)
                .finish("code_mismatch", |c| {
                    let status = bits_to_uint(&c.new[Self::STATUS_BITS]);
                    let expected = if status != 0 { status - 1 } else { u32::from(!c.new[Self::TURN_BIT]) };
                    expected != u32::from(c.code)
                }),
        );
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lngap_contract::Program;

    #[test]
    fn reference_game() {
        let t = TicTacToe;
        let mut s = t.initial();
        let moves = [(Role::User, 4), (Role::Hub, 1), (Role::User, 0), (Role::Hub, 8), (Role::User, 6), (Role::Hub, 3), (Role::User, 2)];
        for (r, m) in moves {
            assert_eq!(t.turn(&s), Some(r));
            s = t.transition(&s, &m, r).unwrap();
            let bits = t.state_bits(&s);
            assert_eq!(t.state_from_bits(&bits).unwrap(), s);
        }
        assert_eq!(s.status, X_WON);
        assert_eq!(s.render(), "XOX/OX./X.O");
        assert_eq!(t.resolution(&s).name, "UserWins");
        assert_eq!(t.turn(&s), None);
        assert_eq!(Program::max_depth_from_bits(&t, &t.state_bits(&s)).unwrap(), 0);
        assert!(t.transition(&s, &5, Role::Hub).is_err());
    }

    #[test]
    fn forfeit_rule() {
        let t = TicTacToe;
        let s = t.initial();
        assert_eq!(t.resolution(&s).name, "HubWins", "user on turn forfeits");
        let s2 = t.transition(&s, &4, Role::User).unwrap();
        assert_eq!(t.resolution(&s2).name, "UserWins", "hub on turn forfeits");
        assert_eq!(t.max_depth_from(&s), 9);
        assert_eq!(t.max_depth_from(&s2), 8);
    }
}

#[cfg(test)]
mod sizes {
    use super::*;
    use bitcoin::Amount;
    use lngap_btc::keys::Seed;
    use lngap_channel::{ChannelParams, CommitCtx, ContractOutput, PartyKeys};
    use lngap_contract::testing::depth_secrets;
    use lngap_contract::{ContractInstance, Program};
    use std::sync::Arc;

    /// Prints every leaf's script size for SCRIPTS.md (no chain needed).
    #[test]
    fn print_tree_sizes() {
        let prog: Arc<dyn Program> = Arc::new(TicTacToe);
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
        let pubs = [user.public(), hub.public()];
        let params = ChannelParams::regtest(Amount::from_sat(200_000));
        let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
        let keys: Vec<_> = (0..9).map(|d| depth_secrets(if d % 2 == 0 { Role::User } else { Role::Hub }, 10 + d as u8, &*prog).1).collect();
        let inst = ContractInstance::new(1, prog.clone(), Amount::from_sat(20_000), prog.initial_bits(), 300, 1, keys, vec![]).unwrap();
        let t0 = inst.tree(&ctx).unwrap();
        for (n, s, cb) in t0.sizes() {
            println!("SIZE C: {n}: script {s} B, control block {cb} B");
        }
        for d in [1u32, 2] {
            let t = inst.depth_tree(&ctx, d).unwrap();
            let total: usize = t.leaves().iter().map(|l| l.script.len()).sum();
            println!("SIZE C'_{d}: {} leaves, {total} B of script total", t.leaves().len());
            for (n, s, cb) in t.sizes() {
                println!("SIZE C'_{d}: {n}: script {s} B, control block {cb} B");
            }
        }
        let graph = inst.graph(&ctx, bitcoin::OutPoint::null(), &bitcoin::TxOut { value: inst.value, script_pubkey: t0.script_pubkey() }).unwrap();
        println!("SIZE graph: {} pre-signed transactions for M = 9", graph.len());
    }
}
