//! The contract's leaves for a dispute: `escalate` (move 1 and the
//! claim's input words), `inputs` (the rest of the input), and each
//! ladder output's tree.
//!
//! The ladder output after move `j` carries:
//! - `post` (`j < 2R + 1`): the next mover's move, 2-of-2 pre-signed into
//!   the next output, after `1 OP_CSV` (with no TRUC, nothing of the
//!   opponent's may sit in the mempool on an unconfirmed link);
//! - its timeout, `split_<payee>`: 2-of-2 pre-signed after `w = delta +
//!   delta'` to the mover of `j`, except at the last depth, where Alice
//!   must prove the step and the hub's split waits `w + delta'`;
//! - the other side's rules on move `j`, `disprove_<rule>`, runtime spends
//!   after `delta` under the disprover's key;
//! - `equiv_d_<d>_<f>` for every move so far and each of its fields: two
//!   different values signed under that field's key (only its mover holds
//!   it) give the other side the output at once, so that a replay after
//!   off-chain play is faithful;
//! - at the last depth, Alice's proofs `prove_<class>`, 2-of-2 pre-signed
//!   after `w` with fixed outputs.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::Leaf;
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_zk::challenges::ProgramInfo;

use crate::rules::{choice_rule, final_rules, prove_rules, Rule};
use crate::script::Msg;
use crate::{mover_at, Kind, Schedule};

fn drop_n(mut b: Builder, n: usize) -> Builder {
    for _ in 0..n / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    if n % 2 == 1 {
        b = b.push_opcode(OP_DROP);
    }
    b
}

/// Verify a one-time signature and drop what it signed.
fn verify_drop(b: Builder, k: &WotsPublic) -> Builder {
    drop_n(b.wots_verify(k), k.params.message_digits as usize)
}

/// Verify a move's signatures, field 0 first (its reveal on top), and drop
/// what they signed.
fn verify_move(mut b: Builder, keys: &[WotsPublic]) -> Builder {
    for k in keys {
        b = verify_drop(b, k);
    }
    b
}

/// What the ladder is built from.
pub struct Spec<'a> {
    pub ctx: &'a CommitCtx<'a>,
    pub s: &'a Schedule,
    pub info: &'a ProgramInfo,
    /// The move keys, `moves[d - 1][f]` for depth `d`'s field `f` (its
    /// mover's).
    pub moves: &'a [Vec<WotsPublic>],
    /// Alice's input-word keys.
    pub words: &'a [WotsPublic],
    /// The relative timelock on `post` (1 without TRUC).
    pub post_csv: u16,
    /// Under a jump list: the read and jump challenges' keys.
    pub tail: Option<&'a crate::tail::TailKeys>,
}

impl Spec<'_> {
    pub fn key(&self, m: Msg) -> WotsPublic {
        match m {
            Msg::Field(d, f) => self.moves[(d - 1) as usize][f].clone(),
            Msg::Word(j) => self.words[j].clone(),
            Msg::Path(l, f) => self.tail.expect("a jump list's tail").path[l][f].clone(),
            Msg::Hop(l) => self.tail.expect("a jump list's tail").hop[l].clone(),
        }
    }
    fn w(&self) -> u16 {
        self.ctx.params.delta + self.ctx.params.delta_prime
    }
    /// `escalate` on the contract output: move 1 and the claim's input
    /// words `claim_words`, 2-of-2 pre-signed, after `to_self_delay`.
    /// Witness, wire order: the words' reveals, LAST word first, move 1's
    /// fields' reveals, its LAST field first, the hub's signature, Alice's.
    pub fn escalate_leaf(&self, claim_words: &[usize]) -> Leaf {
        let mut b = Builder::new();
        let mut tl = Timelock::NONE;
        let d = self.ctx.params.to_self_delay;
        if d > 0 {
            b = b.csv(d);
            tl.csv = Some(d);
        }
        let mut b = verify_move(self.ctx.two_of_two_verify(b), &self.moves[0]);
        for &j in claim_words {
            b = verify_drop(b, &self.words[j]);
        }
        Leaf::new("escalate", b.push_int(1).into_script(), tl)
    }
    /// `inputs` on the output `escalate` creates: the rest of Alice's
    /// signed input words, 2-of-2 pre-signed into the ladder output after
    /// move 1. Witness, wire order: the words' reveals, LAST word first,
    /// the hub's signature, Alice's.
    pub fn inputs_leaf(&self, rest: &[usize]) -> Leaf {
        let mut b = self.ctx.two_of_two_verify(Builder::new());
        for &j in rest {
            b = verify_drop(b, &self.words[j]);
        }
        Leaf::new("inputs", b.push_int(1).into_script(), Timelock::NONE)
    }
    /// The rules on move `j`: the other side's.
    pub fn rules_on(&self, j: u32) -> Vec<Rule> {
        match self.s.kind(j) {
            Kind::Choice(r) => vec![choice_rule(self.s, r)],
            Kind::Final => final_rules(self.s, self.info),
            Kind::Claim | Kind::Hashes(_) => vec![],
        }
    }
    /// Who is paid if the output after move `j` times out.
    pub fn timeout_payee(&self, j: u32) -> Role {
        if j == self.s.depths() {
            mover_at(j).other()
        } else {
            mover_at(j)
        }
    }
    /// The timeout's leaf name, by payee.
    pub fn split_name(payee: Role) -> &'static str {
        if payee == Role::User {
            "split_UserWins"
        } else {
            "split_HubWins"
        }
    }
    /// The leaves of the ladder output after move `j`.
    pub fn leaves(&self, j: u32) -> Vec<Leaf> {
        let (ctx, m) = (self.ctx, self.s.depths());
        let mut v = vec![];
        if j < m {
            let csv = self.post_csv;
            let (mut b, mut tl) = (Builder::new(), Timelock::NONE);
            if csv > 0 {
                b = b.csv(csv);
                tl.csv = Some(csv);
            }
            let b = verify_move(ctx.two_of_two_verify(b), &self.moves[j as usize]);
            v.push(Leaf::new("post", b.push_int(1).into_script(), tl));
        }
        // the timeout
        let payee = self.timeout_payee(j);
        let lock = if j == m { self.w() + ctx.params.delta_prime } else { self.w() };
        let b = ctx.two_of_two_verify(Builder::new().csv(lock));
        v.push(Leaf::new(Self::split_name(payee), b.push_int(1).into_script(), Timelock::csv(lock)));
        // the rules on move j, the other side's
        let disprover = mover_at(j).other();
        let key = |msg: Msg| self.key(msg);
        for r in self.rules_on(j) {
            let gate = Builder::new().csv(ctx.params.delta).checksigverify(&ctx.key(disprover).payment);
            v.push(Leaf::new(format!("disprove_{}", r.name), r.script(gate, &key), Timelock::csv(ctx.params.delta)));
        }
        // equivocation of any move so far
        for d in 1..=j {
            for (f, k) in self.moves[(d - 1) as usize].iter().enumerate() {
                v.push(equiv_move_leaf(ctx, &format!("{d}_{f}"), k, mover_at(d).other()));
            }
        }
        // under a jump list, the hub's path (the read and jump challenges)
        if j == m {
            if let Some(t) = self.tail {
                let csv = self.post_csv.max(1);
                let b = verify_move(ctx.two_of_two_verify(Builder::new().csv(csv)), &t.path[0]);
                v.push(Leaf::new("path", b.push_int(1).into_script(), Timelock::csv(csv)));
            }
        }
        // Alice's proofs
        if j == m {
            let w = self.w();
            for r in prove_rules(self.s, self.info) {
                let gate = ctx.two_of_two_verify(Builder::new().csv(w));
                v.push(Leaf::new(r.name.clone(), r.script(gate, &key), Timelock::csv(w)));
            }
        }
        v
    }
}

/// Where in the tail an output sits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TailOut {
    /// After the hub's path link `l` (0 or 1).
    Path(usize),
    /// After Alice's choice of hop on path link `l`'s output.
    Hop(usize),
}

impl Spec<'_> {
    /// The leaves of an output in the tail (a jump list's read and jump
    /// challenges, lngap_ladder::tail):
    /// - after path link 0: the hub's second link (`post`), Alice's choice
    ///   (`hop`), the hub's verdicts after `w` (`disprove_jump`,
    ///   `disprove_read_<r>`), Alice's timeout after `w + delta'`;
    /// - after path link 1: the same but `post`;
    /// - after her choice: the hub's reveal of the hop (`disprove_hop_<k>`,
    ///   `disprove_hop_range`), Alice's timeout after `w`.
    pub fn tail_leaves(&self, at: TailOut) -> Vec<Leaf> {
        let ctx = self.ctx;
        let t = self.tail.expect("a jump list's tail");
        let csv = self.post_csv.max(1);
        let w = self.w();
        let key = |msg: Msg| self.key(msg);
        let mut v = vec![];
        let hub_gate = |lock: u16| Builder::new().csv(lock).checksigverify(&ctx.key(Role::Hub).payment);
        match at {
            TailOut::Path(l) => {
                if l == 0 {
                    let b = verify_move(ctx.two_of_two_verify(Builder::new().csv(csv)), &t.path[1]);
                    v.push(Leaf::new("post", b.push_int(1).into_script(), Timelock::csv(csv)));
                }
                let b = verify_drop(ctx.two_of_two_verify(Builder::new().csv(csv)), &t.hop[l]);
                v.push(Leaf::new("hop", b.push_int(1).into_script(), Timelock::csv(csv)));
                for r in crate::tail::verdicts(self.s, l) {
                    v.push(Leaf::new(format!("disprove_{}", r.name), r.script(hub_gate(w), &key), Timelock::csv(w)));
                }
                let lock = w + ctx.params.delta_prime;
                let b = ctx.two_of_two_verify(Builder::new().csv(lock));
                v.push(Leaf::new(Self::split_name(Role::User), b.push_int(1).into_script(), Timelock::csv(lock)));
            }
            TailOut::Hop(l) => {
                for r in crate::tail::hop_rules(self.s, l) {
                    v.push(Leaf::new(format!("disprove_{}", r.name), r.script(hub_gate(ctx.params.delta), &key), Timelock::csv(ctx.params.delta)));
                }
                let b = ctx.two_of_two_verify(Builder::new().csv(w));
                v.push(Leaf::new(Self::split_name(Role::User), b.push_int(1).into_script(), Timelock::csv(w)));
            }
        }
        v
    }
    /// A tail rule by name (without `disprove_`), for its witness.
    pub fn tail_rule(&self, at: TailOut, name: &str) -> Option<Rule> {
        let rules = match at {
            TailOut::Path(l) => crate::tail::verdicts(self.s, l),
            TailOut::Hop(l) => crate::tail::hop_rules(self.s, l),
        };
        rules.into_iter().find(|r| r.name == name)
    }
}

/// `equiv_d_<label>`: two different messages signed under one move key;
/// the `exhibitor` (the other side) takes the output at once. A runtime
/// spend. Witness, wire order: one reveal, the other, the exhibitor's
/// signature.
pub fn equiv_move_leaf(ctx: &CommitCtx, label: &str, key: &WotsPublic, exhibitor: Role) -> Leaf {
    let m = key.params.message_digits as usize;
    let mut b = Builder::new().checksigverify(&ctx.key(exhibitor).payment).wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    // the two message vectors must differ somewhere
    b = b.push_int(0);
    for j in 0..m {
        b = b
            .push_int((m - j) as i64)
            .push_opcode(OP_PICK)
            .push_int((2 * m - j + 1) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SUB)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_ADD);
    }
    b = drop_n(b.push_opcode(OP_VERIFY), 2 * m);
    Leaf::new(format!("equiv_d_{label}"), b.push_int(1).into_script(), Timelock::NONE)
}
