//! The blackjack disprove family over the parked tuple (D57).
//!
//! The head layout, the honest transitions and every predicate's native
//! mirror are `lngap-blackjack`'s; this module builds the Script leaves.
//! After a rebuttal at depth `d` the parked register file is the pair
//! `head(d-1) || head(d)` (192 digits, the prior at 0..96, the new at
//! 96..192); at depth 1 it is the single head (96 digits) and the prior is
//! the constant initial head, whose state digits are all zero, so the
//! leaves read constants in its place.
//!
//! Share strings never ride in the heads (D57: OP_SHA256 and OP_SIZE act
//! on one element, and rejoining nibbles would be OP_CAT). A leaf that
//! needs a share takes its string as a witness element BELOW the pair
//! reveal (the chess exhibit convention), checks it against the commitment
//! pinned in the leaf, and reads the value with OP_SIZE.
//!
//! The family: `wrong_slot` (the venue's word0), `bj_malformed`,
//! `bj_transition`, `bj_counters`, `bj_cards_kept`, `bj_status`,
//! `bj_dealer`, and per card position `k` the `bj_share_k` (the mover's
//! share revealed here opens out of range) and, at the house's depths,
//! `bj_card_k` (a card dealt here is not the sum of its shares mod 13).
//!
//! Leaves are written with a small stack emitter: it models the main stack
//! (witness strings, the file's digits, named values), so every PICK depth
//! is computed, not counted by hand. A kind leaf leaves one element, true
//! when the predicate holds (the leaf fires); the finish parks it, drops
//! everything else and brings it back as the only element.

use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::opcodes::Opcode;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use lngap_blackjack as bj;
use lngap_blackjack::{action, digit, phase, status, Commitments, State, HOLE, K};
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::Leaf;
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_factchain::HEAD_BYTES;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};
use lngap_lamport::PublicKey;

use crate::ttt::{self, Layout, PosLeaf};

/// Head digits.
const HD: usize = HEAD_BYTES * 2;

/// The mover's role at the parked depth as the rules name it.
fn player(l: &Layout) -> bool {
    l.mover == Role::User
}

// ----- the emitter -----

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Slot {
    /// A witness string, deepest first.
    Wit(u8),
    /// A file digit.
    Dig(u16),
    /// A named value.
    N(u16),
    Anon,
}

struct E {
    b: Builder,
    st: Vec<Slot>,
    frames: Vec<(usize, Option<usize>)>,
    next: u16,
    l: Layout,
}

impl E {
    /// After `wots_verify`: the witness strings (deepest), then the file.
    fn new(key: &WotsPublic, l: &Layout, wits: usize) -> E {
        let mut st: Vec<Slot> = (0..wits).map(|i| Slot::Wit(i as u8)).collect();
        st.extend((0..l.file).map(|j| Slot::Dig(j as u16)));
        E { b: Builder::new().wots_verify(key), st, frames: vec![], next: 0, l: *l }
    }
    fn raw(&mut self, op: Opcode) {
        self.b = std::mem::replace(&mut self.b, Builder::new()).push_opcode(op);
    }
    fn int(&mut self, v: i64) {
        self.b = std::mem::replace(&mut self.b, Builder::new()).push_int(v);
        self.st.push(Slot::Anon);
    }
    fn bytes(&mut self, v: &[u8; 32]) {
        self.b = std::mem::replace(&mut self.b, Builder::new()).push_slice(v);
        self.st.push(Slot::Anon);
    }
    fn op(&mut self, op: Opcode, pops: usize, pushes: usize) {
        self.raw(op);
        for _ in 0..pops {
            self.st.pop().expect("emitter underflow");
        }
        for _ in 0..pushes {
            self.st.push(Slot::Anon);
        }
    }
    fn depth(&self, s: Slot) -> usize {
        let p = self.st.iter().rposition(|x| *x == s).unwrap_or_else(|| panic!("{s:?} is not on the stack"));
        self.st.len() - 1 - p
    }
    /// Copy a slot to the top.
    fn get(&mut self, s: Slot) {
        match self.depth(s) {
            0 => self.op(OP_DUP, 0, 1),
            1 => self.op(OP_OVER, 0, 1),
            d => {
                self.b = std::mem::replace(&mut self.b, Builder::new()).push_int(d as i64);
                self.raw(OP_PICK);
                self.st.push(Slot::Anon);
            }
        }
    }
    /// Name the top value.
    fn name(&mut self) -> Slot {
        let n = Slot::N(self.next);
        self.next += 1;
        *self.st.last_mut().expect("nothing to name") = n;
        n
    }
    fn if_(&mut self) {
        self.st.pop().expect("condition");
        self.raw(OP_IF);
        self.frames.push((self.st.len(), None));
    }
    fn notif(&mut self) {
        self.st.pop().expect("condition");
        self.raw(OP_NOTIF);
        self.frames.push((self.st.len(), None));
    }
    fn else_(&mut self) {
        let f = self.frames.last_mut().expect("ELSE without IF");
        assert!(f.1.is_none(), "two ELSEs");
        f.1 = Some(self.st.len());
        let base = f.0;
        self.st.truncate(base);
        self.raw(OP_ELSE);
    }
    fn endif(&mut self) {
        let (base, then_len) = self.frames.pop().expect("ENDIF without IF");
        let len = self.st.len();
        match then_len {
            Some(t) => assert_eq!(t, len, "the branches leave different stack heights"),
            None => assert_eq!(base, len, "an IF without ELSE must keep the stack height"),
        }
        // what either branch left is anonymous
        for s in self.st[base.min(len)..].iter_mut() {
            *s = Slot::Anon;
        }
        self.raw(OP_ENDIF);
    }
    // --- arithmetic on the top ---
    fn eq(&mut self, v: i64) {
        self.int(v);
        self.op(OP_NUMEQUAL, 2, 1);
    }
    fn ne(&mut self, v: i64) {
        self.int(v);
        self.op(OP_NUMNOTEQUAL, 2, 1);
    }
    fn gt(&mut self, v: i64) {
        self.int(v);
        self.op(OP_GREATERTHAN, 2, 1);
    }
    fn and(&mut self) {
        self.op(OP_BOOLAND, 2, 1);
    }
    fn or(&mut self) {
        self.op(OP_BOOLOR, 2, 1);
    }
    fn not(&mut self) {
        self.op(OP_NOT, 1, 1);
    }
    /// `a == b` for two slots.
    fn eqs(&mut self, a: Slot, b: Slot) {
        self.get(a);
        self.get(b);
        self.op(OP_NUMEQUAL, 2, 1);
    }
    fn nes(&mut self, a: Slot, b: Slot) {
        self.get(a);
        self.get(b);
        self.op(OP_NUMNOTEQUAL, 2, 1);
    }
    // --- the heads ---
    /// New-head digit `j`.
    fn nd(&mut self, j: usize) {
        self.get(Slot::Dig((self.l.new + j) as u16));
    }
    /// Prior-head digit `j` (a state digit): the file's, or the constant
    /// initial head's zero at depth 1.
    fn pd(&mut self, j: usize) {
        match self.l.prior {
            Some(off) => self.get(Slot::Dig((off + j) as u16)),
            None => self.int(0),
        }
    }
    /// A byte from two digits of the new (`new`) or prior head, named.
    fn byte(&mut self, new: bool, j: usize) -> Slot {
        if new { self.nd(j) } else { self.pd(j) }
        for _ in 0..4 {
            self.op(OP_DUP, 0, 1);
            self.op(OP_ADD, 2, 1);
        }
        if new { self.nd(j + 1) } else { self.pd(j + 1) }
        self.op(OP_ADD, 2, 1);
        self.name()
    }
    fn nib(&mut self, new: bool, j: usize) -> Slot {
        if new { self.nd(j) } else { self.pd(j) }
        self.name()
    }
    /// The best total of the NEW head's cards at the positions `fixed`
    /// plus `lo <= k < hi` (named bounds; `k` ranges over 0..16).
    fn hand_total(&mut self, fixed: &[usize], lo: Slot, hi: Slot) -> Slot {
        let mut vals = 0;
        for k in 0..K {
            let always = fixed.contains(&k);
            // member?
            if !always {
                self.get(lo);
                self.int(k as i64);
                self.op(OP_LESSTHANOREQUAL, 2, 1);
                self.int(k as i64);
                self.get(hi);
                self.op(OP_LESSTHAN, 2, 1);
                self.and();
            } else {
                self.int(1);
            }
            let m = self.name();
            // value: min(r + 1, 10), 0 when not a member
            self.nd(digit::CARDS + k);
            self.op(OP_1ADD, 1, 1);
            self.int(10);
            self.op(OP_MIN, 2, 1);
            if !always {
                self.get(m);
                self.notif();
                self.op(OP_DROP, 1, 0);
                self.int(0);
                self.endif();
            }
            // ace: r == 0 and a member
            self.nd(digit::CARDS + k);
            self.eq(0);
            self.get(m);
            self.and();
            // [.., m, val, ace] -> keep val and ace, drop m
            self.op(OP_ROT, 3, 3);
            self.op(OP_DROP, 1, 0);
            vals += 1;
        }
        // [.., (val, ace) x 16]: fold the aces, then the values
        // gather aces: move every ace to the altstack
        for _ in 0..vals {
            self.op(OP_TOALTSTACK, 1, 0); // ace
            self.op(OP_TOALTSTACK, 1, 0); // val
        }
        // altstack top: val_15, ace_15, ... ; bring back values summed and aces or-ed
        self.int(0); // sum
        self.int(0); // ace
        for _ in 0..vals {
            // [sum, ace] <- val, ace_k
            self.op(OP_FROMALTSTACK, 0, 1); // val
            self.op(OP_ROT, 3, 3); // [ace, val, sum]
            self.op(OP_ADD, 2, 1); // [ace, sum']
            self.op(OP_SWAP, 2, 2); // [sum', ace]
            self.op(OP_FROMALTSTACK, 0, 1); // ace_k
            self.or(); // [sum', ace']
        }
        // best: sum + 10 if ace and sum <= 11
        self.op(OP_OVER, 0, 1); // [sum, ace, sum]
        self.int(11);
        self.op(OP_LESSTHANOREQUAL, 2, 1); // [sum, ace, sum<=11]
        self.and(); // [sum, soft]
        self.if_();
        self.int(10);
        self.op(OP_ADD, 2, 1);
        self.endif();
        self.name()
    }
    /// Park the result, drop everything else, bring it back.
    fn finish(mut self) -> ScriptBuf {
        assert!(self.frames.is_empty(), "unclosed IF");
        self.raw(OP_TOALTSTACK);
        let n = self.st.len() - 1;
        for _ in 0..n / 2 {
            self.raw(OP_2DROP);
        }
        if n % 2 == 1 {
            self.raw(OP_DROP);
        }
        self.raw(OP_FROMALTSTACK);
        self.b.into_script()
    }
}

/// The fields a leaf reads, loaded and named.
struct F {
    pph: Slot,
    pst: Slot,
    pnp: Slot,
    pds: Slot,
    a: Slot,
    nph: Slot,
    nst: Slot,
    nnp: Slot,
    nds: Slot,
    nlo: Slot,
    nhi: Slot,
}

fn load(e: &mut E) -> F {
    let pph = e.nib(false, digit::PHASE);
    let pst = e.nib(false, digit::STATUS);
    let pnp = e.byte(false, digit::NP);
    let pds = e.byte(false, digit::DS);
    let a = e.nib(true, digit::ACTION);
    let nph = e.nib(true, digit::PHASE);
    let nst = e.nib(true, digit::STATUS);
    let nnp = e.byte(true, digit::NP);
    let nds = e.byte(true, digit::DS);
    let nlo = e.byte(true, digit::LO);
    let nhi = e.byte(true, digit::HI);
    F { pph, pst, pnp, pds, a, nph, nst, nnp, nds, nlo, nhi }
}

/// Push `x == v && y == w` for slots `x`, `y`.
fn is2(e: &mut E, x: Slot, v: u8, y: Slot, w: u8) {
    e.get(x);
    e.eq(i64::from(v));
    e.get(y);
    e.eq(i64::from(w));
    e.and();
}

// ----- the leaves -----

/// The prior state the native mirrors see: the parked prior, or the
/// initial state at depth 1.
fn prior_state(l: &Layout, p: &[u8; HEAD_BYTES]) -> State {
    if l.prior.is_some() { State::from_head(p) } else { State::initial() }
}

/// `bj_malformed`: the new head is not a well-formed encoding.
fn malformed(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut e = E::new(key, l, 0);
    let f = load(&mut e);
    e.get(f.a);
    e.gt(i64::from(action::MAX));
    e.get(f.nph);
    e.gt(i64::from(phase::MAX));
    e.or();
    e.get(f.nst);
    e.gt(i64::from(status::MAX));
    e.or();
    e.nd(digit::PAD11);
    e.op(OP_0NOTEQUAL, 1, 1);
    e.or();
    for s in [f.nnp, f.nds, f.nlo, f.nhi] {
        e.get(s);
        e.gt(16);
        e.or();
    }
    for k in 0..K {
        e.nd(digit::CARDS + k);
        e.gt(12);
        e.or();
    }
    // the padding: any non-zero digit
    e.int(0);
    for j in digit::PAD_FROM..HD {
        e.nd(j);
        e.op(OP_ADD, 2, 1);
    }
    e.op(OP_0NOTEQUAL, 1, 1);
    e.or();
    PosLeaf { name: "bj_malformed".into(), script: e.finish(), fires: Arc::new(|_, h| bj::head_malformed(h)) }
}

/// `bj_transition`: the action not allowed for this mover in the prior
/// phase, or the wrong next phase.
fn transition(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut e = E::new(key, l, 0);
    let f = load(&mut e);
    let pl = player(l);
    if pl {
        // START, DEAL -> DEALT
        is2(&mut e, f.pph, phase::START, f.a, action::DEAL);
        e.get(f.nph);
        e.eq(i64::from(phase::DEALT));
        e.and();
        // DECIDE, HIT (np <= 10) -> HIT
        is2(&mut e, f.pph, phase::DECIDE, f.a, action::HIT);
        e.get(f.pnp);
        e.int(i64::from(bj::MAX_HIT_NP));
        e.op(OP_LESSTHANOREQUAL, 2, 1);
        e.and();
        e.get(f.nph);
        e.eq(i64::from(phase::HIT));
        e.and();
        e.or();
        // DECIDE, STAND -> STOOD
        is2(&mut e, f.pph, phase::DECIDE, f.a, action::STAND);
        e.get(f.nph);
        e.eq(i64::from(phase::STOOD));
        e.and();
        e.or();
        // DONE, ACK (player won or push) -> CLOSED
        is2(&mut e, f.pph, phase::DONE, f.a, action::ACK);
        e.get(f.pst);
        e.eq(i64::from(status::PLAYER));
        e.get(f.pst);
        e.eq(i64::from(status::PUSH));
        e.or();
        e.and();
        e.get(f.nph);
        e.eq(i64::from(phase::CLOSED));
        e.and();
        e.or();
    } else {
        // DEALT, REVEAL -> DECIDE
        is2(&mut e, f.pph, phase::DEALT, f.a, action::REVEAL);
        e.get(f.nph);
        e.eq(i64::from(phase::DECIDE));
        e.and();
        // HIT, REVEAL -> DONE if the status is set, else DECIDE
        is2(&mut e, f.pph, phase::HIT, f.a, action::REVEAL);
        e.get(f.nst);
        e.op(OP_0NOTEQUAL, 1, 1);
        e.if_();
        e.int(i64::from(phase::DONE));
        e.else_();
        e.int(i64::from(phase::DECIDE));
        e.endif();
        let want = e.name();
        e.eqs(want, f.nph);
        e.op(OP_NIP, 2, 1);
        e.and();
        e.or();
        // STOOD, REVEAL -> DONE
        is2(&mut e, f.pph, phase::STOOD, f.a, action::REVEAL);
        e.get(f.nph);
        e.eq(i64::from(phase::DONE));
        e.and();
        e.or();
    }
    e.not();
    let lc = *l;
    PosLeaf {
        name: "bj_transition".into(),
        script: e.finish(),
        fires: Arc::new(move |p, h| bj::transition_fires(&prior_state(&lc, p), &State::from_head(h), pl)),
    }
}

/// `bj_counters`: np, ds, lo, hi not what the action requires.
fn counters(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut e = E::new(key, l, 0);
    let f = load(&mut e);
    // pnp + 1, named
    e.get(f.pnp);
    e.op(OP_1ADD, 1, 1);
    let pnp1 = e.name();
    // each case: [cond] [mismatch] BOOLAND, OR-ed into an accumulator
    e.int(0);
    // a mismatch builder: fields vs (np?, ds, lo, hi), each an Int or a Slot
    #[derive(Clone, Copy)]
    enum V {
        I(i64),
        S(Slot),
        Free,
    }
    let mism = |e: &mut E, want: [V; 4]| {
        e.int(0);
        for (s, w) in [f.nnp, f.nds, f.nlo, f.nhi].into_iter().zip(want) {
            match w {
                V::I(v) => {
                    e.get(s);
                    e.ne(v);
                }
                V::S(x) => e.nes(s, x),
                V::Free => continue,
            }
            e.or();
        }
    };
    let cases: Vec<(u8, Option<u8>, [V; 4])> = vec![
        (action::DEAL, None, [V::I(0), V::I(0), V::I(0), V::I(3)]),
        (action::REVEAL, Some(phase::DEALT), [V::I(3), V::I(0), V::I(0), V::I(3)]),
        (action::HIT, None, [V::S(f.pnp), V::S(f.pds), V::S(f.pnp), V::S(pnp1)]),
        (action::REVEAL, Some(phase::HIT), [V::S(pnp1), V::S(f.pds), V::S(f.pnp), V::S(pnp1)]),
        (action::STAND, None, [V::S(f.pnp), V::S(f.pnp), V::S(f.pnp), V::I(K as i64)]),
        (action::REVEAL, Some(phase::STOOD), [V::Free, V::S(f.pds), V::S(f.pnp), V::I(K as i64)]),
        (action::ACK, None, [V::S(f.pnp), V::S(f.pds), V::I(0), V::I(0)]),
    ];
    for (a, pp, want) in cases {
        e.get(f.a);
        e.eq(i64::from(a));
        if let Some(pp) = pp {
            e.get(f.pph);
            e.eq(i64::from(pp));
            e.and();
        }
        mism(&mut e, want);
        e.and();
        e.or();
    }
    let lc = *l;
    PosLeaf {
        name: "bj_counters".into(),
        script: e.finish(),
        fires: Arc::new(move |p, h| bj::counters_fires(&prior_state(&lc, p), &State::from_head(h))),
    }
}

/// `dealt(S, k)` for the prior (`new = false`) or new head, on the stack.
fn dealt(e: &mut E, k: usize, np: Slot, ds: Slot, ph: Slot) {
    e.int(k as i64);
    e.get(np);
    e.op(OP_LESSTHAN, 2, 1);
    if k == HOLE {
        e.get(ds);
        e.op(OP_0NOTEQUAL, 1, 1);
        e.get(ph);
        e.int(i64::from(phase::DONE));
        e.op(OP_GREATERTHANOREQUAL, 2, 1);
        e.and();
        e.or();
    }
}

/// `bj_cards_kept`: a card dealt in the prior changed, or an undealt
/// position of the new head is not zero.
fn cards_kept(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut e = E::new(key, l, 0);
    let f = load(&mut e);
    e.int(0);
    for k in 0..K {
        if l.prior.is_some() {
            dealt(&mut e, k, f.pnp, f.pds, f.pph);
            e.nd(digit::CARDS + k);
            e.pd(digit::CARDS + k);
            e.op(OP_NUMNOTEQUAL, 2, 1);
            e.and();
            e.or();
        }
        dealt(&mut e, k, f.nnp, f.nds, f.nph);
        e.not();
        e.nd(digit::CARDS + k);
        e.op(OP_0NOTEQUAL, 1, 1);
        e.and();
        e.or();
    }
    let lc = *l;
    PosLeaf {
        name: "bj_cards_kept".into(),
        script: e.finish(),
        fires: Arc::new(move |p, h| bj::cards_kept_fires(&prior_state(&lc, p), &State::from_head(h))),
    }
}

/// The player's and the dealer's totals over the NEW head: player
/// {0, 1} + 3..lim (lim = ds if set, else np); dealer {2, 15} + ds..np.
fn totals(e: &mut E, f: &F) -> (Slot, Slot) {
    e.int(bj::FIRST_HIT as i64);
    let three = e.name();
    e.get(f.nds);
    e.op(OP_0NOTEQUAL, 1, 1);
    e.if_();
    e.get(f.nds);
    e.else_();
    e.get(f.nnp);
    e.endif();
    let lim = e.name();
    let pt = e.hand_total(&[0, 1], three, lim);
    let dt = e.hand_total(&[bj::UP, HOLE], f.nds, f.nnp);
    (pt, dt)
}

/// `bj_status`: the status is not the one the transition produces.
fn status_leaf(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut e = E::new(key, l, 0);
    let f = load(&mut e);
    let (pt, dt) = totals(&mut e, &f);
    e.int(0);
    // open after DEAL, HIT, STAND, and the house's first REVEAL
    e.get(f.a);
    e.eq(i64::from(action::DEAL));
    e.get(f.a);
    e.eq(i64::from(action::HIT));
    e.or();
    e.get(f.a);
    e.eq(i64::from(action::STAND));
    e.or();
    is2(&mut e, f.a, action::REVEAL, f.pph, phase::DEALT);
    e.or();
    e.get(f.nst);
    e.op(OP_0NOTEQUAL, 1, 1);
    e.and();
    e.or();
    // after a hit's card: HOUSE if the player busted, else OPEN
    is2(&mut e, f.a, action::REVEAL, f.pph, phase::HIT);
    e.get(pt);
    e.gt(21);
    e.op(OP_DUP, 0, 1);
    e.op(OP_ADD, 2, 1); // 2 * bust
    e.get(f.nst);
    e.op(OP_NUMNOTEQUAL, 2, 1);
    e.and();
    e.or();
    // the showdown
    is2(&mut e, f.a, action::REVEAL, f.pph, phase::STOOD);
    e.get(dt);
    e.gt(21);
    e.get(pt);
    e.get(dt);
    e.op(OP_GREATERTHAN, 2, 1);
    e.or(); // player wins
    e.if_();
    e.int(i64::from(status::PLAYER));
    e.else_();
    e.get(pt);
    e.get(dt);
    e.op(OP_LESSTHAN, 2, 1);
    e.if_();
    e.int(i64::from(status::HOUSE));
    e.else_();
    e.int(i64::from(status::PUSH));
    e.endif();
    e.endif();
    e.get(f.nst);
    e.op(OP_NUMNOTEQUAL, 2, 1);
    e.and();
    e.or();
    // ACK keeps the status
    e.get(f.a);
    e.eq(i64::from(action::ACK));
    e.nes(f.nst, f.pst);
    e.and();
    e.or();
    let lc = *l;
    PosLeaf {
        name: "bj_status".into(),
        script: e.finish(),
        fires: Arc::new(move |p, h| bj::status_fires(&prior_state(&lc, p), &State::from_head(h))),
    }
}

/// `bj_dealer`: the dealer phase broke the drawing rule.
fn dealer(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let mut e = E::new(key, l, 0);
    let f = load(&mut e);
    let dt = e.hand_total(&[bj::UP, HOLE], f.nds, f.nnp);
    e.get(f.nnp);
    e.op(OP_1SUB, 1, 1);
    let np1 = e.name();
    let before = e.hand_total(&[bj::UP, HOLE], f.nds, np1);
    is2(&mut e, f.a, action::REVEAL, f.pph, phase::STOOD);
    // bounds
    e.get(f.nnp);
    e.get(f.pnp);
    e.op(OP_LESSTHAN, 2, 1);
    e.get(f.nnp);
    e.gt(i64::from(bj::DRAW_LIMIT));
    e.or();
    e.get(f.nnp);
    e.get(f.nds);
    e.op(OP_LESSTHAN, 2, 1);
    e.or();
    // stopped below 17 with positions left
    e.get(dt);
    e.int(17);
    e.op(OP_LESSTHAN, 2, 1);
    e.get(f.nnp);
    e.int(i64::from(bj::DRAW_LIMIT));
    e.op(OP_LESSTHAN, 2, 1);
    e.and();
    e.or();
    // drew at 17 or more
    e.get(f.nnp);
    e.get(f.nds);
    e.op(OP_GREATERTHAN, 2, 1);
    e.get(before);
    e.int(17);
    e.op(OP_GREATERTHANOREQUAL, 2, 1);
    e.and();
    e.or();
    e.and();
    let lc = *l;
    PosLeaf {
        name: "bj_dealer".into(),
        script: e.finish(),
        fires: Arc::new(move |p, h| bj::dealer_fires(&prior_state(&lc, p), &State::from_head(h))),
    }
}

/// Open witness string `w` against commitment `c`: fail unless it hashes
/// to `c`; leave its value (|s| - 32), named.
fn open(e: &mut E, w: u8, c: &[u8; 32]) -> Slot {
    e.get(Slot::Wit(w));
    e.op(OP_SHA256, 1, 1);
    e.bytes(c);
    e.op(OP_EQUALVERIFY, 2, 0);
    e.get(Slot::Wit(w));
    e.op(OP_SIZE, 0, 1);
    e.op(OP_NIP, 2, 1);
    e.int(bj::SHARE_BASE as i64);
    e.op(OP_SUB, 2, 1);
    e.name()
}

/// `v` in 0..=12 on the stack.
fn in_range(e: &mut E, v: Slot) {
    e.get(v);
    e.int(0);
    e.int(13);
    e.op(OP_WITHIN, 3, 1);
}

/// `bj_share_k`: the mover revealed position `k` here and its string opens
/// out of range. Witness: the string, below the pair reveal.
fn share(l: &Layout, key: &WotsPublic, c: &Commitments, k: usize) -> PosLeaf {
    let pl = player(l);
    let mut e = E::new(key, l, 1);
    let f = load(&mut e);
    let v = open(&mut e, 0, c.of(pl, k));
    e.get(f.nlo);
    e.int(k as i64);
    e.op(OP_LESSTHANOREQUAL, 2, 1);
    e.int(k as i64);
    e.get(f.nhi);
    e.op(OP_LESSTHAN, 2, 1);
    e.and();
    in_range(&mut e, v);
    e.not();
    e.and();
    PosLeaf {
        name: format!("bj_share_{k}"),
        script: e.finish(),
        // the native mirror of a leaf with a witness string: the tests
        // supply the value through `share_fires` directly
        fires: Arc::new(|_, _| false),
    }
}

/// `bj_card_k` (house depths): a card dealt here is not the sum of its
/// shares mod 13. Witness: the player's string (deepest), then the
/// house's, below the pair reveal. Out-of-range shares make it fail.
fn card(l: &Layout, key: &WotsPublic, c: &Commitments, k: usize) -> PosLeaf {
    let mut e = E::new(key, l, 2);
    let f = load(&mut e);
    let va = open(&mut e, 0, &c.player[k]);
    let vb = open(&mut e, 1, &c.house[k]);
    in_range(&mut e, va);
    e.op(OP_VERIFY, 1, 0);
    in_range(&mut e, vb);
    e.op(OP_VERIFY, 1, 0);
    // (va + vb) mod 13
    e.get(va);
    e.get(vb);
    e.op(OP_ADD, 2, 1);
    e.op(OP_DUP, 0, 1);
    e.int(13);
    e.op(OP_GREATERTHANOREQUAL, 2, 1);
    e.if_();
    e.int(13);
    e.op(OP_SUB, 2, 1);
    e.endif();
    let cv = e.name();
    // dealt here?
    if k == HOLE {
        e.get(f.pph);
        e.eq(i64::from(phase::STOOD));
    } else {
        e.get(f.pnp);
        e.int(k as i64);
        e.op(OP_LESSTHANOREQUAL, 2, 1);
        e.int(k as i64);
        e.get(f.nnp);
        e.op(OP_LESSTHAN, 2, 1);
        e.and();
    }
    e.nd(digit::CARDS + k);
    e.get(cv);
    e.op(OP_NUMNOTEQUAL, 2, 1);
    e.and();
    PosLeaf { name: format!("bj_card_{k}"), script: e.finish(), fires: Arc::new(|_, _| false) }
}

/// The disprove family at this layout (D57).
pub fn disprove_leaves(l: &Layout, key: &WotsPublic, c: &Commitments) -> Vec<PosLeaf> {
    let mut v = vec![ttt::wrong_slot(l, key), malformed(l, key), transition(l, key), counters(l, key), cards_kept(l, key), status_leaf(l, key)];
    if !player(l) {
        v.push(dealer(l, key));
    }
    for k in 0..K {
        v.push(share(l, key, c, k));
    }
    if !player(l) {
        for k in 0..K {
            v.push(card(l, key, c, k));
        }
    }
    v
}

/// The witness strings a share or card leaf takes, bottom first, ahead of
/// the pair reveal.
pub fn leaf_wits(strings: &[&[u8]]) -> Vec<Vec<u8>> {
    strings.iter().map(|s| s.to_vec()).collect()
}

// ----- the authorship fragment (D41; D43 tied-WOTS) -----

/// The signed region's positions: head bytes 4..48 = digits 8..96.
pub fn authorship_positions(head_off: usize) -> Vec<usize> {
    (0..88).map(|j| head_off + 8 + j).collect()
}

/// The off-chain side: the state key signs head bytes 4..48.
pub fn auth_message(head: &[u8; HEAD_BYTES]) -> Vec<u8> {
    head[bj::SIGNED_FROM..].to_vec()
}

pub fn authorship_fragment(b: Builder, file: usize, head_off: usize, key: &WotsPublic) -> Builder {
    assert_eq!(key.params.message_digits as usize, 88, "a blackjack state key covers 44 bytes");
    b.wots_verify_tied(key, file, &authorship_positions(head_off))
}

// ----- the checked split (ungated, D57) -----

/// R(parked new state): the status when set (player 0, house 1, push 2),
/// else the mover of the parked depth wins. Verify it equals `code`.
pub fn resolution_fragment(mut b: Builder, l: &Layout, code: u8) -> Builder {
    let d = l.file - 1 - (l.new + digit::STATUS);
    let mover_code = if player(l) { 0 } else { 1 };
    b = b.push_int(d as i64).push_opcode(OP_PICK); // [st]
    b = b
        .push_opcode(OP_DUP)
        .push_opcode(OP_0NOTEQUAL)
        .push_opcode(OP_IF)
        .push_opcode(OP_1SUB)
        .push_opcode(OP_ELSE)
        .push_opcode(OP_DROP)
        .push_int(mover_code)
        .push_opcode(OP_ENDIF)
        .push_int(i64::from(code))
        .push_opcode(OP_NUMEQUALVERIFY);
    b
}

/// The blackjack checked split of the rebuttal output: after `delta +
/// delta'`, 2-of-2 (pre-signed) and R proven in-leaf. No outcome-code
/// gate: a losing house could otherwise lock the pot by never revealing
/// its code (D57). `_code` is unused (kept for the dispatch's shape).
pub fn checked_split_leaf(ctx: &CommitCtx, l: &Layout, o: &lngap_contract::Outcome, csv: u16, _code: &PublicKey, key: &WotsPublic) -> Leaf {
    let mut b = Builder::new().csv(csv);
    b = ctx.two_of_two_verify(b);
    b = b.wots_verify(key);
    b = resolution_fragment(b, l, o.code);
    for _ in 0..l.file / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    Leaf::new(format!("split_{}", o.name), b.push_int(1).into_script(), Timelock::csv(csv))
}

/// The ungated checked split's witness, wire order: the pair reveal, the
/// hub signature, the user signature (consumed first).
pub fn checked_split_witness(sig_user: Vec<u8>, sig_hub: Vec<u8>, pair: &lngap_lamport::winternitz::WotsSig) -> Vec<Vec<u8>> {
    let mut w = crate::rebut::wots_wire(pair);
    w.push(sig_hub);
    w.push(sig_user);
    w
}

/// The venue's registered check for a blackjack entry (D55 + D57): the
/// mover's state-key signature over head bytes 4..48, and for every
/// position the head declares revealed, a string in the body that opens
/// the mover's commitment to a value in 0..=12. Entry layout: the head,
/// the signature's hash elements, then the share strings (length-prefixed).
pub fn entry_ok(pk: &WotsPublic, c: &Commitments, depth: u32, entry: &[u8]) -> bool {
    let n_sig = pk.params.total_digits() as usize * 20;
    if entry.len() < HEAD_BYTES + n_sig {
        return false;
    }
    let head: [u8; HEAD_BYTES] = entry[..HEAD_BYTES].try_into().expect("48 bytes");
    let sigs: Vec<[u8; 20]> = entry[HEAD_BYTES..HEAD_BYTES + n_sig].chunks(20).map(|x| x.try_into().expect("20")).collect();
    if !crate::rebut::check_entry_sig(pk, &auth_message(&head), &sigs) {
        return false;
    }
    let s = State::from_head(&head);
    if s.lo > s.hi || s.hi as usize > K {
        return false;
    }
    let Some(strings) = bj::decode_shares(&entry[HEAD_BYTES + n_sig..]) else { return false };
    let pl = depth % 2 == 1;
    strings.len() == (s.hi - s.lo) as usize && bj::revealed(&s).zip(strings.iter()).all(|(k, st)| bj::opens(c.of(pl, k), st).is_some())
}

/// Build an entry: the head, the signature's hash elements, the strings.
pub fn entry(head: &[u8; HEAD_BYTES], sig: &lngap_lamport::winternitz::WotsSig, strings: &[&[u8]]) -> Vec<u8> {
    let mut e = head.to_vec();
    for h in &sig.hashes {
        e.extend_from_slice(h);
    }
    e.extend(bj::encode_shares(strings));
    e
}

/// The constant head(0): the initial state at depth 0 (the hub's parity).
pub fn initial_head(game_id: u16) -> [u8; HEAD_BYTES] {
    State::initial().head(game_id, 0, 1)
}

