//! Blackjack's native rules for the PoS venue (D57).
//!
//! This crate is the SPEC: the head layout, the honest transitions, and the
//! native mirror of every disprove predicate. `lngap-pos`'s blackjack
//! module builds the Script leaves and tests them against these mirrors.
//!
//! The game: one hand, the player (user, odd depths) against the house
//! (hub, even depths). An infinite deck: card `k` has rank
//! `(a_k + b_k) mod 13` (0 = ace, 1..=8 = two..nine, 9..=12 = ten-valued),
//! where `a_k` is the player's share and `b_k` the house's, each committed
//! at open as `SHA256(s)` with `|s| = 32 + value` and opened in Script by
//! OP_SIZE. 1:1 payouts, pushes refund; no naturals, doubling, splitting or
//! insurance; the dealer stands on all 17s.
//!
//! Card positions (K = 16): 0 and 1 the player's first two cards, 2 the
//! dealer's up-card, 15 the hole card; from 3 the player's hits, then the
//! dealer's draws from the stand position `ds`. The player may hit while
//! `np <= 10`; the dealer draws at most up to position 14.
//!
//! | mover | action | from phase | reveals (positions) |
//! |---|---|---|---|
//! | player | DEAL | START | 0, 1, 2 |
//! | house | REVEAL | DEALT | 0, 1, 2 (the cards are dealt) |
//! | player | HIT | DECIDE | np |
//! | house | REVEAL | HIT | np (the card; a bust ends the hand) |
//! | player | STAND | DECIDE | np..16 (all draws and the hole) |
//! | house | REVEAL | STOOD | np..16 (the whole dealer phase) |
//! | player | ACK | DONE (player won or push) | none |
//!
//! The head (48 bytes, nibble `j` = digit `j`, high nibble first): 0-7
//! word0 (game id, depth, mover); 8 action; 9 phase; 10 status; 11 zero;
//! 12-13 `np`; 14-15 `ds`; 16-17 `lo`; 18-19 `hi` (the positions whose
//! share the mover reveals in this entry, `lo..hi`); 20-35 the sixteen
//! card ranks; 36-95 zero.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Card positions.
pub const K: usize = 16;
/// The dealer's up-card.
pub const UP: usize = 2;
/// The hole card.
pub const HOLE: usize = 15;
/// The first hit position.
pub const FIRST_HIT: usize = 3;
/// The player may hit while `np <= MAX_HIT_NP`.
pub const MAX_HIT_NP: u8 = 10;
/// The dealer's draws stop before the hole: `np <= DRAW_LIMIT`.
pub const DRAW_LIMIT: u8 = 15;
/// Bytes of randomness a share of value 0 still carries.
pub const SHARE_BASE: usize = 32;
/// Head bytes.
pub const HEAD_BYTES: usize = 48;
/// The state key signs head bytes 4..48.
pub const SIGNED_FROM: usize = 4;
/// Head digit offsets.
pub mod digit {
    pub const ACTION: usize = 8;
    pub const PHASE: usize = 9;
    pub const STATUS: usize = 10;
    pub const PAD11: usize = 11;
    pub const NP: usize = 12;
    pub const DS: usize = 14;
    pub const LO: usize = 16;
    pub const HI: usize = 18;
    pub const CARDS: usize = 20;
    pub const PAD_FROM: usize = 36;
    pub const HEAD: usize = 96;
}

pub mod action {
    pub const NONE: u8 = 0;
    pub const DEAL: u8 = 1;
    pub const REVEAL: u8 = 2;
    pub const HIT: u8 = 3;
    pub const STAND: u8 = 4;
    pub const ACK: u8 = 5;
    pub const MAX: u8 = 5;
}

pub mod phase {
    pub const START: u8 = 0;
    pub const DEALT: u8 = 1;
    pub const DECIDE: u8 = 2;
    pub const HIT: u8 = 3;
    pub const STOOD: u8 = 4;
    pub const DONE: u8 = 5;
    pub const CLOSED: u8 = 6;
    pub const MAX: u8 = 6;
}

pub mod status {
    pub const OPEN: u8 = 0;
    pub const PLAYER: u8 = 1;
    pub const HOUSE: u8 = 2;
    pub const PUSH: u8 = 3;
    pub const MAX: u8 = 3;
}

/// The state a head carries, raw (a decoded head need not be well formed;
/// [`head_malformed`] judges that).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct State {
    pub action: u8,
    pub phase: u8,
    pub status: u8,
    pub np: u8,
    pub ds: u8,
    pub lo: u8,
    pub hi: u8,
    pub cards: [u8; K],
}

/// word0 as the venue packs it: game id, depth, mover (0 user, 1 hub).
pub fn word0(game_id: u16, depth: u32, mover: u8) -> u32 {
    (u32::from(game_id) << 16) | ((depth & 0xff) << 8) | u32::from(mover)
}

impl State {
    /// The state before the deal (the constant head(0)'s).
    pub fn initial() -> State {
        State::default()
    }

    /// The head for this state at `depth` (mover 0 = player, 1 = house).
    pub fn head(&self, game_id: u16, depth: u32, mover: u8) -> [u8; HEAD_BYTES] {
        let mut d = [0u8; 2 * HEAD_BYTES];
        let w = word0(game_id, depth, mover);
        for (i, x) in d.iter_mut().take(8).enumerate() {
            *x = ((w >> (4 * (7 - i))) & 15) as u8;
        }
        d[digit::ACTION] = self.action & 15;
        d[digit::PHASE] = self.phase & 15;
        d[digit::STATUS] = self.status & 15;
        for (off, v) in [(digit::NP, self.np), (digit::DS, self.ds), (digit::LO, self.lo), (digit::HI, self.hi)] {
            d[off] = v >> 4;
            d[off + 1] = v & 15;
        }
        for k in 0..K {
            d[digit::CARDS + k] = self.cards[k] & 15;
        }
        let mut h = [0u8; HEAD_BYTES];
        for (i, b) in h.iter_mut().enumerate() {
            *b = (d[2 * i] << 4) | d[2 * i + 1];
        }
        h
    }

    /// Decode a head's state fields (raw).
    pub fn from_head(h: &[u8; HEAD_BYTES]) -> State {
        let d = digits(h);
        let byte = |o: usize| (d[o] << 4) | d[o + 1];
        let mut cards = [0u8; K];
        for (k, c) in cards.iter_mut().enumerate() {
            *c = d[digit::CARDS + k];
        }
        State {
            action: d[digit::ACTION],
            phase: d[digit::PHASE],
            status: d[digit::STATUS],
            np: byte(digit::NP),
            ds: byte(digit::DS),
            lo: byte(digit::LO),
            hi: byte(digit::HI),
            cards,
        }
    }

    /// Is position `k` dealt in this state?
    pub fn dealt(&self, k: usize) -> bool {
        (k as u32) < u32::from(self.np) || (k == HOLE && self.ds > 0 && self.phase >= phase::DONE)
    }

    /// The player's positions: 0, 1 and the hits `3..lim`, `lim` the stand
    /// position once the player has stood, else `np`.
    pub fn player_positions(&self) -> Vec<usize> {
        let lim = if self.ds > 0 { self.ds } else { self.np } as usize;
        let mut v = vec![0, 1];
        v.extend(FIRST_HIT..lim.max(FIRST_HIT));
        v
    }

    /// The dealer's positions after the dealer phase: up, hole, draws.
    pub fn dealer_positions(&self) -> Vec<usize> {
        let mut v = vec![UP, HOLE];
        v.extend(self.ds as usize..(self.np as usize).max(self.ds as usize));
        v
    }

    pub fn player_total(&self) -> u32 {
        best_total(self.player_positions().iter().map(|&k| self.cards[k]))
    }

    pub fn dealer_total(&self) -> u32 {
        best_total(self.dealer_positions().iter().map(|&k| self.cards[k]))
    }

    pub fn is_terminal(&self) -> bool {
        self.status != status::OPEN
    }
}

/// The head's 96 digits, high nibble first.
pub fn digits(h: &[u8; HEAD_BYTES]) -> [u8; 2 * HEAD_BYTES] {
    let mut d = [0u8; 2 * HEAD_BYTES];
    for (i, b) in h.iter().enumerate() {
        d[2 * i] = b >> 4;
        d[2 * i + 1] = b & 15;
    }
    d
}

/// A rank's value: ace 1, two..nine face, ten-valued 10: `min(r + 1, 10)`.
pub fn value(rank: u8) -> u32 {
    (u32::from(rank) + 1).min(10)
}

/// A hand's best total: the sum, plus 10 for an ace if that stays <= 21.
pub fn best_total(ranks: impl Iterator<Item = u8>) -> u32 {
    let (mut sum, mut ace) = (0u32, false);
    for r in ranks {
        sum += value(r);
        ace |= r == 0;
    }
    if ace && sum + 10 <= 21 {
        sum + 10
    } else {
        sum
    }
}

/// The card two share values make.
pub fn card(a: u8, b: u8) -> u8 {
    (a + b) % 13
}

/// A rank's name.
pub fn rank_name(r: u8) -> &'static str {
    ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"].get(r as usize).copied().unwrap_or("?")
}

/// The outcome code (the contract's: user wins 0, hub wins 1, draw 2) of a
/// terminal status.
pub fn outcome_code(st: u8) -> Option<u8> {
    match st {
        status::PLAYER => Some(0),
        status::HOUSE => Some(1),
        status::PUSH => Some(2),
        _ => None,
    }
}

/// R(state) at a parked depth whose mover was `mover` (0 user, 1 hub): the
/// terminal result, else the side to move forfeits (the mover wins).
pub fn resolution(s: &State, mover: u8) -> u8 {
    outcome_code(s.status).unwrap_or(mover)
}

// ----- honest play -----

/// DEAL (the player, from START): reveals positions 0..3.
pub fn deal(p: &State) -> State {
    State { action: action::DEAL, phase: phase::DEALT, status: status::OPEN, np: 0, ds: 0, lo: 0, hi: 3, cards: p.cards }
}

/// Can the player hit?
pub fn can_hit(p: &State) -> bool {
    p.phase == phase::DECIDE && p.np <= MAX_HIT_NP
}

/// HIT (the player, from DECIDE): reveals position `np`.
pub fn hit(p: &State) -> State {
    State { action: action::HIT, phase: phase::HIT, lo: p.np, hi: p.np + 1, ..*p }
}

/// STAND (the player, from DECIDE): reveals `np..16`.
pub fn stand(p: &State) -> State {
    State { action: action::STAND, phase: phase::STOOD, ds: p.np, lo: p.np, hi: K as u8, ..*p }
}

/// ACK (the player, after a terminal state it won or pushed).
pub fn ack(p: &State) -> State {
    State { action: action::ACK, phase: phase::CLOSED, lo: 0, hi: 0, ..*p }
}

/// May the player ACK?
pub fn can_ack(p: &State) -> bool {
    p.phase == phase::DONE && (p.status == status::PLAYER || p.status == status::PUSH)
}

/// The house's REVEAL: `card_of(k)` is card `k` from both shares. From
/// DEALT: cards 0..3. From HIT: card `np` (a bust ends the hand). From
/// STOOD: the hole, then draws until the dealer's total reaches 17 or the
/// positions run out; the showdown.
pub fn house_reveal(p: &State, card_of: impl Fn(usize) -> u8) -> Option<State> {
    let mut n = State { action: action::REVEAL, ..*p };
    match p.phase {
        phase::DEALT => {
            for k in 0..3 {
                n.cards[k] = card_of(k);
            }
            n.np = 3;
            n.lo = 0;
            n.hi = 3;
            n.phase = phase::DECIDE;
            n.status = status::OPEN;
        }
        phase::HIT => {
            let k = p.np as usize;
            n.cards[k] = card_of(k);
            n.np = p.np + 1;
            n.lo = p.np;
            n.hi = p.np + 1;
            n.status = if n.player_total() > 21 { status::HOUSE } else { status::OPEN };
            n.phase = if n.status != status::OPEN { phase::DONE } else { phase::DECIDE };
        }
        phase::STOOD => {
            n.cards[HOLE] = card_of(HOLE);
            n.phase = phase::DONE;
            n.lo = p.np;
            n.hi = K as u8;
            while n.dealer_total() < 17 && n.np < DRAW_LIMIT {
                let k = n.np as usize;
                n.cards[k] = card_of(k);
                n.np += 1;
            }
            n.status = showdown(&n);
        }
        _ => return None,
    }
    Some(n)
}

/// The showdown's status.
pub fn showdown(n: &State) -> u8 {
    let (pt, dt) = (n.player_total(), n.dealer_total());
    if dt > 21 || pt > dt {
        status::PLAYER
    } else if pt < dt {
        status::HOUSE
    } else {
        status::PUSH
    }
}

/// The positions whose share the mover of `n` reveals.
pub fn revealed(n: &State) -> std::ops::Range<usize> {
    n.lo as usize..n.hi as usize
}

// ----- the disprove predicates' native mirrors (D57) -----
//
// Each takes the parked prior and new states (and, for the card and share
// predicates, the share values the witness strings open to) and says
// whether the leaf FIRES. `player` is whether the parked depth's mover is
// the player (odd depths). None fires on an honest transition.

/// The head is not a well-formed encoding.
pub fn head_malformed(h: &[u8; HEAD_BYTES]) -> bool {
    let d = digits(h);
    let s = State::from_head(h);
    s.action > action::MAX
        || s.phase > phase::MAX
        || s.status > status::MAX
        || d[digit::PAD11] != 0
        || s.np > 16
        || s.ds > 16
        || s.lo > 16
        || s.hi > 16
        || s.cards.iter().any(|&c| c > 12)
        || d[digit::PAD_FROM..].iter().any(|&x| x != 0)
}

/// The action is not allowed in the prior phase for this mover, or the new
/// phase is not the one it leads to.
pub fn transition_fires(p: &State, n: &State, player: bool) -> bool {
    use phase::*;
    let a = n.action;
    let expect = if player {
        match (p.phase, a) {
            (START, action::DEAL) => Some(DEALT),
            (DECIDE, action::HIT) if p.np <= MAX_HIT_NP => Some(HIT),
            (DECIDE, action::STAND) => Some(STOOD),
            (DONE, action::ACK) if p.status == status::PLAYER || p.status == status::PUSH => Some(CLOSED),
            _ => None,
        }
    } else {
        match (p.phase, a) {
            (DEALT, action::REVEAL) => Some(DECIDE),
            (HIT, action::REVEAL) => Some(if n.status != status::OPEN { DONE } else { DECIDE }),
            (STOOD, action::REVEAL) => Some(DONE),
            _ => None,
        }
    };
    expect != Some(n.phase)
}

/// `np`, `ds`, `lo`, `hi` are not what the action requires (combinations
/// the transition predicate rejects are not judged here).
pub fn counters_fires(p: &State, n: &State) -> bool {
    // in u16, as Script computes (a malformed prior's np + 1 does not wrap)
    let (pnp, pds) = (u16::from(p.np), u16::from(p.ds));
    let want: Option<(Option<u16>, u16, u16, u16)> = match (n.action, p.phase) {
        (action::DEAL, _) => Some((Some(0), 0, 0, 3)),
        (action::REVEAL, phase::DEALT) => Some((Some(3), 0, 0, 3)),
        (action::HIT, _) => Some((Some(pnp), pds, pnp, pnp + 1)),
        (action::REVEAL, phase::HIT) => Some((Some(pnp + 1), pds, pnp, pnp + 1)),
        (action::STAND, _) => Some((Some(pnp), pnp, pnp, K as u16)),
        (action::REVEAL, phase::STOOD) => Some((None, pds, pnp, K as u16)),
        (action::ACK, _) => Some((Some(pnp), pds, 0, 0)),
        _ => None,
    };
    match want {
        Some((np, ds, lo, hi)) => np.is_some_and(|x| x != u16::from(n.np)) || u16::from(n.ds) != ds || u16::from(n.lo) != lo || u16::from(n.hi) != hi,
        None => false,
    }
}

/// A dealt card changed, or an undealt position is not zero.
pub fn cards_kept_fires(p: &State, n: &State) -> bool {
    (0..K).any(|k| (p.dealt(k) && n.cards[k] != p.cards[k]) || (!n.dealt(k) && n.cards[k] != 0))
}

/// The status is not the one the transition produces.
pub fn status_fires(p: &State, n: &State) -> bool {
    let want = match (n.action, p.phase) {
        (action::DEAL, _) | (action::HIT, _) | (action::STAND, _) => Some(status::OPEN),
        (action::REVEAL, phase::DEALT) => Some(status::OPEN),
        (action::REVEAL, phase::HIT) => Some(if n.player_total() > 21 { status::HOUSE } else { status::OPEN }),
        (action::REVEAL, phase::STOOD) => Some(showdown(n)),
        (action::ACK, _) => Some(p.status),
        _ => None,
    };
    want.is_some_and(|w| w != n.status)
}

/// The dealer phase broke the drawing rule (only for the REVEAL from
/// STOOD): fewer positions than the prior's, past the limit, stopped below
/// 17 with positions left, or drew at 17 or more.
pub fn dealer_fires(p: &State, n: &State) -> bool {
    if !(n.action == action::REVEAL && p.phase == phase::STOOD) {
        return false;
    }
    if n.np < p.np || n.np > DRAW_LIMIT || n.np < n.ds {
        return true;
    }
    let total = n.dealer_total();
    let stopped_early = total < 17 && n.np < DRAW_LIMIT;
    let drew_late = n.np > n.ds && {
        let mut before = *n;
        before.np -= 1;
        before.dealer_total() >= 17
    };
    stopped_early || drew_late
}

/// Is position `k` dealt at this (house) depth?
pub fn newly_dealt(p: &State, n: &State, k: usize) -> bool {
    if k == HOLE {
        p.phase == phase::STOOD
    } else {
        (k as u32) >= u32::from(p.np) && (k as u32) < u32::from(n.np)
    }
}

/// Card `k`, dealt at this depth, is not `(a + b) mod 13`. `a`, `b` are the
/// values the witness strings open to; out-of-range values make the leaf
/// fail (not fire): that is the share predicate's case.
pub fn card_fires(p: &State, n: &State, k: usize, a: i64, b: i64) -> bool {
    (0..=12).contains(&a) && (0..=12).contains(&b) && newly_dealt(p, n, k) && i64::from(n.cards[k]) != (a + b) % 13
}

/// The mover revealed position `k` in this entry and its string opens to a
/// value outside 0..=12.
pub fn share_fires(n: &State, k: usize, v: i64) -> bool {
    revealed(n).contains(&k) && !(0..=12).contains(&v)
}

// ----- shares -----

/// A share: its value and the string that commits to it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Share {
    pub value: u8,
    pub string: Vec<u8>,
}

impl Share {
    /// A share of `value` with a fresh random string.
    pub fn new(value: u8, rng: &mut impl rand::RngCore) -> Share {
        let mut s = vec![0u8; SHARE_BASE + value as usize];
        rng.fill_bytes(&mut s);
        Share { value, string: s }
    }
    /// A uniformly random share.
    pub fn random(rng: &mut impl rand::RngCore) -> Share {
        let v = loop {
            let x = (rng.next_u32() & 15) as u8;
            if x < 13 {
                break x;
            }
        };
        Share::new(v, rng)
    }
    pub fn commitment(&self) -> [u8; 32] {
        commit(&self.string)
    }
}

pub fn commit(s: &[u8]) -> [u8; 32] {
    Sha256::digest(s).into()
}

/// The value a string opens to: its length less the base (may be out of
/// range; the caller judges).
pub fn open(s: &[u8]) -> i64 {
    s.len() as i64 - SHARE_BASE as i64
}

/// Does `s` open `c` to a value in range?
pub fn opens(c: &[u8; 32], s: &[u8]) -> Option<u8> {
    let v = open(s);
    (commit(s) == *c && (0..=12).contains(&v)).then_some(v as u8)
}

/// Encode share strings for an entry body: each as a length byte and the
/// bytes.
pub fn encode_shares(strings: &[&[u8]]) -> Vec<u8> {
    let mut out = Vec::new();
    for s in strings {
        out.push(s.len() as u8);
        out.extend_from_slice(s);
    }
    out
}

/// Decode an entry body's share strings.
pub fn decode_shares(mut b: &[u8]) -> Option<Vec<Vec<u8>>> {
    let mut out = Vec::new();
    while let Some((&len, rest)) = b.split_first() {
        let len = len as usize;
        if rest.len() < len {
            return None;
        }
        out.push(rest[..len].to_vec());
        b = &rest[len..];
    }
    Some(out)
}

/// Each side's sixteen commitments, exchanged at open.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Commitments {
    pub player: [[u8; 32]; K],
    pub house: [[u8; 32]; K],
}

impl Commitments {
    /// The commitment of the mover `player` (true) or the house at `k`.
    pub fn of(&self, player: bool, k: usize) -> &[u8; 32] {
        if player {
            &self.player[k]
        } else {
            &self.house[k]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{RngCore, SeedableRng};

    /// Every predicate, on a transition: none may fire on an honest one.
    fn fires_any(p: &State, n: &State, player: bool, cards: &dyn Fn(usize) -> (u8, u8)) -> Vec<&'static str> {
        let mut v = vec![];
        if head_malformed(&n.head(1, 2, u8::from(!player))) {
            v.push("malformed");
        }
        if transition_fires(p, n, player) {
            v.push("transition");
        }
        if counters_fires(p, n) {
            v.push("counters");
        }
        if cards_kept_fires(p, n) {
            v.push("cards_kept");
        }
        if status_fires(p, n) {
            v.push("status");
        }
        if dealer_fires(p, n) {
            v.push("dealer");
        }
        for k in 0..K {
            let (a, b) = cards(k);
            if !player && card_fires(p, n, k, i64::from(a), i64::from(b)) {
                v.push("card");
            }
        }
        v
    }

    /// Play whole hands at random: every honest transition fires nothing,
    /// and the hands end in a terminal state.
    #[test]
    fn honest_hands_fire_nothing() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let mut outcomes = [0u32; 4];
        for _ in 0..3000 {
            let shares: Vec<(u8, u8)> = (0..K).map(|_| (Share::random(&mut rng).value, Share::random(&mut rng).value)).collect();
            let cards = |k: usize| shares[k];
            let card_of = |k: usize| card(shares[k].0, shares[k].1);
            let mut s = State::initial();
            let mut player = true;
            let mut steps = 0;
            loop {
                let n = if player {
                    if s.phase == phase::START {
                        deal(&s)
                    } else if s.phase == phase::DECIDE {
                        // a simple strategy with some randomness
                        if can_hit(&s) && (s.player_total() < 12 || (s.player_total() < 17 && rng.next_u32() % 2 == 0)) {
                            hit(&s)
                        } else {
                            stand(&s)
                        }
                    } else if can_ack(&s) {
                        ack(&s)
                    } else {
                        break;
                    }
                } else {
                    match house_reveal(&s, card_of) {
                        Some(n) => n,
                        None => break,
                    }
                };
                let f = fires_any(&s, &n, player, &cards);
                assert!(f.is_empty(), "honest transition fired {f:?}: {s:?} -> {n:?}");
                s = n;
                player = !player;
                steps += 1;
                assert!(steps < 40);
            }
            assert!(s.is_terminal(), "the hand ended open: {s:?}");
            outcomes[s.status as usize] += 1;
        }
        assert!(outcomes[1] > 0 && outcomes[2] > 0 && outcomes[3] > 0, "{outcomes:?}");
    }

    #[test]
    fn head_round_trip() {
        let mut s = State::initial();
        s.action = action::REVEAL;
        s.phase = phase::DECIDE;
        s.np = 3;
        s.cards[0] = 12;
        s.cards[1] = 0;
        s.cards[2] = 9;
        let h = s.head(7, 2, 1);
        assert_eq!(State::from_head(&h), s);
        assert!(!head_malformed(&h));
        assert_eq!(&h[0..4], &word0(7, 2, 1).to_be_bytes());
        let mut bad = h;
        bad[40] = 1;
        assert!(head_malformed(&bad));
    }

    #[test]
    fn totals() {
        assert_eq!(best_total([0, 12].into_iter()), 21);
        assert_eq!(best_total([0, 0].into_iter()), 12);
        assert_eq!(best_total([0, 5, 9].into_iter()), 17);
        assert_eq!(best_total([9, 9, 1].into_iter()), 22);
    }

    #[test]
    fn shares_open() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(1);
        let s = Share::new(9, &mut rng);
        assert_eq!(opens(&s.commitment(), &s.string), Some(9));
        let mut longer = s.string.clone();
        longer.push(0);
        assert_eq!(opens(&s.commitment(), &longer), None);
        let enc = encode_shares(&[&s.string, &[1, 2, 3]]);
        assert_eq!(decode_shares(&enc).unwrap(), vec![s.string.clone(), vec![1, 2, 3]]);
    }
}
