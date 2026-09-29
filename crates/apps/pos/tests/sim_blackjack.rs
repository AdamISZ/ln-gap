//! The blackjack disprove family through the script32 simulator (D57): each
//! leaf against its native mirror in `lngap-blackjack`.
//!
//! Safety: no leaf fires on an honest transition. Completeness: a new head
//! that differs from the honest successor (for the true shares) fires some
//! leaf. Agreement: script and mirror agree on every tuple, honest or not.

use lngap_blackjack as bj;
use lngap_blackjack::{Commitments, Share, State, K};
use lngap_channel::Role;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::blackjack;
use lngap_pos::refute::{self, pair_key, refute_key};
use lngap_pos::ttt::Layout;
use rand::{rngs::StdRng, Rng, RngCore, SeedableRng};

const GAME: u16 = 1;

struct Deck {
    a: Vec<Share>,
    b: Vec<Share>,
    c: Commitments,
}

impl Deck {
    fn new(rng: &mut StdRng) -> Deck {
        let a: Vec<Share> = (0..K).map(|_| Share::random(rng)).collect();
        let b: Vec<Share> = (0..K).map(|_| Share::random(rng)).collect();
        let c = Commitments {
            player: std::array::from_fn(|k| a[k].commitment()),
            house: std::array::from_fn(|k| b[k].commitment()),
        };
        Deck { a, b, c }
    }
    fn card(&self, k: usize) -> u8 {
        bj::card(self.a[k].value, self.b[k].value)
    }
}

fn mover_of(d: u32) -> Role {
    if d % 2 == 1 { Role::User } else { Role::Hub }
}

fn head(s: &State, d: u32) -> [u8; 48] {
    s.head(GAME, d, u8::from(mover_of(d) == Role::Hub))
}

/// The leaves that fired on the tuple (prior state at `d - 1`, new state
/// at `d`), asserting script == mirror for each.
fn fired(d: u32, p: &State, n_head: &[u8; 48], deck: &Deck) -> Vec<String> {
    let l = Layout::at(d, GAME, mover_of(d));
    let sk: WotsSecret = if d >= 2 { pair_key([d as u8; 32]) } else { refute_key([1; 32]) };
    let fam = blackjack::disprove_leaves(&l, &sk.public(), &deck.c);
    let p_head = if d >= 2 { head(p, d - 1) } else { blackjack::initial_head(GAME) };
    let msg = if d >= 2 { [p_head.as_slice(), n_head.as_slice()].concat() } else { n_head.to_vec() };
    let reveal = refute::disprove_witness(&sk.sign(&msg).unwrap());
    let n = State::from_head(n_head);
    let pl = mover_of(d) == Role::User;
    let mut out = vec![];
    for leaf in &fam {
        let (wits, native): (Vec<Vec<u8>>, bool) = if let Some(k) = leaf.name.strip_prefix("bj_share_") {
            let k: usize = k.parse().unwrap();
            let s = if pl { &deck.a[k] } else { &deck.b[k] };
            (vec![s.string.clone()], bj::share_fires(&n, k, bj::open(&s.string)))
        } else if let Some(k) = leaf.name.strip_prefix("bj_card_") {
            let k: usize = k.parse().unwrap();
            let (a, b) = (&deck.a[k], &deck.b[k]);
            let prior = if d >= 2 { *p } else { State::initial() };
            (vec![a.string.clone(), b.string.clone()], bj::card_fires(&prior, &n, k, bj::open(&a.string), bj::open(&b.string)))
        } else {
            (vec![], (leaf.fires)(&p_head, n_head))
        };
        let mut w = wits;
        w.extend(reveal.clone());
        let ran = match lngap_script32::sim::run(leaf.script.as_script(), w) {
            // a spend needs exactly one element left, and it true
            Ok(st) => {
                assert_eq!(st.len(), 1, "depth {d}: leaf {} left {} elements", leaf.name, st.len());
                truthy(&st[0])
            }
            Err(_) => false,
        };
        assert_eq!(ran, native, "depth {d}: leaf {} disagrees with its mirror on {p:?} -> {n:?}", leaf.name);
        if ran {
            out.push(leaf.name.clone());
        }
    }
    out
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

/// The honest successor of `p` for the mover at `d`.
fn honest(p: &State, d: u32, deck: &Deck, rng: &mut StdRng) -> Option<State> {
    if mover_of(d) == Role::User {
        match p.phase {
            bj::phase::START => Some(bj::deal(p)),
            bj::phase::DECIDE => Some(if bj::can_hit(p) && (p.player_total() < 12 || (p.player_total() < 17 && rng.gen_bool(0.5))) { bj::hit(p) } else { bj::stand(p) }),
            _ if bj::can_ack(p) => Some(bj::ack(p)),
            _ => None,
        }
    } else {
        bj::house_reveal(p, |k| deck.card(k))
    }
}

/// Play a hand; return the (depth, prior, new) transitions.
fn hand(deck: &Deck, rng: &mut StdRng) -> Vec<(u32, State, State)> {
    let mut s = State::initial();
    let mut out = vec![];
    for d in 1.. {
        let Some(n) = honest(&s, d, deck, rng) else { break };
        out.push((d, s, n));
        s = n;
    }
    out
}

#[test]
fn honest_transitions_fire_nothing() {
    let mut rng = StdRng::seed_from_u64(11);
    let mut seen = std::collections::BTreeSet::new();
    for _ in 0..12 {
        let deck = Deck::new(&mut rng);
        for (d, p, n) in hand(&deck, &mut rng) {
            let f = fired(d, &p, &head(&n, d), &deck);
            assert!(f.is_empty(), "honest transition at depth {d} fired {f:?}: {p:?} -> {n:?}");
            seen.insert((n.action, p.phase));
        }
    }
    // the hands covered every kind of move
    for want in [(bj::action::DEAL, bj::phase::START), (bj::action::REVEAL, bj::phase::DEALT), (bj::action::HIT, bj::phase::DECIDE), (bj::action::REVEAL, bj::phase::HIT), (bj::action::STAND, bj::phase::DECIDE), (bj::action::REVEAL, bj::phase::STOOD)] {
        assert!(seen.contains(&want), "no honest {want:?} in the sample: {seen:?}");
    }
}

/// Mutate one field of the head (or a raw nibble).
fn mutate(n: &State, d: u32, rng: &mut StdRng) -> [u8; 48] {
    let mut s = *n;
    match rng.gen_range(0..9) {
        0 => s.action = rng.gen_range(0..7),
        1 => s.phase = rng.gen_range(0..8),
        2 => s.status = rng.gen_range(0..5),
        3 => s.np = s.np.wrapping_add(rng.gen_range(1..3)),
        4 => s.ds = rng.gen_range(0..17),
        5 => s.lo = rng.gen_range(0..17),
        6 => s.hi = rng.gen_range(0..18),
        7 => {
            let k = rng.gen_range(0..K);
            s.cards[k] = rng.gen_range(0..14);
        }
        _ => {
            // a raw nibble anywhere past word0
            let mut h = head(&s, d);
            let j = rng.gen_range(8..96);
            let byte = &mut h[j / 2];
            let v = (rng.next_u32() & 15) as u8;
            *byte = if j % 2 == 0 { (*byte & 0x0f) | (v << 4) } else { (*byte & 0xf0) | v };
            return h;
        }
    }
    head(&s, d)
}

#[test]
fn wrong_heads_are_caught_and_agree() {
    let mut rng = StdRng::seed_from_u64(12);
    let mut caught = 0;
    for _ in 0..10 {
        let deck = Deck::new(&mut rng);
        for (d, p, n) in hand(&deck, &mut rng) {
            let honest_head = head(&n, d);
            for _ in 0..4 {
                let h = mutate(&n, d, &mut rng);
                if h == honest_head {
                    continue;
                }
                let f = fired(d, &p, &h, &deck);
                // the dealer's np is the one free field: a different np with
                // the same everything else is judged by bj_dealer
                assert!(!f.is_empty(), "depth {d}: a wrong head fired nothing: {p:?} -> {:?}", State::from_head(&h));
                caught += 1;
            }
        }
    }
    assert!(caught > 100, "{caught}");
}

/// A share opening out of range, and a wrong card, fire their leaves.
#[test]
fn bad_shares_and_cards_fire() {
    let mut rng = StdRng::seed_from_u64(13);
    let mut deck = Deck::new(&mut rng);
    // the player's position-1 share opens to 14: committed, but out of range
    deck.a[1] = Share::new(14, &mut rng);
    deck.c.player[1] = deck.a[1].commitment();
    let p = State::initial();
    let n = bj::deal(&p);
    let f = fired(1, &p, &head(&n, 1), &deck);
    assert_eq!(f, vec!["bj_share_1".to_string()], "{f:?}");
    // the house deals card 2 wrongly
    let deck = Deck::new(&mut rng);
    let p = bj::deal(&State::initial());
    let mut n = bj::house_reveal(&p, |k| deck.card(k)).unwrap();
    n.cards[2] = (n.cards[2] + 1) % 13;
    let f = fired(2, &p, &head(&n, 2), &deck);
    assert!(f.contains(&"bj_card_2".to_string()), "{f:?}");
}
