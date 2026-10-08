//! V25_POC_PLAN.md Phase 3 on regtest: a venue of three members whose seal
//! chains close at staggered heights (one closing per block, venue-wide)
//! date a move sent to all of them.
//!
//! - every member closing in the move's window after it was sent carries
//!   the move's leaf in the root it puts on chain, and its path verifies
//!   against that on-chain root; a member that closed before the move was
//!   sent does not have it;
//! - faults: a withholding member gives no path; an equivocating member's
//!   second root is a pair under the same key; a censoring member's root
//!   lacks the move; a skipping member's chain ends (its closing is
//!   absent, its bond burnable), the others carry on.
//!
//! Run with `--test-threads=1` or 2: each test starts its own node.

use bitcoin::{Amount, Transaction};
use lngap_btc::regtest::Regtest;
use lngap_seal::dating::{Choice, ChoiceKey, SignedChoice};
use lngap_seal::world::{root_of_closing, Venue, VenueMember};
use lngap_seal::{ceremony, first_tree, Member, SealSpec};

const N: usize = 3;

fn spec(start: u32) -> SealSpec {
    SealSpec {
        value: Amount::from_sat(300_000),
        start,
        period: N as u32,
        periods: 4,
        grace: 2,
        release_delay: 5,
        fanout_depth: 2,
        leaf_value: Amount::from_sat(330),
        split_fee: Amount::from_sat(400),
        anchor_value: Amount::from_sat(240),
        closing_fee: Amount::from_sat(3_000),
    }
}

/// Three members; member i closes at base + i, base + i + 3, ...
fn venue(rt: &Regtest) -> (Venue, u32) {
    let base = rt.height().unwrap() + 8;
    let mut members = Vec::new();
    for i in 0..N {
        let s = spec(base + i as u32);
        let m = Member::new([0x40 + i as u8; 32], &s);
        let ceremony_seed = [0xC0 + i as u8; 32];
        let tree = first_tree(&s, &m.public(), &ceremony_seed).unwrap();
        let (op, _) = rt.fund(&tree.script_pubkey(), s.value).unwrap();
        let chain = ceremony(&s, &m.public(), op, &ceremony_seed).unwrap();
        members.push(VenueMember::new(i, m, chain));
    }
    (Venue::new(members), base)
}

/// Mine block by block up to `height`, with every due closing in its
/// block. Returns the closings mined: (member, period, tx).
fn run_to(rt: &Regtest, v: &mut Venue, height: u32) -> Vec<(usize, u32, Transaction)> {
    let mut mined = Vec::new();
    while rt.height().unwrap() < height {
        let tip = rt.height().unwrap();
        let due = v.closings_due(tip).unwrap();
        if due.is_empty() {
            rt.mine(1).unwrap();
            continue;
        }
        let txs: Vec<Transaction> = due.iter().map(|(_, t)| t.clone()).collect();
        let at = rt.mine_with(&txs).unwrap_or_else(|e| panic!("closings due at {} must mine: {e:#}", tip + 1));
        for (i, tx) in due {
            let k = (1..=4).find(|&k| v.members[i].closing_height(k) == at).unwrap();
            mined.push((i, k, tx));
        }
    }
    mined
}

fn signed(key: &ChoiceKey, contract: u32, depth: u16, value: u8) -> SignedChoice {
    SignedChoice { choice: Choice { contract, depth, value: vec![value] }, sig: key.sign(&[value]).unwrap() }
}

#[test]
fn members_date_a_move_in_its_window() {
    let rt = Regtest::start().unwrap();
    let (mut v, base) = venue(&rt);
    let key = ChoiceKey::new([0x11; 32], 1);
    v.register(1, 1, key.public());
    v.members[1].faults.withhold = true;
    v.members[2].faults.equivocate.insert(1);

    // closings before the move: member 0 closes period 1 at base
    rt.mine_to_height(base - 1).unwrap();
    let early = run_to(&rt, &mut v, base);
    assert_eq!(early.len(), 1);
    // the move is sent with the chain at `base`: members 1 and 2 (period 1)
    // and member 0 (period 2) close after it
    let sent = rt.height().unwrap();
    let mv = signed(&key, 1, 1, 7);
    v.submit(sent, &mv).unwrap();
    let deadline = sent + N as u32;
    let window = v.window(sent, deadline);
    assert_eq!(window, vec![(1, 1), (2, 1), (0, 2)]);
    let mined = run_to(&rt, &mut v, deadline);

    let leaf = mv.choice.leaf();
    for (i, k) in &window {
        let (_, _, tx) = mined.iter().find(|(j, kk, _)| j == i && kk == k).expect("every window member closed");
        let on_chain = root_of_closing(tx).expect("a closing with the move carries a root");
        let tree = &v.members[*i].sealed[k];
        assert_eq!(tree.root(), on_chain, "member {i}: the sealed tree is the root on chain");
        match v.members[*i].path(*k, leaf) {
            Some((path, root)) => assert_eq!((path.root_from(leaf), root), (on_chain, on_chain)),
            None => assert_eq!(*i, 1, "only the withholding member gives no path"),
        }
    }
    // member 0's period-1 closing came before the move: no leaf there
    let (i0, k0, tx0) = &early[0];
    assert_eq!((*i0, *k0), (0, 1));
    assert!(root_of_closing(tx0).is_none(), "an empty closing (nothing received yet)");

    // the equivocation: a second root for member 2's period 1, under the
    // same key: a slashable pair
    let (second, sig2) = v.members[2].second_root(1).unwrap().expect("member 2 equivocated");
    let first = v.members[2].sealed[&1].root();
    assert_ne!(second, first);
    let key2 = &v.members[2].chain.member.roots[0];
    assert_eq!(key2.verify(&sig2).unwrap(), second.to_vec());
    let sig1 = v.members[2].member.sign_root(1, &first).unwrap();
    assert_eq!(key2.verify(&sig1).unwrap(), first.to_vec());
    println!(
        "DATING window {:?}: tree depth {} (1 move), closings {:?} vB",
        window,
        v.members[0].sealed[&2].depth(),
        mined.iter().map(|(_, _, t)| t.vsize()).collect::<Vec<_>>()
    );
}

#[test]
fn censoring_and_skipping_members() {
    let rt = Regtest::start().unwrap();
    let (mut v, base) = venue(&rt);
    let key = ChoiceKey::new([0x12; 32], 1);
    v.register(2, 1, key.public());
    v.members[2].faults.censor.insert(2);
    v.members[0].faults.skip.insert(1);

    rt.mine_to_height(base - 2).unwrap();
    let sent = rt.height().unwrap();
    let mv = signed(&key, 2, 1, 9);
    let periods = v.submit(sent, &mv).unwrap();
    assert_eq!(periods, vec![Some(1), Some(1), None], "the censoring member refuses the move");
    let mined = run_to(&rt, &mut v, base + 2 * N as u32);

    // member 0 skipped period 1: no closing, and its chain ended
    assert!(mined.iter().all(|(i, _, _)| *i != 0), "a skipping member closes nothing after the skip");
    assert!(v.members[0].dead);
    // its bond is burnable after the grace
    let burn = v.members[0].chain.burn(1).unwrap();
    rt.mine_to_height(v.members[0].chain.spec.burn_from(1).max(rt.height().unwrap() + 1) - 1).unwrap();
    rt.send_raw_any_fee(&burn).unwrap();
    rt.mine(1).unwrap();
    // member 1 dated the move; member 2's root lacks it
    let leaf = mv.choice.leaf();
    assert!(v.members[1].path(1, leaf).is_some(), "the honest member dated the move");
    assert!(v.members[2].path(1, leaf).is_none(), "the censoring member's root lacks the move");
    // the others carried on into later periods
    assert!(mined.iter().any(|(i, k, _)| *i == 1 && *k == 2) && mined.iter().any(|(i, k, _)| *i == 2 && *k == 2));
}
