//! M1: fund a channel, do balance updates, close cooperatively; force-close
//! with delay; penalty on a revoked broadcast. All on regtest, with parties
//! reacting to blocks on their own.

use std::sync::Arc;

use bitcoin::Amount;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::protocol::{funding_tree, run_bus, ChannelParty, Closing};
use lngap_channel::{ChannelParams, ChannelState, PartyKeys, Role};

const FUNDING: Amount = Amount::from_sat(200_000);
const HALF: Amount = Amount::from_sat(100_000);
const CONTRIB: Amount = Amount::from_sat(100_500);

pub struct Pair {
    pub user: ChannelParty,
    pub hub: ChannelParty,
}

fn init_log() {
    let _ = tracing_subscriber::fmt().with_env_filter(
        tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()),
    ).with_test_writer().try_init();
}

/// Open a 100k/100k channel between fresh user and hub parties.
pub fn open_channel(rt: &Arc<Regtest>, label: &str) -> Pair {
    let params = ChannelParams::regtest(FUNDING);
    let user_keys = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("{label}/user")));
    let hub_keys = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("{label}/hub")));
    let pubs = [user_keys.public(), hub_keys.public()];

    // each party gets a coin at its payout script
    let (u_op, u_prev) = rt.fund(&pubs[0].payout_spk, CONTRIB).unwrap();
    let (h_op, h_prev) = rt.fund(&pubs[1].payout_spk, CONTRIB).unwrap();
    let ftree = funding_tree(&pubs);
    let mut ftx = build_funding_tx(&[(u_op, u_prev.clone()), (h_op, h_prev.clone())], ftree.script_pubkey(), FUNDING);
    let funding = (bitcoin::OutPoint { txid: ftx.compute_txid(), vout: 0 }, ftx.output[0].clone());

    let initial = ChannelState { seq: 0, balances: [HALF, HALF], contracts: vec![] };
    let accept_all: lngap_channel::protocol::Policy = Box::new(|_, _| Ok(()));
    let accept_all2: lngap_channel::protocol::Policy = Box::new(|_, _| Ok(()));
    let user_rev = [user_keys.revocation_hash(0), user_keys.revocation_hash(1)];
    let hub_rev = [hub_keys.revocation_hash(0), hub_keys.revocation_hash(1)];
    let chain: Arc<dyn lngap_channel::chain::Chain> = rt.clone();
    let mut user = ChannelParty::new(user_keys, pubs[1].clone(), params, funding.clone(), initial.clone(), hub_rev, chain.clone(), accept_all).unwrap();
    let mut hub = ChannelParty::new(hub_keys, pubs[0].clone(), params, funding, initial, user_rev, chain, accept_all2).unwrap();

    // exchange state-0 signatures, then sign and broadcast funding
    let m1 = user.initial_commit_sigs().unwrap();
    let m2 = hub.initial_commit_sigs().unwrap();
    run_bus(&mut user, &mut hub, vec![m1, m2]).unwrap();
    assert!(user.ready_to_fund() && hub.ready_to_fund());
    let prevouts = [u_prev, h_prev];
    sign_funding_input(&mut ftx, 0, &prevouts, &user.keys.payout_tree(), &user.keys.payout).unwrap();
    sign_funding_input(&mut ftx, 1, &prevouts, &hub.keys.payout_tree(), &hub.keys.payout).unwrap();
    rt.send_and_confirm(&ftx).unwrap();
    Pair { user, hub }
}

/// Move `amount` from `from` to the other side, proposer = `from`.
pub fn pay(p: &mut Pair, from: Role, amount: Amount) {
    let (a, b) = match from {
        Role::User => (&mut p.user, &mut p.hub),
        Role::Hub => (&mut p.hub, &mut p.user),
    };
    let mut st = a.current_state().clone();
    st.seq += 1;
    st.balances[from.idx()] -= amount;
    st.balances[from.other().idx()] += amount;
    let msgs = a.propose(st).unwrap();
    run_bus(a, b, msgs).unwrap();
    assert_eq!(a.current_seq(), b.current_seq());
    assert!(a.pending_seq().is_none() && b.pending_seq().is_none());
}

/// Mine `n` blocks one at a time, letting both parties see each block.
pub fn advance(rt: &Regtest, p: &mut Pair, n: u32) {
    for _ in 0..n {
        rt.mine(1).unwrap();
        let h = rt.height().unwrap();
        let txs = rt.block_txs(h).unwrap();
        p.user.on_block(h, &txs).unwrap();
        p.hub.on_block(h, &txs).unwrap();
    }
}

fn balances(rt: &Regtest, p: &Pair) -> (Amount, Amount) {
    (rt.balance_of(&p.user.my_payout_spk()).unwrap(), rt.balance_of(&p.hub.my_payout_spk()).unwrap())
}

#[test]
fn ten_updates_then_cooperative_close() {
    init_log();
    let rt = Arc::new(Regtest::start().unwrap());
    let mut p = open_channel(&rt, "coop");
    for i in 0..10u64 {
        let from = if i % 2 == 0 { Role::User } else { Role::Hub };
        pay(&mut p, from, Amount::from_sat(5_000 + i * 100));
    }
    assert_eq!(p.user.current_seq(), 10);
    let st = p.user.current_state().clone();
    // user paid 5000+5200+5400+5600+5800 = 27000; hub paid 5100+5300+5500+5700+5900 = 27500
    assert_eq!(st.balances[0], Amount::from_sat(100_500));
    assert_eq!(st.balances[1], Amount::from_sat(99_500));

    let msgs = p.user.propose_close().unwrap();
    run_bus(&mut p.user, &mut p.hub, msgs).unwrap();
    let h0 = rt.height().unwrap();
    advance(&rt, &mut p, 1);
    assert!(matches!(p.user.closing, Some(Closing::Cooperative { .. })));
    // exactly two channel txs on-chain: funding and the close
    let close_txs = rt.block_txs(h0 + 1).unwrap();
    assert_eq!(close_txs.len(), 2, "coinbase + close");
    let (u, h) = balances(&rt, &p);
    assert_eq!(u, Amount::from_sat(100_500 - 500));
    assert_eq!(h, Amount::from_sat(99_500 - 500));
}

#[test]
fn unilateral_close_with_delay() {
    init_log();
    let rt = Arc::new(Regtest::start().unwrap());
    let mut p = open_channel(&rt, "uni");
    pay(&mut p, Role::User, Amount::from_sat(30_000));
    pay(&mut p, Role::Hub, Amount::from_sat(10_000));
    // user: 80k, hub: 120k
    p.user.force_close().unwrap();
    advance(&rt, &mut p, 1); // commitment confirms; hub claims to_remote immediately
    let h_commit = rt.height().unwrap();
    assert!(matches!(p.hub.closing, Some(Closing::Remote { revoked: false, .. })));
    advance(&rt, &mut p, 1); // hub's claim confirms
    let (u, h) = balances(&rt, &p);
    assert_eq!(h, Amount::from_sat(120_000 - 1_000));
    assert_eq!(u, Amount::ZERO, "user's to_local is delayed");
    // user's to_local: CSV 6 → claim broadcastable at tip = h_commit + 5, confirmed at h_commit + 6
    while rt.height().unwrap() < h_commit + 4 {
        advance(&rt, &mut p, 1);
        assert_eq!(balances(&rt, &p).0, Amount::ZERO, "too early");
    }
    advance(&rt, &mut p, 2);
    let (u, _) = balances(&rt, &p);
    assert_eq!(u, Amount::from_sat(80_000 - 1_000 - 1_000), "balance minus commit fee minus sweep fee");
    assert_eq!(rt.height().unwrap(), h_commit + 6);
}

#[test]
fn penalty_on_revoked_broadcast() {
    init_log();
    let rt = Arc::new(Regtest::start().unwrap());
    let mut p = open_channel(&rt, "penalty");
    pay(&mut p, Role::Hub, Amount::from_sat(40_000)); // seq 1: user 140k, hub 60k
    pay(&mut p, Role::User, Amount::from_sat(60_000)); // seq 2: user 80k, hub 120k
    pay(&mut p, Role::User, Amount::from_sat(1_000)); // seq 3: user 79k, hub 121k
    // hub cheats: broadcasts seq 1 where it had... no wait, seq 1 favours the user.
    // The hub's best stale state is seq 2 (hub 120k) vs current seq 3 (hub 121k) — still
    // any revoked state is punishable; use seq 1 to make the sweep amounts unambiguous.
    p.hub.force_close_at(1).unwrap();
    advance(&rt, &mut p, 1); // revoked commitment confirms; user sweeps in the same block cycle
    assert!(matches!(p.user.closing, Some(Closing::Remote { revoked: true, .. })));
    advance(&rt, &mut p, 1); // penalty confirms
    let (u, h) = balances(&rt, &p);
    assert_eq!(u, Amount::from_sat(200_000 - 1_000 - 1_000), "everything minus commit fee minus sweep fee");
    assert_eq!(h, Amount::ZERO);
    // and the hub cannot claim its delayed output: it was swept already
    advance(&rt, &mut p, 8);
    assert_eq!(balances(&rt, &p).1, Amount::ZERO);
}
