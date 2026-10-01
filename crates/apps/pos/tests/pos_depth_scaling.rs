//! Measurement (ZK_Z3_PLAN.md, step 1): how the pre-signed graph scales
//! with the contract's depth. The search played in the channel needs about
//! 30 depths (hello-world) to about 61 (a Groth16 verifier); chess runs at
//! 20. A chess contract at max depth M is added to a real Poon-Dryja
//! channel by one update, and we time each side's key generation, the
//! venue's registry, and the update itself (both sides build the graph for
//! both commitment versions, sign and verify), and measure the bytes on
//! the wire (the key offers, which travel out of band, and the update's
//! JSON messages).
//!
//! Opt-in (slow): `cargo test -p lngap-pos --release --test
//! pos_depth_scaling -- --ignored --nocapture`; `POS_DEPTHS=20,30` picks
//! the depths.

use std::sync::Arc;
use std::time::Instant;

use bitcoin::{Amount, OutPoint};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::chain::Chain;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::protocol::{funding_tree, run_bus, ChannelParty, Policy};
use lngap_channel::wire::{WireEnvelope, WireMsg};
use lngap_channel::{ChannelParams, ChannelState, ContractOutput, PartyKeys, Role};
use lngap_lamport::keystore::KeyStore;
use lngap_pos::instance::{self, Game, GameClock, PosInstance};
use lngap_pos::{Member, PosMiner};

const SEED: [u8; 32] = [0x6b; 32];
const GAME_ID: u16 = 1;
const FUNDING: Amount = Amount::from_sat(3_000_000);
const HALF: Amount = Amount::from_sat(1_500_000);
const STAKE: Amount = Amount::from_sat(500_000);
const DEPOSIT: Amount = Amount::from_sat(250_000);

fn members() -> Vec<Member> {
    (0..5u8).map(|i| Member::new([SEED[0] + i; 32])).collect()
}

fn open(rt: &Arc<Regtest>) -> (ChannelParty, ChannelParty) {
    let params = ChannelParams { presign_fee: Amount::from_sat(60_000), ..ChannelParams::regtest(FUNDING) };
    let user_keys = PartyKeys::from_seed(Role::User, Seed::from_label("scale/user"));
    let hub_keys = PartyKeys::from_seed(Role::Hub, Seed::from_label("scale/hub"));
    let pubs = [user_keys.public(), hub_keys.public()];
    let (u_op, u_prev) = rt.fund(&pubs[0].payout_spk, HALF + Amount::from_sat(10_000)).unwrap();
    let (h_op, h_prev) = rt.fund(&pubs[1].payout_spk, HALF + Amount::from_sat(10_000)).unwrap();
    let ftree = funding_tree(&pubs);
    let mut ftx = build_funding_tx(&[(u_op, u_prev.clone()), (h_op, h_prev.clone())], ftree.script_pubkey(), FUNDING);
    let funding = (OutPoint { txid: ftx.compute_txid(), vout: 0 }, ftx.output[0].clone());
    let initial = ChannelState { seq: 0, balances: [HALF, HALF], contracts: vec![] };
    let accept = || -> Policy { Box::new(|_, _| Ok(())) };
    let user_rev = [user_keys.revocation_hash(0), user_keys.revocation_hash(1)];
    let hub_rev = [hub_keys.revocation_hash(0), hub_keys.revocation_hash(1)];
    let chain: Arc<dyn Chain> = rt.clone();
    let mut user = ChannelParty::new(user_keys, pubs[1].clone(), params, funding.clone(), initial.clone(), hub_rev, chain.clone(), accept()).unwrap();
    let mut hub = ChannelParty::new(hub_keys, pubs[0].clone(), params, funding, initial, user_rev, chain, accept()).unwrap();
    let (m1, m2) = (user.initial_commit_sigs().unwrap(), hub.initial_commit_sigs().unwrap());
    run_bus(&mut user, &mut hub, vec![m1, m2]).unwrap();
    let prevouts = [u_prev, h_prev];
    sign_funding_input(&mut ftx, 0, &prevouts, &user.keys.payout_tree(), &user.keys.payout).unwrap();
    sign_funding_input(&mut ftx, 1, &prevouts, &hub.keys.payout_tree(), &hub.keys.payout).unwrap();
    rt.send_and_confirm(&ftx).unwrap();
    (user, hub)
}

#[test]
#[ignore]
fn graph_scaling_with_depth() {
    let depths: Vec<u32> = std::env::var("POS_DEPTHS").ok().map(|s| s.split(',').map(|x| x.trim().parse().unwrap()).collect()).unwrap_or(vec![20, 30, 60]);
    let rt = Arc::new(Regtest::start().unwrap());
    let mut miner = PosMiner::new(SEED, members());
    println!(
        "{:>5} {:>8} {:>9} {:>9} {:>10} {:>9} {:>11} {:>10} {:>11}",
        "depth", "keygen s", "offers MB", "registry", "graph txs", "update s", "graph sigs", "update MB", "contract leaves"
    );
    for (i, &m) in depths.iter().enumerate() {
        let (mut user, mut hub) = open(&rt);
        let id = 100 + i as u32;
        let mut ks = [KeyStore::new(Seed::from_label(&format!("scale/user-ks/{m}"))), KeyStore::new(Seed::from_label(&format!("scale/hub-ks/{m}")))];

        let t = Instant::now();
        let offer_u = instance::gen_pos_keys(&mut ks[0], Role::User, id, 1, m, Game::Chess).unwrap();
        let offer_h = instance::gen_pos_keys(&mut ks[1], Role::Hub, id, 1, m, Game::Chess).unwrap();
        let keygen = t.elapsed().as_secs_f64() / 2.0;
        let offers = serde_json::to_string(&offer_u).unwrap().len() + serde_json::to_string(&offer_h).unwrap().len();
        let keys = instance::collect_keys(&offer_u, &offer_h, m).unwrap();

        let t = Instant::now();
        let registry = miner.registry(id, m).unwrap();
        let reg_s = t.elapsed().as_secs_f64();
        let t0 = rt.mtp().unwrap();
        let clock = GameClock { t0, ell: 60, margin: 60 };
        let deadline = t0 + (m + 1) * 60 + 60 + 7 * 24 * 3600;
        let inst = PosInstance::new(id, STAKE * 2 + DEPOSIT * 2, deadline, GAME_ID, Game::Chess, clock, keys, registry).unwrap().with_deposit(DEPOSIT).unwrap();
        miner.register(id, m, inst.authorship()).unwrap();
        let contract: Arc<dyn ContractOutput> = Arc::new(inst);

        // one update adding the contract: both sides build both commitment
        // versions' graphs, sign, verify; every message crosses as JSON
        let t = Instant::now();
        let seq = user.current_seq() + 1;
        let msgs = user.propose(ChannelState { seq, balances: [HALF - STAKE - DEPOSIT, HALF - STAKE - DEPOSIT], contracts: vec![contract.clone()] }).unwrap();
        let mut queue: std::collections::VecDeque<_> = msgs.into();
        let (mut bytes, mut sigs) = (0usize, 0usize);
        while let Some(env) = queue.pop_front() {
            let w = WireEnvelope::from_env(&env).unwrap();
            if let WireMsg::CommitSigs { graph_sigs, .. } = &w.msg {
                sigs += graph_sigs.len();
            }
            let json = serde_json::to_string(&w).unwrap();
            bytes += json.len();
            let back: WireEnvelope = serde_json::from_str(&json).unwrap();
            let env = back.into_env(|cid| (cid == id).then(|| contract.clone())).unwrap();
            let target = if env.to == Role::User { &mut user } else { &mut hub };
            queue.extend(target.handle(env).unwrap());
        }
        let update_s = t.elapsed().as_secs_f64();
        assert_eq!((user.current_seq(), hub.current_seq()), (seq, seq));

        // the graph's size, for one commitment version
        let ctx = user.commit_ctx(seq, Role::User).unwrap();
        let op = OutPoint::null();
        let prev = bitcoin::TxOut { value: contract.value(), script_pubkey: contract.tree(&ctx).unwrap().script_pubkey() };
        let graph = contract.graph(&ctx, op, &prev).unwrap();
        let leaves = contract.tree(&ctx).unwrap().leaves().len();
        println!("{m:>5} {keygen:>8.2} {:>9.2} {reg_s:>8.2}s {:>10} {update_s:>9.2} {sigs:>11} {:>10.2} {leaves:>11}", offers as f64 / 1e6, graph.len(), bytes as f64 / 1e6);
    }
}
