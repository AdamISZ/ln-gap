//! Z3 step 6: `Game::Zk` in the PoS graph. A hello-world search contract
//! (11 rounds, 23 depths) with ZkFamily attached:
//!
//! - its contract tree and pre-signed graph build: the prove leaves and
//!   the claimant's final disproves at depth 23, `zk_choice`/`zk_copied`
//!   below, the input key's equivocation leaf, settle paying the prover;
//! - one channel update adds it to a real Poon-Dryja channel (both sides
//!   build, sign and verify both commitment versions' graphs; JSON on the
//!   wire);
//! - the venue seals every move of scenario A's game (the members' check:
//!   the state key's signature, the bodies opening the heads, the input
//!   signed) and refuses a body that doesn't open, an unsigned input, and
//!   a head under the wrong key.

use std::sync::Arc;
use std::time::Instant;

use bitcoin::{Amount, OutPoint};
use emulator::decision::challenge::ForceCondition;
use emulator::loader::program_definition::ProgramDefinition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::chain::Chain;
use lngap_channel::funding::{build_funding_tx, sign_funding_input};
use lngap_channel::protocol::{funding_tree, run_bus, ChannelParty, Policy};
use lngap_channel::wire::{WireEnvelope, WireMsg};
use lngap_channel::{ChannelParams, ChannelState, ContractOutput, PartyKeys, Role};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::ext::Family;
use lngap_pos::instance::{self, mover_at, Game, GameClock, PosInstance};
use lngap_pos::{Member, PosMiner};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::{search, Behaviour};
use lngap_zk::family::{encode_entry, encode_inputs, ZkFamily};
use lngap_zk::final_d60::{input_key_params, input_message, input_words};
use lngap_zk::game::{play, Entry, Search};

const SEED: [u8; 32] = [0x7c; 32];
const GAME_ID: u16 = 1;
const ID: u32 = 900;
const FUNDING: Amount = Amount::from_sat(3_000_000);
const HALF: Amount = Amount::from_sat(1_500_000);
const STAKE: Amount = Amount::from_sat(500_000);
const DEPOSIT: Amount = Amount::from_sat(250_000);
const INPUT: [u8; 4] = [0x11; 4];

fn pdf() -> String {
    format!("{}/programs/hello-world-binary.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn open(rt: &Arc<Regtest>) -> (ChannelParty, ChannelParty) {
    let params = ChannelParams { presign_fee: Amount::from_sat(60_000), ..ChannelParams::regtest(FUNDING) };
    let user_keys = PartyKeys::from_seed(Role::User, Seed::from_label("zkf/user"));
    let hub_keys = PartyKeys::from_seed(Role::Hub, Seed::from_label("zkf/hub"));
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
fn zk_contract_in_a_channel() {
    let rt = Arc::new(Regtest::start().unwrap());
    let (mut user, mut hub) = open(&rt);
    let mut miner = PosMiner::new(SEED, (0..5u8).map(|i| Member::new([SEED[0] + i; 32])).collect());
    let rounds = ProgramDefinition::from_config(&pdf()).unwrap().nary_def().total_rounds() as u32;
    let sr = Search { game_id: GAME_ID, rounds };
    let m = sr.total();
    let info = ProgramInfo::load(&pdf()).unwrap();
    // keys: both sides' per-depth keys; the prover's (the user's: odd
    // depths) input keys
    let mut ks = [KeyStore::new(Seed::from_label("zkf/user-ks")), KeyStore::new(Seed::from_label("zkf/hub-ks"))];
    let offer_u = instance::gen_pos_keys(&mut ks[0], Role::User, ID, 1, m, Game::Zk).unwrap();
    let offer_h = instance::gen_pos_keys(&mut ks[1], Role::Hub, ID, 1, m, Game::Zk).unwrap();
    let keys = instance::collect_keys(&offer_u, &offer_h, m).unwrap();
    let input_keys: Vec<WotsSecret> = (0..info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x90 + j as u8; 32])).collect();
    let family = ZkFamily::new(sr, info.clone(), input_keys.iter().map(|k| k.public()).collect());
    println!("family: {family:?}");
    let registry = miner.registry(ID, m).unwrap();
    let t0 = rt.mtp().unwrap();
    let clock = GameClock { t0, ell: 60, margin: 60 };
    let deadline = t0 + (m + 1) * 60 + 60 + 7 * 24 * 3600;
    let inst = PosInstance::new(ID, STAKE * 2 + DEPOSIT * 2, deadline, GAME_ID, Game::Zk, clock, keys, registry)
        .unwrap()
        .with_deposit(DEPOSIT)
        .unwrap()
        .with_family(family.clone())
        .unwrap();
    miner.register(ID, m, inst.authorship()).unwrap();

    // the trees and the graph
    let ctx = user.commit_ctx(0, Role::User).unwrap();
    let t = Instant::now();
    let tree = inst.tree(&ctx).unwrap();
    assert!(tree.leaf("equiv_input_0").is_ok() && tree.leaf("settle").is_ok());
    let fin = inst.refuted_tree(&ctx, sr.depths()).unwrap();
    let names: Vec<&str> = fin.leaves().iter().map(|l| l.name.as_str()).collect();
    let n_prove = names.iter().filter(|n| n.starts_with("zk_prove_")).count();
    let n_dis = names.iter().filter(|n| n.starts_with("disprove_")).count();
    assert!(n_prove == family.classes.len() && n_prove > 0);
    assert!(names.contains(&"disprove_zk_record_step") && names.contains(&"disprove_zk_halt_exit") && names.contains(&"disprove_zk_input_0") && names.contains(&"not_timely"));
    assert!(inst.refuted_tree(&ctx, 4).unwrap().leaf("disprove_zk_choice").is_ok());
    assert!(inst.refuted_tree(&ctx, 5).unwrap().leaf("disprove_zk_copied").is_ok());
    assert!(inst.refuted_tree(&ctx, 1).unwrap().leaf("disprove_zk_claim").is_ok());
    // the read challenge (D62): the opening, a phase-2 choice, the terminal
    assert!(inst.refuted_tree(&ctx, sr.open_depth()).unwrap().leaf("disprove_zk_open").is_ok());
    assert!(inst.refuted_tree(&ctx, sr.open_depth() + 2).unwrap().leaf("disprove_zk_choice").is_ok());
    let term = inst.refuted_tree(&ctx, m).unwrap();
    assert!(["disprove_zk_read_value_1", "disprove_zk_read_value_2", "disprove_zk_correct_hash", "disprove_zk_copied"].iter().all(|n| term.leaf(n).is_ok()));
    let graph = inst.graph(&ctx, OutPoint::null(), &bitcoin::TxOut { value: inst.value, script_pubkey: tree.script_pubkey() }).unwrap();
    println!("{m} depths; at {}: {n_prove} prove leaves, {n_dis} disproves; graph {} pre-signed txs; trees and graph built in {:.2?}", sr.depths(), graph.len(), t.elapsed());

    // one channel update adding it
    let contract: Arc<dyn ContractOutput> = Arc::new(inst.clone());
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
        let env = serde_json::from_str::<WireEnvelope>(&json).unwrap().into_env(|cid| (cid == ID).then(|| contract.clone())).unwrap();
        let target = if env.to == Role::User { &mut user } else { &mut hub };
        queue.extend(target.handle(env).unwrap());
    }
    assert_eq!((user.current_seq(), hub.current_seq()), (seq, seq));
    println!("channel update: {:.2?}, {sigs} graph signatures, {:.2} MB on the wire", t.elapsed(), bytes as f64 / 1e6);

    // the venue seals scenario A's moves
    let dir = std::env::temp_dir().join(format!("lngap-zkf-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let a = search(&pdf(), &INPUT, &dir, &Behaviour::default(), &Behaviour::default(), ForceCondition::ValidInputStepAndHash).unwrap().unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let entries = play(&a, &sr).unwrap();
    let words = input_words(&INPUT);
    let wsigs: Vec<_> = words.iter().zip(&input_keys).map(|(w, k)| k.sign(&input_message(*w)).unwrap()).collect();
    let encode = |e: &Entry, ks: &mut [KeyStore; 2], inputs: bool| {
        let mover = mover_at(e.depth);
        let sig = ks[mover.idx()].sign_wots(&instance::state_label(ID, 1, e.depth), &e.head[4..]).unwrap();
        let mut body = e.body();
        if inputs {
            body.extend(encode_inputs(&words, &wsigs));
        }
        encode_entry(&e.head, &sig, &body)
    };
    for e in &entries {
        let enc = encode(e, &mut ks, e.depth == 1);
        if e.depth == 1 {
            // refused first: the input unsigned
            assert!(!family.entry_ok(
                1,
                &inst.depth_keys(1).state,
                &encode_entry(&e.head, &WotsSecret::from_entropy(input_key_params(), [1; 32]).sign(&[0; 4]).unwrap(), &e.body())
            ));
        }
        // a body that doesn't open the head
        let mut bad = enc.clone();
        let last = bad.len() - 1;
        bad[last] ^= 1;
        assert!(!family.entry_ok(e.depth, &inst.depth_keys(e.depth).state, &bad), "depth {}: a tampered body", e.depth);
        let sealer = miner.default_sealer(ID, e.depth).unwrap();
        miner.seal_entry(ID, e.depth, sealer, &enc).unwrap_or_else(|err| panic!("depth {}: {err}", e.depth));
    }
    // a head under the wrong key (the other side's state key at depth 2)
    let e = &entries[1];
    assert!(!family.entry_ok(2, &inst.depth_keys(3).state, &encode(e, &mut ks, false)));
    println!("the venue sealed all {} moves of scenario A (disputed step {})", entries.len(), a.step);
}
