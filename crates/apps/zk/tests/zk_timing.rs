//! Where a Game::Zk graph build spends its time (hello-world, 47 depths):
//! the family's leaf scripts vs the trees around them; a second build of
//! the same contract shows what a cache saves.

use std::time::Instant;

use bitcoin::{Amount, OutPoint, TxOut};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_btc::keys::Seed;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::ext::Family;
use lngap_pos::instance::{self, Game, GameClock, PosInstance};
use lngap_pos::{Member, PosMiner};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::family::ZkFamily;
use lngap_zk::final_d60::input_key_params;
use lngap_zk::game::Search;

#[test]
fn graph_build_timing() {
    let pdf = format!("{}/programs/hello-world-binary.yaml", env!("CARGO_MANIFEST_DIR"));
    let rounds = ProgramDefinition::from_config(&pdf).unwrap().nary_def().total_rounds() as u32;
    let sr = Search { game_id: 1, rounds };
    let m = sr.total();
    let info = ProgramInfo::load(&pdf).unwrap();
    let mut ks = [KeyStore::new(Seed::from_label("zkt/u")), KeyStore::new(Seed::from_label("zkt/h"))];
    let keys = instance::collect_keys(
        &instance::gen_pos_keys(&mut ks[0], Role::User, 7, 1, m, Game::Zk).unwrap(),
        &instance::gen_pos_keys(&mut ks[1], Role::Hub, 7, 1, m, Game::Zk).unwrap(),
        m,
    )
    .unwrap();
    let ik: Vec<_> = (0..info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [j as u8; 32]).public()).collect();
    let family = ZkFamily::new(sr, info, ik);
    let mut miner = PosMiner::new([5; 32], (0..5u8).map(|i| Member::new([5 + i; 32])).collect());
    let registry = miner.registry(7, m).unwrap();
    let inst = PosInstance::new(7, Amount::from_sat(600_000), 1_900_000_000, 1, Game::Zk, GameClock { t0: 1_800_000_000, ell: 60, margin: 60 }, keys, registry)
        .unwrap()
        .with_family(family.clone())
        .unwrap();
    let params = ChannelParams::regtest(Amount::from_sat(600_000));
    let pubs = [PartyKeys::from_seed(Role::User, Seed::from_label("zkt/pu")).public(), PartyKeys::from_seed(Role::Hub, Seed::from_label("zkt/ph")).public()];
    let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0; 20] };

    // the family's leaves alone, every depth
    let t = Instant::now();
    let mut n = 0;
    for d in 1..=m {
        let l = inst.layout(d);
        n += family.disprove_leaves(&l, &inst.depth_keys(d).rebut).len();
        if d == sr.depths() {
            n += family.prove_leaves(&l, &inst.depth_keys(d).rebut).len();
        }
    }
    let t_leaves = t.elapsed();
    let tree = inst.tree(&ctx).unwrap();
    let prev = TxOut { value: inst.value, script_pubkey: tree.script_pubkey() };
    let t = Instant::now();
    let g1 = inst.graph(&ctx, OutPoint::null(), &prev).unwrap();
    let t1 = t.elapsed();
    let t = Instant::now();
    let _ = inst.graph(&ctx, OutPoint::null(), &prev).unwrap();
    let t2 = t.elapsed();
    println!("{n} family leaves built in {t_leaves:.2?}; graph ({} txs) {t1:.2?}, again {t2:.2?}", g1.len());
}
