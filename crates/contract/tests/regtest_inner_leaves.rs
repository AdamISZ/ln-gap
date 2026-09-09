//! The inner-level disprove leaves through the interpreter: a schedule word
//! and single SHA-256 rounds (including round 63 with the feed-forward).
//! Honest commitments must not be disprovable; a lie must be.

use std::time::Instant;

use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_contract::claim::{end_label, round_label, step_sources, ClaimKeys, StateSource};
use lngap_contract::inner::{self, round_leaf, round_sources, round_states, round_witness, sched_inputs, sched_leaf, sched_witness, schedule, InnerKeys, InnerSource};
use lngap_contract::script_hash::state_bytes;
use lngap_contract::toy::HashChain;
use lngap_contract::Program;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSig;

fn prover_keys(ks: &mut KeyStore, id: u32, seq: u64, d: u32, spec: &lngap_contract::ClaimSpec) -> ClaimKeys {
    ClaimKeys {
        end: ks.generate_wots(&end_label(id, seq, d), 32).unwrap(),
        rounds: (1..=spec.rounds()).map(|r| (0..spec.k - 1).map(|t| ks.generate_wots(&round_label(id, seq, d, r, t), 32).unwrap()).collect()).collect(),
        inner: Some(InnerKeys {
            sched: (16..inner::ROUNDS).map(|i| ks.generate_wots(&inner::sched_label(id, seq, d, i), 4).unwrap()).collect(),
            states: (1..=inner::SEARCH.rounds()).map(|r| (0..inner::INNER_K - 1).map(|t| ks.generate_wots(&inner::inner_state_label(id, seq, d, r, t), 32).unwrap()).collect()).collect(),
        }),
    }
}

/// Sign a value under the key a source resolves to (None for a constant).
fn sign_source(ks: &mut KeyStore, id: u32, seq: u64, d: u32, src: &InnerSource, state: &[u32; 8]) -> Option<WotsSig> {
    let label = match src {
        InnerSource::Outer(StateSource::Const(_)) => return None,
        InnerSource::Outer(StateSource::End) => end_label(id, seq, d),
        InnerSource::Outer(StateSource::Round(r, t)) => round_label(id, seq, d, *r, *t),
        InnerSource::Inner(r, t) => inner::inner_state_label(id, seq, d, *r, *t),
    };
    // a fresh store per signature so that lies do not trip the equivocation guard
    let mut fresh = KeyStore::new(Seed::from_label("prover"));
    let _ = ks;
    fresh.generate_wots(&label, 32).unwrap();
    Some(fresh.sign_wots(&label, &state_bytes(state)).unwrap())
}

fn sign_word(id: u32, seq: u64, d: u32, i: u32, w: u32) -> Option<WotsSig> {
    if i < 16 {
        return None;
    }
    let mut fresh = KeyStore::new(Seed::from_label("prover"));
    let label = inner::sched_label(id, seq, d, i);
    fresh.generate_wots(&label, 4).unwrap();
    Some(fresh.sign_wots(&label, &w.to_be_bytes()).unwrap())
}

struct Rig {
    rt: Regtest,
    sink: ScriptBuf,
    q: bitcoin::key::Keypair,
}

impl Rig {
    fn spend(&self, name: &str, leaf: &ScriptBuf, args: Vec<Vec<u8>>) -> Transaction {
        let tree = TapTree::new(vec![Leaf::new(name, leaf.clone(), Timelock::NONE)]).unwrap();
        let (op, prevout) = self.rt.fund(&tree.script_pubkey(), Amount::from_sat(200_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(150_000), script_pubkey: self.sink.clone() }]);
        let sig = sign_tapscript(&self.q, &tx, 0, std::slice::from_ref(&prevout), leaf).unwrap();
        let mut w = WitnessStack::new();
        w.push(sig.as_ref().to_vec()).extend(args);
        tx.input[0].witness = w.build(leaf, &tree.control_block(name).unwrap());
        tx
    }
}

#[test]
fn inner_leaves_on_regtest() {
    let rt = Regtest::start().unwrap();
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
    let pubs = [user.public(), hub.public()];
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
    let prover = Role::User; // the hub (payment key) is Q
    let rig = Rig { rt, sink: TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey(), q: hub.payment };
    let (id, seq, d) = (7u32, 1u64, 1u32);
    let prog = HashChain::standard();
    let spec = prog.claim().unwrap();
    let mut ks = KeyStore::new(Seed::from_label("prover"));
    let keys = prover_keys(&mut ks, id, seq, d, &spec);
    let block = spec.blocks[0];
    let w = schedule(&block);

    // ----- schedule leaves -----
    for i in [20u32, 63] {
        let (name, leaf) = sched_leaf(&ctx, prover, &keys, &block, i);
        let spend = |claimed: u32| {
            let sigs: Vec<Option<WotsSig>> = sched_inputs(i).iter().map(|j| sign_word(id, seq, d, *j, w[*j as usize])).collect();
            let refs: Vec<&WotsSig> = sigs.iter().flatten().collect();
            rig.spend(&name, &leaf, sched_witness(&refs, &sign_word(id, seq, d, i, claimed).unwrap()))
        };
        assert!(rig.rt.test_accept(&spend(w[i as usize])).is_err(), "honest W[{i}] must not be disprovable");
        let tx = spend(w[i as usize] ^ 0x8000);
        let vs = rig.rt.test_accept(&tx).unwrap_or_else(|e| panic!("sched_{i} rejected: {e}"));
        eprintln!("SIZE sched leaf i={i}: script {} B, witness {} B, vsize {vs}", leaf.len(), tx.input[0].witness.size());
    }

    // ----- round leaves: for the level-1 path isolating step 0 (cur constant) and step 5 (cur committed) -----
    for (path, rounds) in [(vec![0u32, 0], vec![0u32, 1, 30]), (vec![1, 1], vec![0, 63]), (vec![3, 3], vec![63])] {
        let (cur_src, next_src, step) = step_sources(&spec, &path);
        let states = spec.states();
        let cur = states[step as usize];
        let s = round_states(&cur, &w, None);
        assert_eq!(s[64], states[step as usize + 1], "inner chain ends at the honest next state");
        for r in rounds {
            let (name, leaf) = round_leaf(&ctx, prover, &keys, &cur_src, &next_src, &block, r);
            let (in_src, out_src, rr) = round_sources(&cur_src, &next_src, &[r / 8, r % 8]);
            assert_eq!(rr, r);
            let spend = |claimed_out: &[u32; 8]| {
                let in_sig = sign_source(&mut KeyStore::new(Seed::from_label("x")), id, seq, d, &in_src, &s[r as usize]);
                let w_sig = sign_word(id, seq, d, r, w[r as usize]);
                let cur_sig = if r == 63 { sign_source(&mut KeyStore::new(Seed::from_label("x")), id, seq, d, &InnerSource::Outer(cur_src.clone()), &cur) } else { None };
                let out_sig = sign_source(&mut KeyStore::new(Seed::from_label("x")), id, seq, d, &out_src, claimed_out).expect("output is always committed");
                rig.spend(&name, &leaf, round_witness(w_sig.as_ref(), in_sig.as_ref(), cur_sig.as_ref(), &out_sig))
            };
            let honest = s[r as usize + 1];
            assert!(rig.rt.test_accept(&spend(&honest)).is_err(), "honest round {r} must not be disprovable");
            let mut lie = honest;
            lie[(r % 8) as usize] ^= 1 << (r % 32);
            let tx = spend(&lie);
            let vs = rig.rt.test_accept(&tx).unwrap_or_else(|e| panic!("round {r} (path {path:?}) rejected: {e}"));
            eprintln!("SIZE round leaf r={r} path {path:?} ({in_src:?} -> {out_src:?}): script {} B, witness {} B, vsize {vs}", leaf.len(), tx.input[0].witness.size());
        }
    }

    // ----- the trees along the inner chain: leaf counts and build time -----
    let ck_inner: Vec<lngap_lamport::PublicKey> = (1..=inner::SEARCH.rounds()).map(|r| ks.generate(&inner::inner_index_label(id, seq, d, r), 3).unwrap()).collect();
    let t0 = Instant::now();
    let s0 = inner::wait_sched_tree(&ctx, prover, &keys).unwrap();
    let i1 = inner::wait_inner_q_tree(&ctx, prover, &keys, &ck_inner, &spec, 1).unwrap();
    let term = inner::round_terminal_tree(&ctx, prover, &keys, &spec).unwrap();
    eprintln!(
        "TREES p_sched leaf {} B; I_1 {} leaves; terminal {} leaves; built in {:?}",
        s0.leaf("p_sched").unwrap().script.len(),
        i1.leaves().len(),
        term.leaves().len(),
        t0.elapsed()
    );
}

