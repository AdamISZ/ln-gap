//! The disprove leaves of both chains through the interpreter, on a 24-word
//! register file: schedule word, block word, re-commitment mismatch, a
//! compression's keep/predicate/copy checks, single SHA-256 rounds (both
//! init kinds, including round 63 with the feed-forward), and a simple step.
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
use lngap_contract::claim::{end_label, round_label, state_nibbles, words_bytes, ClaimKeys, ClaimSpec, Copy, Init, Pred, Src, StateSource, Step, IV};
use lngap_contract::inner::{self, block_leaf, ccopy_leaf, ckeep_leaf, cpred_leaf, mismatch_leaf, round_leaf, round_sources, round_states, round_witness, sched_inputs, sched_leaf, sched_witness, schedule, InnerKeys, InnerSource};
use lngap_contract::simple::simple_leaf;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSig;

const N: usize = 24;
const ID: u32 = 7;
const SEQ: u64 = 1;
const D: u32 = 1;

fn prover_keys(spec: &ClaimSpec) -> ClaimKeys {
    let mut ks = KeyStore::new(Seed::from_label("prover"));
    let nb = spec.wots_bytes();
    ClaimKeys {
        end: ks.generate_wots(&end_label(ID, SEQ, D), nb).unwrap(),
        rounds: (1..=spec.rounds()).map(|r| (0..spec.k - 1).map(|t| ks.generate_wots(&round_label(ID, SEQ, D, r, t), nb).unwrap()).collect()).collect(),
        inner: Some(InnerKeys {
            re_cur: ks.generate_wots(&inner::re_cur_label(ID, SEQ, D), nb).unwrap(),
            re_next: ks.generate_wots(&inner::re_next_label(ID, SEQ, D), nb).unwrap(),
            block: (0..16).map(|j| ks.generate_wots(&inner::block_label(ID, SEQ, D, j), 4).unwrap()).collect(),
            sched: (16..inner::ROUNDS).map(|i| ks.generate_wots(&inner::sched_label(ID, SEQ, D, i), 4).unwrap()).collect(),
            states: (1..=inner::SEARCH.rounds()).map(|r| (0..inner::INNER_K - 1).map(|t| ks.generate_wots(&inner::inner_state_label(ID, SEQ, D, r, t), 32).unwrap()).collect()).collect(),
        }),
    }
}

/// Sign under a label with a fresh store (so lies do not trip the equivocation guard).
fn sign(label: &str, msg: &[u8]) -> WotsSig {
    let mut ks = KeyStore::new(Seed::from_label("prover"));
    ks.generate_wots(label, msg.len() as u32).unwrap();
    ks.sign_wots(label, msg).unwrap()
}
fn sign_word(i: u32, w: u32) -> WotsSig {
    let label = if i < 16 { inner::block_label(ID, SEQ, D, i) } else { inner::sched_label(ID, SEQ, D, i) };
    sign(&label, &w.to_be_bytes())
}
fn sign_state(label: &str, s: &[u32]) -> WotsSig {
    sign(label, &words_bytes(s))
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
    /// The honest witness must be rejected, the lying one accepted; returns the lying tx's vsize.
    fn check(&self, what: &str, leaf: &ScriptBuf, honest: Vec<Vec<u8>>, lie: Vec<Vec<u8>>) -> u64 {
        assert!(self.rt.test_accept(&self.spend("l", leaf, honest)).is_err(), "{what}: honest must not be disprovable");
        let tx = self.spend("l", leaf, lie);
        let vs = self.rt.test_accept(&tx).unwrap_or_else(|e| panic!("{what}: lie rejected: {e}"));
        eprintln!("SIZE {what}: script {} B, witness {} B, vsize {vs}", leaf.len(), tx.input[0].witness.size());
        vs
    }
}

/// A 24-word spec in the SPV pipeline's shapes: a header-like compression
/// from data words with a link predicate and a copy into A, a compression
/// from D with mixed sources and an nBits predicate, a target check, a nop.
fn spec() -> ClaimSpec {
    let mut start = vec![0u32; N];
    start[..8].copy_from_slice(&IV);
    for (i, w) in start.iter_mut().enumerate().skip(8) {
        *w = (i as u32).wrapping_mul(0x9e37_79b9);
    }
    let nn = 8 * N;
    let block_data: [Src; 16] = core::array::from_fn(Src::Data);
    let block_mixed: [Src; 16] = core::array::from_fn(|j| if j < 4 { Src::Data(j) } else if j == 4 { Src::Const(0x8000_0000) } else if j == 15 { Src::Const(1664) } else if j == 8 { Src::Reg(9) } else { Src::Const(0) });
    let mut target = [0xffu8; 32];
    target[31] = 0x7f;
    let c1 = Step::compress("hdr1", Init::Iv, block_data)
        .with_preds(vec![Pred::EqNibbles { a: nn + 8, b: 0, n: 64 }])
        .with_copies(vec![Copy { src: nn + 72, dst: 64, n: 56 }]);
    let c2 = Step::compress("hdr2", Init::D, block_mixed).with_preds(vec![Pred::EqConst { off: nn + 16, nibbles: state_nibbles(&[0x207f_ffff]) }]).with_copies(vec![Copy { src: nn, dst: 120, n: 8 }]);
    let target_check = Step::check("target", vec![Pred::LeTarget { target }, Pred::EqNibbles { a: 64, b: 128, n: 8 }]);
    ClaimSpec { n_words: N, start, steps: vec![c1, c2, target_check, Step::nop()], k: 2, inner: true, ..Default::default() }
}

#[test]
fn inner_and_check_leaves_on_regtest() {
    let rt = Regtest::start().unwrap();
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
    let pubs = [user.public(), hub.public()];
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
    let prover = Role::User; // the hub (payment key) is Q
    let rig = Rig { rt, sink: TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey(), q: hub.payment };
    let spec = spec();
    let keys = prover_keys(&spec);
    let mut hdr1 = vec![0x1111_1111u32; 16];
    hdr1[1..9].copy_from_slice(&spec.start[..8]);
    let hdr2 = vec![0x2222_2222u32, 0x3333_3333, 0x207f_ffff, 0x4444_4444];
    let data: Vec<Vec<u32>> = vec![hdr1.clone(), hdr2.clone()];
    let states = spec.states(&data);
    let s1 = spec.apply(&spec.steps[0], &states[0], &hdr1);
    assert!(s1.1, "hdr1 predicates hold");
    assert!(spec.apply(&spec.steps[1], &states[1], &hdr2).1, "hdr2 predicates hold");
    let re_cur_l = inner::re_cur_label(ID, SEQ, D);
    let re_next_l = inner::re_next_label(ID, SEQ, D);

    // ----- schedule leaves (path- and kind-independent) -----
    let (_init0, block0) = ClaimSpec::compress_inputs(&spec.steps[0], &states[0], &hdr1);
    let w = schedule(&block0);
    for i in [20u32, 63] {
        let (_, leaf) = sched_leaf(&ctx, prover, &keys, i);
        let wit = |claimed: u32| {
            let sigs: Vec<WotsSig> = sched_inputs(i).iter().map(|j| sign_word(*j, w[*j as usize])).collect();
            let refs: Vec<&WotsSig> = sigs.iter().collect();
            sched_witness(&refs, &sign_word(i, claimed))
        };
        rig.check(&format!("sched i={i}"), &leaf, wit(w[i as usize]), wit(w[i as usize] ^ 0x8000));
    }

    // ----- block word leaves: a register source and a constant -----
    for (j, src) in [(8usize, Src::Reg(9)), (4, Src::Const(0x8000_0000))] {
        let (_, leaf) = block_leaf(&ctx, prover, &keys, N, j, src);
        let expected = match src { Src::Reg(i) => states[1][i], Src::Const(c) => c, Src::Data(_) => unreachable!() };
        let wit = |claimed: u32| {
            let mut v = sign_word(j as u32, claimed).consumption_order();
            if matches!(src, Src::Reg(_)) {
                v.extend(sign_state(&re_cur_l, &states[1]).consumption_order());
            }
            v
        };
        rig.check(&format!("block j={j} {src:?}"), &leaf, wit(expected), wit(expected ^ 1));
    }

    // ----- re-commitment mismatch: constant source and a round key -----
    for (which_next, src, val) in [(false, StateSource::Const(spec.start.clone()), states[0].clone()), (true, StateSource::Round(1, 0), states[1].clone())] {
        let (name, leaf) = mismatch_leaf(&ctx, prover, &keys, N, which_next, &src);
        let re_label = if which_next { &re_next_l } else { &re_cur_l };
        let wit = |re: &[u32]| {
            let mut v = sign_state(re_label, re).consumption_order();
            if let StateSource::Round(r, t) = src {
                v.extend(sign_state(&round_label(ID, SEQ, D, r, t), &val).consumption_order());
            }
            v
        };
        let mut lie = val.clone();
        lie[17] ^= 0x10;
        rig.check(&name, &leaf, wit(&val), wit(&lie));
    }

    // ----- a compression's keep / predicate / copy checks (step 0) -----
    {
        let step = &spec.steps[0];
        let (_, block) = ClaimSpec::compress_inputs(step, &states[0], &hdr1);
        let block_words: Vec<u32> = (0..16).map(|j| u32::from_be_bytes(block[4 * j..4 * j + 4].try_into().unwrap())).collect();
        let block_sigs = |words: &[u32]| -> Vec<Vec<u8>> { words.iter().enumerate().rev().flat_map(|(j, w)| sign_word(j as u32, *w).consumption_order()).collect() };
        // keep: a register other than D and the copy destination (A) changed
        let (name, leaf) = ckeep_leaf(&ctx, prover, &keys, N, step);
        let wit = |next: &[u32]| {
            let mut v = sign_state(&re_cur_l, &states[0]).consumption_order();
            v.extend(sign_state(&re_next_l, next).consumption_order());
            v
        };
        let mut lie = states[1].clone();
        lie[20] ^= 4;
        rig.check(&name, &leaf, wit(&states[1]), wit(&lie));
        let mut fine = states[1].clone();
        fine[9] ^= 4; // inside the copy destination: not this leaf's business
        assert!(rig.rt.test_accept(&rig.spend("l", &leaf, wit(&fine))).is_err());
        // predicate: the link (block words 1..9 == D)
        let (name, leaf) = cpred_leaf(&ctx, prover, &keys, N, step);
        let wit = |words: &[u32]| {
            let mut v = block_sigs(words);
            v.extend(sign_state(&re_cur_l, &states[0]).consumption_order());
            v
        };
        let mut lie = block_words.clone();
        lie[5] ^= 0x100;
        rig.check(&name, &leaf, wit(&block_words), wit(&lie));
        // copy: A must equal block words 9..16
        let (name, leaf) = ccopy_leaf(&ctx, prover, &keys, N, step);
        let wit = |next: &[u32]| {
            let mut v = block_sigs(&block_words);
            v.extend(sign_state(&re_next_l, next).consumption_order());
            v
        };
        let mut lie = states[1].clone();
        lie[12] ^= 0x10;
        rig.check(&name, &leaf, wit(&states[1]), wit(&lie));
    }

    // ----- round leaves: init Iv (step 0) and init D (step 1) -----
    for (step, rounds) in [(0usize, vec![0u32, 1, 63]), (1, vec![0, 30, 63])] {
        let cur = &states[step];
        let next = &states[step + 1];
        let (init, block) = ClaimSpec::compress_inputs(&spec.steps[step], cur, &data[step]);
        let init_kind = match &spec.steps[step] { Step::Compress { init, .. } => *init, _ => unreachable!() };
        let w = schedule(&block);
        let s = round_states(&init, &w, None);
        assert_eq!(&s[64][..], &next[..8], "inner chain ends at the step's D");
        for r in rounds {
            let (name, leaf) = round_leaf(&ctx, prover, &keys, N, init_kind, r);
            let (in_src, out_src, _) = round_sources(init_kind, &[r / 8, r % 8]);
            let sig_inner = |src: &InnerSource, st: &[u32; 8]| -> Option<WotsSig> {
                match src {
                    InnerSource::Init(Init::Iv) => None,
                    InnerSource::Init(Init::D) => Some(sign_state(&re_cur_l, cur)),
                    InnerSource::ReNext => {
                        let mut n = next.clone();
                        n[..8].copy_from_slice(st);
                        Some(sign_state(&re_next_l, &n))
                    }
                    InnerSource::Inner(rr, t) => Some(sign_state(&inner::inner_state_label(ID, SEQ, D, *rr, *t), st)),
                }
            };
            let wit = |claimed_out: &[u32; 8]| {
                let in_sig = sig_inner(&in_src, &s[r as usize]);
                let init_sig = if r == 63 { sig_inner(&InnerSource::Init(init_kind), &init) } else { None };
                let out_sig = sig_inner(&out_src, claimed_out).expect("output is always committed");
                round_witness(&sign_word(r, w[r as usize]), in_sig.as_ref(), init_sig.as_ref(), &out_sig)
            };
            let honest = s[r as usize + 1];
            let mut lie = honest;
            lie[(r % 8) as usize] ^= 1 << (r % 32);
            rig.check(&format!("{name} r={r} step {step} ({in_src:?} -> {out_src:?})"), &leaf, wit(&honest), wit(&lie));
        }
    }

    // ----- the simple steps: target check (predicates) and nop -----
    {
        let step = &spec.steps[2];
        let (name, leaf) = simple_leaf(&ctx, prover, &keys, N, step);
        // craft a state satisfying both predicates: D below the target (byte 31 < 0x80), A[0] == A[8]
        let mut cur = states[2].clone();
        cur[7] &= 0xffff_ff7f;
        cur[16] = cur[8];
        assert!(spec.apply(step, &cur, &[]).1, "target and A[0] == A[8] hold on the crafted state");
        let wit = |c: &[u32], next: &[u32]| {
            let mut v = sign_state(&re_cur_l, c).consumption_order();
            v.extend(sign_state(&re_next_l, next).consumption_order());
            v
        };
        // lie 1: an untouched register changed
        let mut lie = cur.clone();
        lie[23] ^= 1;
        rig.check(&format!("{name} (bad keep)"), &leaf, wit(&cur, &cur), wit(&cur, &lie));
        // lie 2: the target predicate fails (D's most significant byte ≥ 0x80) with a consistent next
        let mut hi = cur.clone();
        hi[7] |= 0x80;
        assert!(!spec.apply(step, &hi, &[]).1);
        let tx = rig.spend("l", &leaf, wit(&hi, &hi));
        let vs = rig.rt.test_accept(&tx).unwrap_or_else(|e| panic!("failed target predicate must be disprovable: {e}"));
        eprintln!("SIZE {name} (bad target): vsize {vs}");
        // lie 3: the equality predicate fails
        let mut ne = cur.clone();
        ne[16] ^= 0x1000_0000;
        assert!(!spec.apply(step, &ne, &[]).1);
        rig.rt.test_accept(&rig.spend("l", &leaf, wit(&ne, &ne))).unwrap_or_else(|e| panic!("failed equality predicate must be disprovable: {e}"));
        // and a nop step
        let (nname, nleaf) = simple_leaf(&ctx, prover, &keys, N, &spec.steps[3]);
        let mut lie = states[3].clone();
        lie[0] ^= 1;
        rig.check(&nname, &nleaf, wit(&states[3], &states[3]), wit(&states[3], &lie));
    }

    // ----- trees along the chains: leaf counts and build time -----
    let mut ks = KeyStore::new(Seed::from_label("challenger"));
    let ck = lngap_contract::ChallengerKeys {
        indices: (1..=spec.rounds()).map(|r| ks.generate(&lngap_contract::claim::index_label(ID, SEQ, D, r), spec.index_bits()).unwrap()).collect(),
        inner_indices: (1..=inner::SEARCH.rounds()).map(|r| ks.generate(&inner::inner_index_label(ID, SEQ, D, r), 3).unwrap()).collect(),
    };
    let t0 = Instant::now();
    let (_, trees) = inner::compress_chain(&ctx, prover, &keys, &ck, &spec).unwrap();
    let (_, ctrees) = lngap_contract::simple::check_chain(&ctx, prover, &keys, &spec).unwrap();
    let total: usize = trees.iter().chain(ctrees.iter()).map(|t| t.leaves().iter().map(|l| l.script.len()).sum::<usize>()).sum();
    eprintln!(
        "TREES I_1 {} leaves; T {} leaves; C_1 {} leaves; {} KB of leaf scripts; built in {:?}",
        trees[4].leaves().len(),
        trees[7].leaves().len(),
        ctrees[2].leaves().len(),
        total / 1000,
        t0.elapsed()
    );
}
