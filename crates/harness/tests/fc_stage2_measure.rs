//! Stage 2 measurement: n4bit dispute chain script sizes, witness sizes,
//! and fee reserves. Builds the actual on-chain dispute transaction graph
//! for an n4bit ClaimSpec and measures concrete numbers.

use anyhow::Result;
use bitcoin::Amount;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_contract::claim::{
    self, end_label, index_label, round_label, ClaimKeys, ClaimSpec, Init, Pred, Src, Step,
};
use lngap_contract::inner::{self, InnerKeys};
use lngap_contract::ChallengerKeys;
use lngap_factchain::claim::FactChainShape;
use lngap_lamport::keystore::KeyStore;
use lngap_n4bit::{self, hash, target_from_difficulty};
use std::sync::Arc;

const ID: u32 = 10;
const SEQ: u64 = 1;
const D: u32 = 1;

fn prover_keys(spec: &ClaimSpec, ks: &mut KeyStore) -> ClaimKeys {
    let nb = spec.wots_bytes();
    let ir = spec.inner_search().rounds() as usize;
    let bw = spec.hash.block_words();
    ClaimKeys {
        end: ks.generate_wots(&end_label(ID, SEQ, D), nb).unwrap(),
        rounds: (1..=spec.rounds())
            .map(|r| {
                (0..spec.k - 1)
                    .map(|t| {
                        ks.generate_wots(&round_label(ID, SEQ, D, r, t), nb)
                            .unwrap()
                    })
                    .collect()
            })
            .collect(),
        inner: if spec.inner {
            Some(InnerKeys {
                re_cur: ks
                    .generate_wots(&inner::re_cur_label(ID, SEQ, D), nb)
                    .unwrap(),
                re_next: ks
                    .generate_wots(&inner::re_next_label(ID, SEQ, D), nb)
                    .unwrap(),
                block: (0..bw)
                    .map(|j| {
                        ks.generate_wots(&inner::block_label(ID, SEQ, D, j as u32), 4)
                            .unwrap()
                    })
                    .collect(),
                sched: if spec.has_schedule() {
                    (bw as u32..spec.inner_rounds())
                        .map(|i| {
                            ks.generate_wots(&inner::sched_label(ID, SEQ, D, i), 4)
                                .unwrap()
                        })
                        .collect()
                } else {
                    vec![]
                },
                states: (1..=ir)
                    .map(|r| {
                        (0..spec.inner_k() - 1)
                            .map(|t| {
                                ks.generate_wots(
                                    &inner::inner_state_label(ID, SEQ, D, r as u32, t),
                                    (spec.d_words() * 4) as u32,
                                )
                                .unwrap()
                            })
                            .collect()
                    })
                    .collect(),
            })
        } else {
            None
        },
    }
}

fn challenger_keys(spec: &ClaimSpec, ks: &mut KeyStore) -> ChallengerKeys {
    ChallengerKeys {
        indices: (1..=spec.rounds())
            .map(|r| {
                ks.generate(&index_label(ID, SEQ, D, r), spec.index_bits())
                    .unwrap()
            })
            .collect(),
        inner_indices: if spec.inner {
            (1..=spec.inner_search().rounds())
                .map(|r| {
                    ks.generate(
                        &inner::inner_index_label(ID, SEQ, D, r),
                        spec.inner_search().index_bits(),
                    )
                    .unwrap()
                })
                .collect()
        } else {
            vec![]
        },
    }
}

fn measure_dispute(
    rt: &Regtest,
    ctx: &CommitCtx,
    prover: Role,
    spec: &ClaimSpec,
    label: &str,
) -> Result<(usize, usize, u64, usize)> {
    let mut ks = KeyStore::new(Seed::from_label(&format!("{label}_prover")));
    let keys = prover_keys(spec, &mut ks);
    let mut ks2 = KeyStore::new(Seed::from_label(&format!("{label}_chall")));
    let ck = challenger_keys(spec, &mut ks2);

    let parent_tree = TapTree::new(vec![Leaf::new(
        "dispute",
        ctx.two_of_two(bitcoin::script::Builder::new()).into_script(),
        Timelock::NONE,
    )])
    .unwrap();
    let parent_op = rt
        .fund(&parent_tree.script_pubkey(), Amount::from_sat(200_000))?
        .0;
    let parent_prevout = TxOut {
        value: Amount::from_sat(200_000),
        script_pubkey: parent_tree.script_pubkey(),
    };

    let t0 = std::time::Instant::now();
    let dispute_txs = claim::dispute_graph(
        ctx,
        prover,
        &keys,
        &ck,
        spec,
        &parent_tree,
        parent_op,
        &parent_prevout,
    )?;
    let elapsed = t0.elapsed();

    let mut total_script = 0usize;
    let mut total_witness = 0usize;
    let mut total_fee = 0u64;

    println!("\n=== {} dispute chain ===", label);
    println!("  spec: {} steps, {} level-1 rounds", spec.steps.len(), spec.rounds());
    if spec.inner {
        println!(
            "  inner: {} rounds, k={}, search={:?}",
            spec.inner_rounds(),
            spec.inner_k(),
            spec.inner_search()
        );
    }

    for tx in &dispute_txs {
        let script_len = tx.leaf.script.len();
        // Witness: 2 channel sigs + control block + script + any proof elements
        let witness_size = tx.tx.input[0].witness.size();
        // Fee = sum(prevouts) - sum(outputs)
        let in_val: u64 = tx.prevouts.iter().map(|o| o.value.to_sat()).sum();
        let out_val: u64 = tx.tx.output.iter().map(|o| o.value.to_sat()).sum();
        let fee = in_val - out_val;

        total_script += script_len;
        total_witness += witness_size;
        total_fee += fee;

        println!(
            "  {:25} script={:5}B  witness={:5}B  fee={:5}  ({})",
            tx.label, script_len, witness_size, fee, tx.role_description
        );
    }

    println!("\n  {} totals: {} txs, {} script, {} witness, {} sat fee, {:?} build",
        label, dispute_txs.len(), total_script, total_witness, total_fee, elapsed);

    Ok((total_script, total_witness, total_fee, dispute_txs.len()))
}

use bitcoin::TxOut;

#[test]
fn n4bit_vs_sha256_dispute_chain() -> Result<()> {
    let rt = Arc::new(Regtest::start()?);
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
    let pubs = [user.public(), hub.public()];
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let ctx = CommitCtx {
        params: &params,
        keys: &pubs,
        broadcaster: Role::User,
        seq: 1,
        rev_hash: [0u8; 20],
    };
    let prover = Role::User;

    // n4bit spec: 1 header, 7 steps, padded to 8, 3 bisection rounds
    let checkpoint = hash(&[]);
    let shape = FactChainShape {
        checkpoint,
        target: target_from_difficulty(5),
        n_headers: 1,
    };
    let n4_spec = shape.spec();

    println!("\n========== n4bit ClaimSpec ==========");
    println!("  hash kind: {:?}", n4_spec.hash);
    println!("  n_words: {}", n4_spec.n_words);
    println!("  d_words: {} ({} nibbles)", n4_spec.d_words(), n4_spec.d_nibbles());
    println!("  block_words: {}", n4_spec.hash.block_words());
    println!("  inner_rounds: {}", n4_spec.inner_rounds());
    println!("  inner_k: {}", n4_spec.inner_k());
    println!("  has_schedule: {}", n4_spec.has_schedule());
    println!("  has_feed_forward: {}", n4_spec.has_feed_forward());
    println!("  steps: {}", n4_spec.steps.len());
    println!("  level-1 rounds: {}", n4_spec.rounds());
    println!("  inner search: {:?}", n4_spec.inner_search());

    let (n4_script, n4_witness, n4_fee, n4_txs) =
        measure_dispute(&rt, &ctx, prover, &n4_spec, "n4bit")?;

    // SHA-256 spec: 1 header = 3 compressions + 1 check = 4 steps, 2 rounds
    let spv_spec = ClaimSpec {
        n_words: 24,
        start: vec![0u32; 24],
        steps: vec![
            Step::compress(
                "hdr_c1",
                Init::Iv,
                vec![
                    Src::Data(0), Src::Data(1), Src::Data(2), Src::Data(3),
                    Src::Data(4), Src::Data(5), Src::Data(6), Src::Data(7),
                    Src::Data(8), Src::Data(9), Src::Data(10), Src::Data(11),
                    Src::Data(12), Src::Data(13), Src::Data(14), Src::Data(15),
                ],
            ),
            Step::compress(
                "hdr_c2",
                Init::D,
                vec![
                    Src::Data(0), Src::Data(1), Src::Data(2), Src::Data(3),
                    Src::Const(0x80000000), Src::Const(0), Src::Const(0), Src::Const(0),
                    Src::Const(0), Src::Const(0), Src::Const(0), Src::Const(0),
                    Src::Const(0), Src::Const(0), Src::Const(0), Src::Const(1664),
                ],
            ),
            Step::compress(
                "hdr_c3",
                Init::Iv,
                vec![
                    Src::Reg(0), Src::Reg(1), Src::Reg(2), Src::Reg(3),
                    Src::Reg(4), Src::Reg(5), Src::Reg(6), Src::Reg(7),
                    Src::Const(0), Src::Const(0), Src::Const(0), Src::Const(0),
                    Src::Const(0), Src::Const(0), Src::Const(0), Src::Const(0),
                ],
            ),
            Step::check(
                "target",
                vec![Pred::LeTarget {
                    target: {
                        let mut t = [0xffu8; 32];
                        t[31] = 0x7f;
                        t
                    },
                }],
            ),
        ],
        k: 2,
        inner: true,
        ..Default::default()
    };

    let (spv_script, spv_witness, spv_fee, spv_txs) =
        measure_dispute(&rt, &ctx, prover, &spv_spec, "SHA-256")?;

    println!("\n========== Comparison ==========");
    println!(
        "  n4bit:   {} txs, {} script bytes, {} witness bytes, {} sat fee",
        n4_txs, n4_script, n4_witness, n4_fee
    );
    println!(
        "  SHA-256: {} txs, {} script bytes, {} witness bytes, {} sat fee",
        spv_txs, spv_script, spv_witness, spv_fee
    );
    if spv_script > 0 {
        println!(
            "  Script size ratio: {:.1}x smaller (n4bit {}B vs SHA-256 {}B)",
            spv_script as f64 / n4_script as f64,
            n4_script,
            spv_script
        );
    }
    if spv_witness > 0 {
        println!(
            "  Witness size ratio: {:.1}x smaller",
            spv_witness as f64 / n4_witness as f64
        );
    }
    if spv_fee > 0 {
        println!(
            "  Fee ratio: {:.1}x cheaper (n4bit {} sat vs SHA-256 {} sat)",
            spv_fee as f64 / n4_fee as f64,
            n4_fee,
            spv_fee
        );
    }

    // Also measure the n4bit round leaf script directly
    let round_script = lngap_n4bit::script::round_leaf_script(1);
    println!("\n========== n4bit round leaf (per-round Script) ==========");
    println!("  size: {} bytes/round", round_script.len());
    println!("  vs SHA-256 round leaf: ~12,000 bytes/round");
    println!(
        "  ratio: {:.1}x smaller",
        12000.0 / round_script.len() as f64
    );

    assert!(n4_txs > 0, "should have dispute transactions");
    assert!(n4_script > 0, "should have script bytes");

    Ok(())
}
