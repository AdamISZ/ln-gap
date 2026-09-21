//! Stage 2 measurement: n4bit dispute chain script sizes, witness sizes,
//! and fee reserves. Builds the actual on-chain dispute transaction graph
//! for an n4bit ClaimSpec and measures concrete numbers.
//!
//! Measures at W = 1, 10, 100 headers for both n4bit and SHA-256 baselines,
//! printing a scaling comparison table.

use anyhow::Result;
use bitcoin::Amount;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_contract::claim::{
    self, end_label, index_label, round_label, ClaimKeys, ClaimSpec, HashKind, Init, Pred, Src,
    Step,
};
use lngap_contract::inner::{self, InnerKeys};
use lngap_contract::ChallengerKeys;
use lngap_factchain::claim::FactChainShape;
use lngap_lamport::keystore::KeyStore;
use lngap_n4bit::{self, hash, target_from_difficulty};
use std::sync::Arc;
use std::time::Duration;

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

/// One row of measurement results.
struct Measurement {
    label: String,
    w: usize,
    steps: usize,
    rounds: u32,
    total_script: usize,
    total_witness: usize,
    total_fee: u64,
    tx_count: usize,
    build_time: Duration,
}

fn measure_dispute(
    rt: &Regtest,
    ctx: &CommitCtx,
    prover: Role,
    spec: &ClaimSpec,
    label: &str,
    w: usize,
) -> Result<Measurement> {
    let mut ks = KeyStore::new(Seed::from_label(&format!("{label}_prover_w{w}")));
    let keys = prover_keys(spec, &mut ks);
    let mut ks2 = KeyStore::new(Seed::from_label(&format!("{label}_chall_w{w}")));
    let ck = challenger_keys(spec, &mut ks2);

    let parent_tree = TapTree::new(vec![Leaf::new(
        "dispute",
        ctx.two_of_two(bitcoin::script::Builder::new())
            .into_script(),
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
        None,
    )?;
    let elapsed = t0.elapsed();

    let mut total_script = 0usize;
    let mut total_witness = 0usize;
    let mut total_fee = 0u64;

    println!("\n=== {} dispute chain (W={}) ===", label, w);
    println!(
        "  spec: {} steps, {} level-1 rounds",
        spec.steps.len(),
        spec.rounds()
    );
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

    println!(
        "\n  {} W={} totals: {} txs, {} script, {} witness, {} sat fee, {:?} build",
        label,
        w,
        dispute_txs.len(),
        total_script,
        total_witness,
        total_fee,
        elapsed
    );

    Ok(Measurement {
        label: label.to_string(),
        w,
        steps: spec.steps.len(),
        rounds: spec.rounds(),
        total_script,
        total_witness,
        total_fee,
        tx_count: dispute_txs.len(),
        build_time: elapsed,
    })
}

/// Build the n4bit ClaimSpec for W headers.
fn n4bit_spec(w: usize) -> ClaimSpec {
    let checkpoint = hash(&[]);
    let shape = FactChainShape {
        checkpoint,
        target: target_from_difficulty(5),
        n_headers: w,
    };
    shape.spec()
}

/// Build the SHA-256 baseline ClaimSpec for W headers.
///
/// Each header = 3 compression steps + 1 check step = 4 steps.
/// For W headers: 4*W steps, padded to next power of 2.
fn sha256_spec(w: usize) -> ClaimSpec {
    let target = {
        let mut t = [0xffu8; 32];
        t[31] = 0x7f;
        t
    };

    let mut steps = Vec::new();
    for h in 0..w {
        // compression 1: first block (16 data words)
        steps.push(Step::compress(
            &format!("hdr{h}_c1"),
            Init::Iv,
            vec![
                Src::Data(0),
                Src::Data(1),
                Src::Data(2),
                Src::Data(3),
                Src::Data(4),
                Src::Data(5),
                Src::Data(6),
                Src::Data(7),
                Src::Data(8),
                Src::Data(9),
                Src::Data(10),
                Src::Data(11),
                Src::Data(12),
                Src::Data(13),
                Src::Data(14),
                Src::Data(15),
            ],
        ));
        // compression 2: padding block
        steps.push(Step::compress(
            &format!("hdr{h}_c2"),
            Init::D,
            vec![
                Src::Const(0x80000000),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(1664),
            ],
        ));
        // compression 3: register-chained block
        steps.push(Step::compress(
            &format!("hdr{h}_c3"),
            Init::Iv,
            vec![
                Src::Reg(0),
                Src::Reg(1),
                Src::Reg(2),
                Src::Reg(3),
                Src::Reg(4),
                Src::Reg(5),
                Src::Reg(6),
                Src::Reg(7),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
                Src::Const(0),
            ],
        ));
        // PoW check — include a per-header EqConst so each check leaf is
        // unique (otherwise duplicate predicates produce identical taproot
        // leaves, which the tree builder rejects).
        steps.push(Step::check(
            &format!("hdr{h}_target"),
            vec![
                Pred::EqConst {
                    off: h,
                    nibbles: vec![0],
                },
                Pred::LeTarget { target },
            ],
        ));
    }

    // Pad to next power of 2 (for bisection with k=2)
    let mut n = 1;
    while n < steps.len() {
        n *= 2;
    }
    while steps.len() < n {
        steps.push(Step::nop());
    }

    ClaimSpec {
        n_words: 24,
        start: vec![0u32; 24],
        steps,
        k: 2,
        inner: true,
        hash: HashKind::Sha256,
        flat_inner: false,
    }
}

fn print_table(rows: &[Measurement]) {
    println!("\n{}", "=".repeat(80));
    println!("========== SCALING COMPARISON TABLE ==========");
    println!(
        "{:>6} {:>5} {:>6} {:>5} {:>10} {:>10} {:>12} {:>7} {:>10}",
        "kind", "W", "steps", "rnds", "script(B)", "witness(B)", "fee(sat)", "txs", "build(ms)"
    );
    println!("{}", "-".repeat(80));
    for r in rows {
        println!(
            "{:>6} {:>5} {:>6} {:>5} {:>10} {:>10} {:>12} {:>7} {:>10.1}",
            r.label,
            r.w,
            r.steps,
            r.rounds,
            r.total_script,
            r.total_witness,
            r.total_fee,
            r.tx_count,
            r.build_time.as_secs_f64() * 1000.0,
        );
    }
    println!("{}", "-".repeat(80));

    // Ratios at each W
    println!("\n========== n4bit vs SHA-256 ratios (SHA-256 / n4bit) ==========");
    println!(
        "{:>5} {:>12} {:>14} {:>12} {:>10} {:>12}",
        "W", "script ratio", "witness ratio", "fee ratio", "tx ratio", "build ratio"
    );
    println!("{}", "-".repeat(70));
    for w in [1, 10, 100] {
        let n4 = rows.iter().find(|r| r.label == "n4bit" && r.w == w);
        let spv = rows.iter().find(|r| r.label == "SHA-256" && r.w == w);
        if let (Some(n4), Some(spv)) = (n4, spv) {
            let sr = spv.total_script as f64 / n4.total_script as f64;
            let wr = spv.total_witness as f64 / n4.total_witness as f64;
            let fr = spv.total_fee as f64 / n4.total_fee as f64;
            let tr = spv.tx_count as f64 / n4.tx_count as f64;
            let br = spv.build_time.as_secs_f64() / n4.build_time.as_secs_f64().max(1e-9);
            println!(
                "{:>5} {:>12.1}x {:>14.1}x {:>12.1}x {:>10.1}x {:>12.1}x",
                w, sr, wr, fr, tr, br
            );
        }
    }
    println!("{}", "-".repeat(70));
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

    let widths = [1usize, 10, 100];
    let mut measurements = Vec::new();

    for &w in &widths {
        // --- n4bit ---
        let n4_spec = n4bit_spec(w);

        if w == 1 {
            // Print the detailed spec info only for W=1 (existing behavior)
            println!("\n========== n4bit ClaimSpec (W={}) ==========", w);
            println!("  hash kind: {:?}", n4_spec.hash);
            println!("  n_words: {}", n4_spec.n_words);
            println!(
                "  d_words: {} ({} nibbles)",
                n4_spec.d_words(),
                n4_spec.d_nibbles()
            );
            println!("  block_words: {}", n4_spec.hash.block_words());
            println!("  inner_rounds: {}", n4_spec.inner_rounds());
            println!("  inner_k: {}", n4_spec.inner_k());
            println!("  has_schedule: {}", n4_spec.has_schedule());
            println!("  has_feed_forward: {}", n4_spec.has_feed_forward());
            println!("  steps: {}", n4_spec.steps.len());
            println!("  level-1 rounds: {}", n4_spec.rounds());
            println!("  inner search: {:?}", n4_spec.inner_search());
        }

        let n4_m = measure_dispute(&rt, &ctx, prover, &n4_spec, "n4bit", w)?;
        measurements.push(n4_m);

        // --- SHA-256 baseline ---
        let spv_spec = sha256_spec(w);

        if w == 1 {
            println!("\n========== SHA-256 ClaimSpec (W={}) ==========", w);
            println!("  hash kind: {:?}", spv_spec.hash);
            println!("  n_words: {}", spv_spec.n_words);
            println!("  steps: {}", spv_spec.steps.len());
            println!("  level-1 rounds: {}", spv_spec.rounds());
            println!("  inner search: {:?}", spv_spec.inner_search());
        }

        let spv_m = measure_dispute(&rt, &ctx, prover, &spv_spec, "SHA-256", w)?;
        measurements.push(spv_m);
    }

    print_table(&measurements);

    // Also measure the n4bit round leaf script directly
    let round_script = lngap_n4bit::script::round_leaf_script(1);
    println!("\n========== n4bit round leaf (per-round Script) ==========");
    println!("  size: {} bytes/round", round_script.len());
    println!("  vs SHA-256 round leaf: ~12,000 bytes/round");
    println!(
        "  ratio: {:.1}x smaller",
        12000.0 / round_script.len() as f64
    );

    // Assertions on the W=1 n4bit baseline (existing checks)
    let n4_w1 = measurements
        .iter()
        .find(|m| m.label == "n4bit" && m.w == 1)
        .expect("W=1 n4bit measurement");
    assert!(n4_w1.tx_count > 0, "should have dispute transactions");
    assert!(n4_w1.total_script > 0, "should have script bytes");

    Ok(())
}
