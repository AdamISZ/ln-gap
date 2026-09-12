//! Measure fact-chain proof sizes at various W (header count) values.
//! This is the PoC's validating outcome: are the dispute proofs
//! small enough for practical Bitcoin transactions?

use anyhow::Result;
use lngap_factchain::{ChainClient, FactShape, Miner, DIFFICULTY_BITS, HEADER_BYTES};
use lngap_n4bit::DIGEST_BYTES;

#[test]
fn measure_proof_sizes() -> Result<()> {
    let g = lngap_factchain::genesis();
    let mut miner = Miner::new(g.header.digest(), 0);
    let mut client = ChainClient::from_checkpoint(0, g.header.digest());

    // Mine 100 blocks with dummy entries
    for i in 0..100u32 {
        let mut e = vec![0u8; 64];
        e[0..4].copy_from_slice(&(i + 1).to_le_bytes());
        miner.submit(e.clone());
        let block = miner.mine_next().expect("mine");
        client.verify_and_append(&block).map_err(|e| anyhow::anyhow!(e))?;
    }

    println!("\n=== Fact-chain proof size measurement ===");
    println!("Header: {} bytes (prev={} + root={} + height=4 + nonce=4)", HEADER_BYTES, DIGEST_BYTES, DIGEST_BYTES);
    println!("Digest: {} bits (160-bit, 2^80 collision security)", DIGEST_BYTES * 8);
    println!("Difficulty: {} bits (fixed, no retargeting)", DIFFICULTY_BITS);
    println!();

    // Measure at various W values
    for w in [4, 10, 50, 100] {
        let shape = FactShape {
            checkpoint: g.header.digest(),
            difficulty_bits: DIFFICULTY_BITS,
            n_headers: w,
        };
        let entry = vec![0xABu8; 64];
        let data = shape.build_data(&client, &entry);
        let total_header_bytes = data.headers.len() * HEADER_BYTES;
        let entry_bytes = data.entry.len();

        // Bisection: the claim has w header compressions + 1 entry-hash + 1 entry-predicate
        // = w + 2 steps, padded to next power of 2
        let n_steps = w + 2;
        let mut padded = 1;
        while padded < n_steps {
            padded *= 2;
        }
        let rounds = f64::log2(padded as f64) as u32;

        // Fee reserve: 1000 sat per dispute transaction, 2 txs per round + terminal
        let n_dispute_txs = (rounds as usize) * 2 + 3; // p_round + q_round per round + move + terminal + dispute_open
        let fee_reserve = n_dispute_txs as u64 * 1000;

        println!("W={w:3}: {} headers ({} bytes) + {} bytes entry = {} bytes off-chain data",
            data.headers.len(), total_header_bytes, entry_bytes, total_header_bytes + entry_bytes);
        println!("       {} real steps, {} padded, {} bisection rounds, ~{} dispute txs, ~{} sat fee reserve",
            n_steps, padded, rounds, n_dispute_txs, fee_reserve);
    }

    println!();
    println!("=== Comparison: old SPV (Bitcoin) vs new fact chain ===");
    println!();
    println!("| W  | old (SPV) steps | old rounds | old fee | new steps | new rounds | new fee |");
    println!("|----|-----------------|------------|----------|-----------|------------|----------|");

    // Old SPV: ~128 steps, 7 rounds, ~27k sat (from the current PoC)
    let old_steps = 128;
    let old_rounds = 7;
    let old_fee = 27_000u64;

    for w in [4, 10, 50, 100] {
        let n_steps = w + 2;
        let mut padded = 1;
        while padded < n_steps {
            padded *= 2;
        }
        let rounds = f64::log2(padded as f64) as u32;
        let n_dispute_txs = (rounds as usize) * 2 + 3;
        let fee_reserve = n_dispute_txs as u64 * 1000;

        // Old is always 128/7/27k regardless of W (shape was pinned)
        println!("| {:2} | {:3}             | {:2}          | {:5}    | {:3}       | {:2}         | {:5}    |",
            w, old_steps, old_rounds, old_fee, n_steps, rounds, fee_reserve);
    }

    println!();
    println!("Key result: at W=100 (the W_max bound), the fact chain proof has");
    let n_steps = 102;
    let mut padded = 1;
    while padded < n_steps {
        padded *= 2;
    }
    let rounds = f64::log2(padded as f64) as u32;
    let n_dispute_txs = (rounds as usize) * 2 + 3;
    let fee_reserve = n_dispute_txs as u64 * 1000;
    println!("  {} steps (vs {} old), {} bisection rounds (vs {}), ~{} sat fee reserve (vs ~{} old)",
            n_steps, old_steps, rounds, old_rounds, fee_reserve, old_fee);
    println!("  The old design could not handle W=100 (shape pinned at open time).");
    println!("  The new design handles any W up to W_max because W is prover-selected.");

    Ok(())
}
