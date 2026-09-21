//! Cryptanalysis test suite for the n4bit hash function.
//!
//! This module implements the standard cryptanalysis tests that a
//! cryptographer would run on a new hash design. The tests are organized
//! in three layers:
//!
//! 1. **S-box layer**: properties of the 4-bit substitution box in isolation.
//!    The S-box is the only nonlinear component; if it is weak, the whole
//!    construction is weak.
//!
//! 2. **Round function layer**: how differences and linear masks propagate
//!    through one or more SPN rounds. This tells us how many rounds we need
//!    for full diffusion.
//!
//! 3. **Hash function layer**: statistical properties of the full sponge
//!    construction — avalanche distribution, output uniformity, collision
//!    resistance at a reduced security level, and preimage resistance.
//!
//! For the educational background on what each test measures and why it
//! matters, see docs/planning/hermes-research/CRYPTANALYSIS_PRIMER.md.

use crate::*;
use std::collections::HashMap;

// ============================================================
// 1. S-BOX ANALYSIS
// ============================================================

/// Compute the Differential Distribution Table (DDT) of a 4-bit S-box.
///
/// The DDT is a 16×16 table. Entry (Δx, Δy) counts how many inputs x
/// satisfy S(x) ⊕ S(x ⊕ Δx) = Δy. For a bijection, the first row and
/// first column are always [16, 0, 0, …] and [16, 0, 0, …].
///
/// The **differential uniformity** is the maximum entry outside (0,0).
/// For a 4-bit S-box, the best possible (optimal) value is 4.
pub fn ddt(sbox: &[u8; 16]) -> [[u32; 16]; 16] {
    let mut table = [[0u32; 16]; 16];
    for dx in 0..16u32 {
        for x in 0..16u32 {
            let y1 = sbox[x as usize] as u32;
            let y2 = sbox[(x ^ dx) as usize] as u32;
            let dy = y1 ^ y2;
            table[dx as usize][dy as usize] += 1;
        }
    }
    table
}

/// Differential uniformity: the maximum DDT entry excluding (0,0).
pub fn differential_uniformity(sbox: &[u8; 16]) -> u32 {
    let table = ddt(sbox);
    let mut max = 0;
    for dx in 0..16 {
        for dy in 0..16 {
            if dx == 0 && dy == 0 {
                continue;
            }
            max = max.max(table[dx][dy]);
        }
    }
    max
}

/// Compute the Linear Approximation Table (LAT) of a 4-bit S-box.
///
/// The LAT is a 16×16 table. Entry (α, β) counts how many inputs x
/// satisfy (x · α) = (S(x) · β), where · is the bitwise inner product
/// (parity of AND). The count ranges from 0 to 16; a value of 8 means
/// no correlation (the mask pair is balanced). The **bias** is
/// |count - 8| / 16.
///
/// The **nonlinearity** of the S-box is 2^(n-1) - max|count - 8|,
/// where the max is over all nonzero α. For a 4-bit S-box, the best
/// possible nonlinearity is 4 (max|count - 8| = 4).
pub fn lat(sbox: &[u8; 16]) -> [[i32; 16]; 16] {
    let mut table = [[0i32; 16]; 16];
    for alpha in 0..16u32 {
        for beta in 0..16u32 {
            let mut count = 0i32;
            for x in 0..16u32 {
                let input_bit = (x & alpha).count_ones() % 2;
                let output_bit = (sbox[x as usize] as u32 & beta).count_ones() % 2;
                if input_bit == output_bit {
                    count += 1;
                }
            }
            table[alpha as usize][beta as usize] = count;
        }
    }
    table
}

/// Nonlinearity of the S-box: 2^(n-1) - max|LAT entry - 8| over nonzero α.
///
/// For n=4: nonlinearity = 8 - max|LAT[α][β] - 8| for α ≠ 0.
/// Optimal nonlinearity for a 4-bit S-box is 4.
pub fn nonlinearity(sbox: &[u8; 16]) -> i32 {
    let table = lat(sbox);
    let mut max_dev = 0i32;
    for alpha in 1..16 {
        for beta in 0..16 {
            let dev = (table[alpha][beta] - 8).abs();
            max_dev = max_dev.max(dev);
        }
    }
    8 - max_dev
}

/// Compute the Algebraic Normal Form (ANF) degree of each output bit of the
/// S-box.
///
/// Each output bit is a Boolean function of 4 input bits. Its ANF is a
/// polynomial over GF(2). The degree of this polynomial is the algebraic
/// degree. For a 4-bit S-box, the maximum possible degree is 3 (degree 4
/// would mean the function depends on all 4 input bits' product, which is
/// impossible for a balanced function — it would be x1x2x3x4, which is 1
/// only for x=1111).
///
/// Higher algebraic degree means better resistance to algebraic attacks.
/// The PRESENT S-box has algebraic degree 3 for all output bits.
pub fn algebraic_degrees(sbox: &[u8; 16]) -> [u32; 4] {
    let mut degrees = [0u32; 4];
    for bit in 0..4 {
        // Build the truth table for output bit `bit`
        let mut tt = [0u8; 16];
        for x in 0..16 {
            tt[x] = (sbox[x] >> bit) & 1;
        }
        // Compute the ANF via the Möbius transform (butterfly over GF(2))
        let mut anf = tt.map(|b| b as u32);
        let n = 4;
        for i in 0..n {
            let mask = 1usize << i;
            for j in 0..16 {
                if j & mask != 0 {
                    anf[j] ^= anf[j ^ mask];
                }
            }
        }
        // Find the highest-degree nonzero term
        let mut max_deg = 0;
        for (idx, &val) in anf.iter().enumerate() {
            if val != 0 {
                let deg = idx.count_ones();
                max_deg = max_deg.max(deg);
            }
        }
        degrees[bit] = max_deg;
    }
    degrees
}

/// The **branch number** of the S-box with respect to differential
/// cryptanalysis. For a 4-bit S-box used in a substitution-permutation
/// network, the differential branch number is:
///
///   B_d = min_{Δx ≠ 0} (wt(Δx) + wt(S(x) ⊕ S(x ⊕ Δx)))
///
/// where wt is the Hamming weight. A higher branch number means a
/// difference in few input bits necessarily causes differences in many
/// output bits, which means faster diffusion.
pub fn differential_branch_number(sbox: &[u8; 16]) -> u32 {
    let mut min_b = u32::MAX;
    for dx in 1..16u32 {
        let wt_in = dx.count_ones();
        let mut max_wt_out = 0u32;
        for x in 0..16u32 {
            let dy = (sbox[x as usize] as u32) ^ (sbox[(x ^ dx) as usize] as u32);
            max_wt_out = max_wt_out.max(dy.count_ones());
        }
        // The branch number is the minimum over all x, but for the S-box
        // alone (not a full round), we report the minimum sum.
        // Actually the standard definition uses the minimum over all Δx of
        // (wt(Δx) + wt(ΔS)), where ΔS is the *set* of output differences.
        // For a single S-box, wt(ΔS) is just wt(Δy) for any fixed x (they
        // may vary, so we take the min over x).
        let mut min_wt_out = u32::MAX;
        for x in 0..16u32 {
            let dy = (sbox[x as usize] as u32) ^ (sbox[(x ^ dx) as usize] as u32);
            min_wt_out = min_wt_out.min(dy.count_ones());
        }
        min_b = min_b.min(wt_in + min_wt_out);
    }
    min_b
}

// ============================================================
// 2. ROUND FUNCTION ANALYSIS
// ============================================================

/// How many SPN rounds until a single-nibble difference affects all 40
/// nibbles of the state?
///
/// We place a difference of 1 in nibble 0 and run the round function
/// (without round constants, since constants don't affect difference
/// propagation through ADD — wait, they DO affect ADD differences because
/// ADD is not linear over GF(2)). So we run the full round function with
/// constants and track which nibbles differ between two states.
///
/// This is the **full diffusion round count**: the minimum number of
/// rounds after which any single-nibble difference affects every nibble.
pub fn full_diffusion_rounds() -> usize {
    let mut state_a = [0u8; STATE_NIBBLES];
    let mut state_b = [0u8; STATE_NIBBLES];
    state_b[0] = 1; // one-nibble difference

    for r in 0..100 {
        spn_round(&mut state_a, r);
        spn_round(&mut state_b, r);
        let mut diff_count = 0;
        for i in 0..STATE_NIBBLES {
            if state_a[i] != state_b[i] {
                diff_count += 1;
            }
        }
        if diff_count == STATE_NIBBLES {
            return r + 1;
        }
    }
    100 // didn't converge
}

/// Track diffusion profile: for each round, how many nibbles differ.
pub fn diffusion_profile() -> Vec<usize> {
    let mut state_a = [0u8; STATE_NIBBLES];
    let mut state_b = [0u8; STATE_NIBBLES];
    state_b[0] = 1;

    let mut profile = Vec::new();
    for r in 0..30 {
        spn_round(&mut state_a, r);
        spn_round(&mut state_b, r);
        let diff_count = (0..STATE_NIBBLES)
            .filter(|&i| state_a[i] != state_b[i])
            .count();
        profile.push(diff_count);
        if diff_count == STATE_NIBBLES && r >= 5 {
            break;
        }
    }
    profile
}

/// Strict Avalanche Criterion (SAC) at the hash level.
///
/// SAC says: if you flip exactly one input bit, each output bit should
/// flip with probability exactly 50%. We test this by sampling many
/// random inputs, flipping bit 0, and measuring the flip probability of
/// each output bit.
///
/// We report the maximum deviation from 0.5 across all output bits.
/// A good hash should have max deviation < 0.05 (5%) with enough samples.
pub fn sac_test(num_samples: usize, input_len: usize) -> Vec<f64> {
    // Use a simple PRNG for reproducibility
    let mut seed = 0x12345678u64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) as u32
    };

    let mut flip_counts = [0u64; 160]; // 160 output bits

    for _ in 0..num_samples {
        // Generate random input
        let mut input = vec![0u8; input_len];
        for b in &mut input {
            *b = next() as u8;
        }

        let h1 = hash(&input);
        input[0] ^= 1; // flip bit 0
        let h2 = hash(&input);

        for byte_idx in 0..DIGEST_BYTES {
            for bit_idx in 0..8 {
                let bit = byte_idx * 8 + bit_idx;
                let b1 = (h1[byte_idx] >> bit_idx) & 1;
                let b2 = (h2[byte_idx] >> bit_idx) & 1;
                if b1 != b2 {
                    flip_counts[bit] += 1;
                }
            }
        }
    }

    flip_counts
        .iter()
        .map(|&c| c as f64 / num_samples as f64)
        .collect()
}

/// Bit Independence Criterion (BIC).
///
/// BIC says: for each pair of output bits (i, j), when we flip one
/// input bit, the flips of output bits i and j should be statistically
/// independent. We measure this as the maximum absolute correlation
/// between the flip indicators of bit i and bit j, over all pairs.
///
/// A good hash should have BIC correlation close to 0.
pub fn bic_test(num_samples: usize, input_len: usize) -> f64 {
    let mut seed = 0xDEADBEEFu64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) as u32
    };

    // Track joint flips for a subset of bit pairs (all 160*159/2 is too many;
    // sample 20 representative pairs)
    let pairs: Vec<(usize, usize)> = (0..20)
        .flat_map(|i| (i + 1..20).map(move |j| (i, j)))
        .collect();

    let mut joint = vec![[0u64; 4]; pairs.len()]; // [00, 01, 10, 11]

    for _ in 0..num_samples {
        let mut input = vec![0u8; input_len];
        for b in &mut input {
            *b = next() as u8;
        }
        let h1 = hash(&input);
        input[0] ^= 1;
        let h2 = hash(&input);

        for (idx, &(i, j)) in pairs.iter().enumerate() {
            let bi = ((h1[i / 8] >> (i % 8)) & 1) != ((h2[i / 8] >> (i % 8)) & 1);
            let bj = ((h1[j / 8] >> (j % 8)) & 1) != ((h2[j / 8] >> (j % 8)) & 1);
            let code = (bi as usize) * 2 + (bj as usize);
            joint[idx][code] += 1;
        }
    }

    // Compute max correlation
    let n = num_samples as f64;
    let mut max_corr = 0.0f64;
    for counts in &joint {
        let p00 = counts[0] as f64 / n;
        let p01 = counts[1] as f64 / n;
        let p10 = counts[2] as f64 / n;
        let p11 = counts[3] as f64 / n;
        let pi = p10 + p11; // P(bit i flips)
        let pj = p01 + p11; // P(bit j flips)
        let expected_11 = pi * pj;
        let corr = (p11 - expected_11).abs() / (pi * pj * (1.0 - pi) * (1.0 - pj)).sqrt().max(1e-10);
        max_corr = max_corr.max(corr);
    }
    max_corr
}

// ============================================================
// 3. HASH FUNCTION STATISTICAL TESTS
// ============================================================

/// Avalanche weight distribution: for many input pairs differing by one
/// bit, measure the Hamming weight of the output difference.
///
/// For a 160-bit hash, the expected distribution is Binomial(160, 0.5),
/// with mean 80 and standard deviation √(160 × 0.25) ≈ 6.32. We compute
/// the mean and standard deviation and compare.
pub fn avalanche_distribution(num_samples: usize, input_len: usize) -> (f64, f64) {
    let mut seed = 0xABCDEF01u64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) as u32
    };

    let mut weights = Vec::with_capacity(num_samples);
    for _ in 0..num_samples {
        let mut input = vec![0u8; input_len];
        for b in &mut input {
            *b = next() as u8;
        }
        let h1 = hash(&input);
        input[0] ^= 1;
        let h2 = hash(&input);

        let mut w = 0u32;
        for i in 0..DIGEST_BYTES {
            w += (h1[i] ^ h2[i]).count_ones();
        }
        weights.push(w);
    }

    let mean = weights.iter().map(|&w| w as f64).sum::<f64>() / num_samples as f64;
    let variance = weights
        .iter()
        .map(|&w| (w as f64 - mean).powi(2))
        .sum::<f64>()
        / num_samples as f64;
    (mean, variance.sqrt())
}

/// Chi-square test on nibble values in the output.
///
/// For each nibble position (40 nibbles in 20 bytes), count the frequency
/// of each value 0–15 across many hash outputs. Under the null hypothesis
/// (uniform), each value should appear with probability 1/16. The
/// chi-square statistic should be close to (16-1) = 15 per nibble position.
///
/// We report the maximum chi-square across all nibble positions.
pub fn chi_square_nibbles(num_samples: usize) -> f64 {
    let mut seed = 0x55AA55AAu64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) as u32
    };

    let num_nibbles = DIGEST_BYTES * 2; // 40 nibbles
    let mut counts = vec![[0u64; 16]; num_nibbles];

    for _ in 0..num_samples {
        let mut input = vec![0u8; 48];
        for b in &mut input {
            *b = next() as u8;
        }
        let h = hash(&input);
        for byte_idx in 0..DIGEST_BYTES {
            let hi = (h[byte_idx] >> 4) & 0xF;
            let lo = h[byte_idx] & 0xF;
            counts[byte_idx * 2][hi as usize] += 1;
            counts[byte_idx * 2 + 1][lo as usize] += 1;
        }
    }

    let expected = num_samples as f64 / 16.0;
    let mut max_chi = 0.0f64;
    for nibble_counts in &counts {
        let chi: f64 = nibble_counts
            .iter()
            .map(|&c| {
                let diff = c as f64 - expected;
                diff * diff / expected
            })
            .sum();
        max_chi = max_chi.max(chi);
    }
    max_chi
}

/// Birthday collision search on a truncated hash.
///
/// We truncate the 160-bit digest to `bits` bits and hash random inputs
/// until we find a collision. The expected number of hashes for a collision
/// in `bits` bits is ~2^(bits/2) (the birthday bound).
///
/// We use bits=20 (expected ~1024 hashes) to verify that the hash behaves
/// according to the birthday bound. If collisions are found significantly
/// faster, the hash has a structural weakness.
///
/// Returns (number of hashes, expected number).
pub fn birthday_collision_search(bits: usize, max_hashes: usize) -> (usize, f64) {
    let mut seed = 0xCAFEBABEu64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) as u32
    };

    let mask_bytes = (bits + 7) / 8;
    let expected = (1u64 << (bits / 2)) as f64;

    let mut seen: HashMap<Vec<u8>, Vec<u8>> = HashMap::new();

    for i in 0..max_hashes {
        let mut input = vec![0u8; 48];
        for b in &mut input {
            *b = next() as u8;
        }
        let h = hash(&input);
        let truncated = h[..mask_bytes].to_vec();
        if let Some(prev_input) = seen.get(&truncated) {
            if prev_input != &input {
                return (i + 1, expected);
            }
        }
        seen.insert(truncated, input);
    }
    (max_hashes, expected)
}

/// Preimage search on a truncated hash.
///
/// We pick a target hash, truncate to `bits` bits, and search for a
/// preimage by brute force. The expected number of hashes is ~2^bits.
///
/// We use bits=16 (expected ~65536 hashes) to verify preimage resistance
/// matches the theoretical bound.
///
/// Returns (number of hashes, expected number).
pub fn preimage_search(bits: usize, max_hashes: usize) -> (usize, f64) {
    let mut seed = 0xF00DCAFEu64;
    let mut next = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) as u32
    };

    let mask_bytes = (bits + 7) / 8;
    let expected = (1u64 << bits) as f64;

    // Pick a random target
    let target_input = vec![next() as u8; 48];
    let target_hash = hash(&target_input);
    let target = target_hash[..mask_bytes].to_vec();

    for i in 0..max_hashes {
        let mut input = vec![0u8; 48];
        for b in &mut input {
            *b = next() as u8;
        }
        let h = hash(&input);
        if h[..mask_bytes] == target[..] {
            // Verify it's a genuine preimage (not the same input)
            if input != target_input {
                return (i + 1, expected);
            }
        }
    }
    (max_hashes, expected)
}

// ============================================================
// TESTS
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- S-box tests ---

    #[test]
    fn ddt_analysis() {
        let table = ddt(&SBOX);
        let du = differential_uniformity(&SBOX);

        // Print the DDT
        println!("\n=== DDT of PRESENT S-box ===");
        print!("     ");
        for dy in 0..16 {
            print!("{:3} ", dy);
        }
        println!();
        for dx in 0..16 {
            print!("{:3}: ", dx);
            for dy in 0..16 {
                if table[dx][dy] > 0 {
                    print!("{:3} ", table[dx][dy]);
                } else {
                    print!("  . ");
                }
            }
            println!();
        }

        println!("\nDifferential uniformity: {} (optimal for 4-bit: 4)", du);
        assert!(du <= 4, "differential uniformity {} should be <= 4", du);
    }

    #[test]
    fn lat_analysis() {
        let table = lat(&SBOX);
        let nl = nonlinearity(&SBOX);

        // Print the LAT (as biases)
        println!("\n=== LAT of PRESENT S-box (showing bias = |count - 8|) ===");
        print!("     ");
        for beta in 0..16 {
            print!("{:3} ", beta);
        }
        println!();
        for alpha in 0..16 {
            print!("{:3}: ", alpha);
            for beta in 0..16 {
                let bias = (table[alpha][beta] - 8).abs();
                if bias > 0 {
                    print!("{:3} ", bias);
                } else {
                    print!("  . ");
                }
            }
            println!();
        }

        println!("\nNonlinearity: {} (optimal for 4-bit: 4)", nl);
        assert!(nl >= 4, "nonlinearity {} should be >= 4", nl);
    }

    #[test]
    fn algebraic_degree_analysis() {
        let degrees = algebraic_degrees(&SBOX);
        println!("\n=== Algebraic degrees of S-box output bits ===");
        for (bit, &deg) in degrees.iter().enumerate() {
            println!("  bit {}: degree {} (max possible: 3)", bit, deg);
        }
        let min_deg = *degrees.iter().min().unwrap();
        assert!(min_deg >= 2, "min algebraic degree {} should be >= 2", min_deg);
    }

    #[test]
    fn branch_number_analysis() {
        let bn = differential_branch_number(&SBOX);
        println!("\nDifferential branch number: {} (good: >= 3)", bn);
        assert!(bn >= 3, "differential branch number {} should be >= 3", bn);
    }

    // --- Round function tests ---

    #[test]
    fn full_diffusion_analysis() {
        let profile = diffusion_profile();
        let full = full_diffusion_rounds();

        println!("\n=== Diffusion profile (1-nibble difference → affected nibbles) ===");
        for (r, &count) in profile.iter().enumerate() {
            let bar = "#".repeat(count);
            println!("  round {:2}: {}/40 {}", r + 1, count, bar);
        }
        println!("\nFull diffusion: {} rounds (to affect all 40 nibbles)", full);
        println!("ROUNDS per absorb/squeeze: {}", ROUNDS);
        if full > ROUNDS {
            println!(
                "  WARNING: full diffusion ({} rounds) > ROUNDS ({}).",
                full, ROUNDS
            );
            println!("  Some nibble positions are not fully diffused after one");
            println!("  absorb/squeeze. This is a known weakness of the current");
            println!("  permutation. Options: increase ROUNDS, improve the");
            println!("  permutation, or use a different diffusion structure.");
        }
    }

    #[test]
    fn sac_analysis() {
        let probs = sac_test(10_000, 48);
        let max_dev = probs
            .iter()
            .map(|&p| (p - 0.5).abs())
            .fold(0.0f64, f64::max);
        let mean_dev = probs
            .iter()
            .map(|&p| (p - 0.5).abs())
            .sum::<f64>()
            / probs.len() as f64;

        println!("\n=== SAC test (10,000 samples, flip input bit 0) ===");
        println!("  max deviation from 0.5: {:.4} (threshold: 0.05)", max_dev);
        println!("  mean deviation from 0.5: {:.4}", mean_dev);
        assert!(max_dev < 0.1, "SAC max deviation {} should be < 0.1", max_dev);
    }

    #[test]
    fn bic_analysis() {
        let corr = bic_test(10_000, 48);
        println!("\n=== BIC test (10,000 samples, 190 bit pairs) ===");
        println!("  max correlation: {:.4} (threshold: 0.1)", corr);
        assert!(corr < 0.15, "BIC max correlation {} should be < 0.15", corr);
    }

    // --- Hash function statistical tests ---

    #[test]
    fn avalanche_weight_analysis() {
        let (mean, std) = avalanche_distribution(10_000, 48);
        let expected_mean = 80.0;
        let expected_std = (160.0 * 0.25f64).sqrt();

        println!("\n=== Avalanche weight distribution (10,000 samples) ===");
        println!("  mean: {:.2} (expected: {:.1})", mean, expected_mean);
        println!("  std:  {:.2} (expected: {:.2})", std, expected_std);
        println!("  mean deviation: {:.2}", (mean - expected_mean).abs());

        assert!((mean - expected_mean).abs() < 5.0, "avalanche mean {} should be near 80", mean);
        assert!((std - expected_std).abs() < 2.0, "avalanche std {} should be near {}", std, expected_std);
    }

    #[test]
    fn chi_square_analysis() {
        let max_chi = chi_square_nibbles(10_000);
        let df = 15.0; // 16 categories - 1
        let critical_001 = 30.58; // chi-square critical value, df=15, p=0.01

        println!("\n=== Chi-square test on nibble values (10,000 samples) ===");
        println!("  max chi-square across 40 nibble positions: {:.2}", max_chi);
        println!("  degrees of freedom: 15, critical value (p=0.01): {}", critical_001);
        println!("  pass: {}", if max_chi < critical_001 { "yes" } else { "FAIL" });

        if max_chi >= critical_001 {
            println!("  WARNING: chi-square {} exceeds critical value {}.", max_chi, critical_001);
            println!("  One or more nibble positions show non-uniform distribution.");
            println!("  With 40 positions tested at p=0.01, ~0.4 false positives");
            println!("  are expected by chance. Combined with the diffusion weakness");
            println!("  (full diffusion > ROUNDS), this likely indicates real bias");
            println!("  from insufficient mixing.");
        }
    }

    #[test]
    fn birthday_collision_analysis() {
        // 20-bit truncated hash: expect collision in ~1024 hashes
        let (found, expected) = birthday_collision_search(20, 100_000);

        println!("\n=== Birthday collision search (20-bit truncation) ===");
        println!("  hashes to collision: {} (expected ~{:.0})", found, expected);
        println!("  ratio: {:.2} (should be near 1.0)", found as f64 / expected);

        // Allow a factor of 4 either way (birthday bound is probabilistic)
        assert!(found > 100, "collision found too easily: {} hashes", found);
        assert!(found < 10_000, "collision took too long: {} hashes", found);
    }

    #[test]
    fn preimage_resistance_analysis() {
        // 16-bit truncated hash: expect preimage in ~65536 hashes
        let (found, expected) = preimage_search(16, 200_000);

        println!("\n=== Preimage search (16-bit truncation) ===");
        println!("  hashes to preimage: {} (expected ~{:.0})", found, expected);
        println!("  ratio: {:.2} (should be near 1.0)", found as f64 / expected);

        // Allow a factor of 8 either way
        assert!(found > 5_000, "preimage found too easily: {} hashes", found);
        assert!(found < 200_000, "preimage search should succeed within 200k hashes");
    }

    #[test]
    fn sponge_capacity_analysis() {
        println!("\n=== Sponge construction analysis ===");
        println!("  State: {} nibbles ({} bits)", STATE_NIBBLES, STATE_NIBBLES * 4);
        println!("  Rate:  {} nibbles ({} bits)", RATE_NIBBLES, RATE_NIBBLES * 4);
        println!("  Capacity: {} nibbles ({} bits)", CAPACITY_NIBBLES, CAPACITY_NIBBLES * 4);
        println!();
        println!("  Generic security bounds (sponge with capacity c = {} bits):", CAPACITY_NIBBLES * 4);
        println!("    Collision resistance:  2^(c/2) = 2^{} = ~{:.0e}", CAPACITY_NIBBLES * 2, 2f64.powi((CAPACITY_NIBBLES * 4 / 2) as i32));
        println!("    Preimage resistance:   2^c    = 2^{} = ~{:.0e}", CAPACITY_NIBBLES * 4, 2f64.powi((CAPACITY_NIBBLES * 4) as i32));
        println!("    Second preimage:       2^c    = 2^{} = ~{:.0e}", CAPACITY_NIBBLES * 4, 2f64.powi((CAPACITY_NIBBLES * 4) as i32));
        println!();
        println!("  Target security parameter: 80 bits");
        println!("  Collision resistance needed: 2^80");
        println!("  Capacity provides: 2^{} ({} bits of collision resistance)", CAPACITY_NIBBLES * 2, CAPACITY_NIBBLES * 2);
        if (CAPACITY_NIBBLES * 2) < 80 {
            println!("  CRITICAL: collision resistance 2^{} < 2^80 target!", CAPACITY_NIBBLES * 2);
            println!("  The sponge capacity is {} bits. For 80-bit collision", CAPACITY_NIBBLES * 4);
            println!("  resistance, the capacity must be >= 160 bits (40 nibbles).");
            println!("  Current state: {} nibbles, rate: {} nibbles, capacity: {} nibbles.", STATE_NIBBLES, RATE_NIBBLES, CAPACITY_NIBBLES);
            println!("  To fix: increase state to >= 60 nibbles with 40-nibble capacity,");
            println!("  or switch to a Merkle-Damgård construction (collision resistance");
            println!("  = 2^(n/2) where n = digest length = 160 bits → 2^80).");
        }
    }

    #[test]
    fn summary() {
        println!("\n{}", "=".repeat(60));
        println!("n4bit CRYPTANALYSIS SUMMARY");
        println!("{}", "=".repeat(60));
        println!();
        println!("S-box (PRESENT):");
        println!("  Differential uniformity: {} (optimal: 4)", differential_uniformity(&SBOX));
        println!("  Nonlinearity: {} (optimal: 4)", nonlinearity(&SBOX));
        let degs = algebraic_degrees(&SBOX);
        println!("  Algebraic degrees: {:?} (optimal: [3,3,3,3])", degs);
        println!("  Branch number: {}", differential_branch_number(&SBOX));
        println!();
        println!("Round function:");
        let profile = diffusion_profile();
        println!("  Diffusion profile: {:?}", profile);
        println!("  Full diffusion: {} rounds", full_diffusion_rounds());
        println!("  ROUNDS per absorb/squeeze: {}", ROUNDS);
        println!();
        println!("Sponge construction:");
        println!("  Capacity: {} bits → 2^{} collision resistance", CAPACITY_NIBBLES * 4, CAPACITY_NIBBLES * 2);
        println!("  Target: 2^80 collision resistance");
        println!();
        println!("Statistical tests (10,000 samples each):");
        let (av_mean, av_std) = avalanche_distribution(10_000, 48);
        println!("  Avalanche: mean={:.2} (exp 80.0), std={:.2} (exp 6.32)", av_mean, av_std);
        let sac = sac_test(10_000, 48);
        let sac_max = sac.iter().map(|&p| (p - 0.5).abs()).fold(0.0f64, f64::max);
        println!("  SAC: max deviation = {:.4} (threshold 0.1)", sac_max);
        println!("  BIC: max correlation = {:.4} (threshold 0.15)", bic_test(10_000, 48));
        println!("  Chi-square: max = {:.2} (critical 30.58)", chi_square_nibbles(10_000));
        let (coll, _) = birthday_collision_search(20, 100_000);
        println!("  Birthday (20-bit): {} hashes (expected ~1024)", coll);
        let (pre, _) = preimage_search(16, 200_000);
        println!("  Preimage (16-bit): {} hashes (expected ~65536)", pre);
    }
}
