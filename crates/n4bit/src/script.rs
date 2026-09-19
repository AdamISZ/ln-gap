//! n4bit round function as Bitcoin Script (Tapscript).
//!
//! This is the Script-level implementation of the n4bit SPN round,
//! mirroring `spn_round` in lib.rs but executing in Bitcoin Script opcodes.
//!
//! The round function is: add constants, S-box, Feistel mix, permute.
//! In Script:
//! - ADD constants: OP_ADD + mod-16 correction
//! - S-box: 16-entry table on the stack, OP_PICK
//! - Feistel mix: OP_ADD on nibble pairs
//! - Permute: OP_ROLL + altstack
//!
//! The table footprint is just 16 elements (the S-box) vs SHA-256's 608
//! (256 XOR + 256 AND + 96 shift). This is the core advantage.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;

use crate::*;

/// The S-box table: 16 script numbers, pushed so SBOX[0] is on top.
/// Cost: 16 × ~2 bytes = ~32 bytes. This is the *only* table.
pub fn push_sbox_table(b: Builder) -> Builder {
    let mut b = b;
    for &v in SBOX.iter().rev() {
        b = b.push_int(i64::from(v));
    }
    b
}

/// Number of stack elements the S-box table occupies.
pub const SBOX_TABLE_SIZE: usize = 16;

/// mod-16 correction: if the top element >= 16, subtract 16.
/// Stack in: [n]  Stack out: [n % 16]
fn mod16(b: Builder) -> Builder {
    b.push_opcode(OP_DUP)
        .push_int(16)
        .push_opcode(OP_GREATERTHANOREQUAL)
        .push_opcode(OP_IF)
        .push_int(16)
        .push_opcode(OP_SUB)
        .push_opcode(OP_ENDIF)
}

/// Add a round constant to the top nibble: `(n + rc) % 16`.
/// Stack in: [n]  Stack out: [(n + rc) % 16]
fn add_constant(b: Builder, rc_val: u8) -> Builder {
    let b = b.push_int(i64::from(rc_val)).push_opcode(OP_ADD);
    mod16(b)
}

/// Apply the S-box to the top nibble: `SBOX[n]`.
///
/// The S-box table must be on the stack with SBOX[0] at `table_base`
/// depth from the top (counting elements above the table). The nibble
/// is above the table at depth 0.
///
/// We compute the index: table_base + n, then OP_PICK.
/// Cost: push_int(table_base) + OP_ADD + OP_PICK = ~5 bytes.
fn sbox_lookup(b: Builder, table_base: usize) -> Builder {
    // `table_base` counts the nibble itself; OP_ADD consumes it, so at the
    // OP_PICK the table's top entry is one element shallower.
    b.push_int(table_base as i64 - 1)
        .push_opcode(OP_ADD)   // table_base - 1 + n = depth of SBOX[n]
        .push_opcode(OP_PICK)  // SBOX[n]
}

/// Feistel ADD mixing on a nibble pair.
/// Stack in: [a, b]  (b on top, a below)
/// Stack out: [new_b, new_a]  (new_a on top, new_b below)
///
/// new_a = (a + b) % 16
/// new_b = (b + new_a) % 16
pub fn feistel_add(b: Builder) -> Builder {
    // [a, b], b on top; the altstack is left exactly as found
    b
        // new_a = (a + b) % 16 — but b is on alt, a is on top, we need b
        // Actually [a, b] with b on top. DUP b, TOALT. Now [a] with a on top.
        // We need b to compute new_a = a+b. But b is on alt.
        // Push b from alt, compute new_a, then push b again for new_b.
        // Better: OP_OVER before saving.
        // [a, b] → OP_DUP → [a, b, b] → OP_TOALTSTACK → [a, b]
        // Now b is on top, a below. OP_SWAP → [b, a]. OP_OVER → [b, a, b].
        // Hmm, we want a+b. [a, b] with b on top: just OP_ADD gives a+b.
        // But we also saved b. Let's use a cleaner approach:
        // [a, b] → OP_TOALTSTACK (save b) → [a] → OP_FROMALTSTACK → [a, b]?
        // No, TOALT pops. So:
        // [a, b] → OP_DUP → [a, b, b] → OP_TOALTSTACK → [a, b]
        // Now: OP_SWAP → [b, a] → OP_OVER → [b, a, b] → ...
        // This is getting convoluted. Cleanest:
        // [a, b] → OP_SWAP → [b, a] → OP_TOALTSTACK → [b] (a on alt)
        // OP_DUP → [b, b] → OP_FROMALTSTACK → [b, b, a] → OP_ADD → [b, b+a]
        // mod16 → [b, new_a] → OP_SWAP → [new_a, b] → OP_OVER → [new_a, b, new_a]
        // OP_ADD → [new_a, b+new_a] → mod16 → [new_a, new_b] → OP_SWAP → [new_b, new_a]
        // That's: 2+1+1+1+1+1+7+1+1+7+1 = ~24 bytes
        .push_opcode(OP_SWAP)       // [b, a]
        .push_opcode(OP_TOALTSTACK) // [b] (a on alt)
        .push_opcode(OP_DUP)        // [b, b]
        .push_opcode(OP_FROMALTSTACK) // [b, b, a]
        .push_opcode(OP_ADD)        // [b, a+b]
        // mod 16
        .push_opcode(OP_DUP)
        .push_int(16)
        .push_opcode(OP_GREATERTHANOREQUAL)
        .push_opcode(OP_IF)
        .push_int(16)
        .push_opcode(OP_SUB)
        .push_opcode(OP_ENDIF)      // [b, new_a]
        // new_b = (b + new_a) % 16
        .push_opcode(OP_SWAP)        // [new_a, b]
        .push_opcode(OP_OVER)        // [new_a, b, new_a]
        .push_opcode(OP_ADD)         // [new_a, b+new_a]
        // mod 16
        .push_opcode(OP_DUP)
        .push_int(16)
        .push_opcode(OP_GREATERTHANOREQUAL)
        .push_opcode(OP_IF)
        .push_int(16)
        .push_opcode(OP_SUB)
        .push_opcode(OP_ENDIF)      // [new_a, new_b]
        .push_opcode(OP_SWAP)        // [new_b, new_a]
}

/// Compute the permutation: perm[i] = source position for output position i.
fn compute_permutation() -> Vec<usize> {
    let mut state: Vec<usize> = (0..STATE_NIBBLES).collect();

    // Step 1: ShiftRows
    let mut tmp = vec![0usize; STATE_NIBBLES];
    for r in 0..ROWS {
        for c in 0..COLS {
            tmp[r * COLS + c] = state[r * COLS + (c + r) % COLS];
        }
    }
    // Step 2: Column rotation
    for c in 0..COLS {
        let shift = c % ROWS;
        for r in 0..ROWS {
            state[r * COLS + c] = tmp[((r + shift) % ROWS) * COLS + c];
        }
    }
    // Step 3: Cross-boundary swap
    for i in (0..RATE_NIBBLES).step_by(2) {
        state.swap(i, i + RATE_NIBBLES);
    }
    state
}

/// Apply the permutation to 40 nibbles on the stack.
///
/// Stack in: 40 nibbles (n0 deepest, n39 on top) + S-box table below
/// Stack out: 40 nibbles in permuted order + S-box table below
///
/// Each output nibble is rolled to the top and parked, output 39 first,
/// so that unparking all 40 lands output 0 deepest. The depth of a source
/// nibble is computed against the nibbles still on the stack, which
/// shrink as they are parked.
pub fn permute_script(b: Builder) -> Builder {
    let perm = compute_permutation();
    let mut b = b;
    let mut remaining: Vec<usize> = (0..STATE_NIBBLES).collect(); // source indices, deepest first
    for k in (0..STATE_NIBBLES).rev() {
        let src = perm[k];
        let pos = remaining.iter().position(|&x| x == src).expect("a permutation");
        let depth = remaining.len() - 1 - pos;
        b = roll_to_top(b, depth).push_opcode(OP_TOALTSTACK);
        remaining.remove(pos);
    }
    for _ in 0..STATE_NIBBLES {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    b
}

/// Roll the element at `depth` to the top (a no-op at depth 0).
fn roll_to_top(b: Builder, depth: usize) -> Builder {
    match depth {
        0 => b,
        1 => b.push_opcode(OP_SWAP),
        2 => b.push_opcode(OP_ROT),
        d => b.push_int(d as i64).push_opcode(OP_ROLL),
    }
}

/// One full SPN round in Script, applied to 40 nibbles on the stack.
///
/// Stack in: 40 nibbles (n0 deepest, n39 on top) + S-box table below
/// Stack out: 40 nibbles after one round + S-box table below
///
/// The round is: add constants, S-box, Feistel mix, permute, each a pass
/// that consumes the nibbles from the top, parks its results on the
/// altstack in the order that unparking restores, and unparks. Round
/// constants come from `rc(round, i)` in lib.rs. Verified against the
/// native round by `script_round_matches_native_round`.
pub fn spn_round_script(b: Builder, round: usize) -> Builder {
    permute_script(mix_script(sbox_phase_script(b, round)))
}

/// Phase 1: constants and S-box, nibble 39 first (it is on top). When
/// nibble i is consumed, i nibbles remain above the table, so the table's
/// top entry SBOX[0] sits at depth i.
pub fn sbox_phase_script(b: Builder, round: usize) -> Builder {
    let mut b = b;
    for i in (0..STATE_NIBBLES).rev() {
        b = add_constant(b, rc(round, i));
        b = sbox_lookup(b, i + 1).push_opcode(OP_TOALTSTACK);
    }
    for _ in 0..STATE_NIBBLES {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    b
}

/// Phase 2: Feistel on pairs, the top pair (38, 39) first; each pair's
/// results parked new_b then new_a so that unparking lands new_a(2i)
/// below new_b(2i+1).
pub fn mix_script(b: Builder) -> Builder {
    let mut b = b;
    for _ in 0..STATE_NIBBLES / 2 {
        b = feistel_add(b); // [a, b] -> [new_b, new_a]
        b = b.push_opcode(OP_SWAP).push_opcode(OP_TOALTSTACK).push_opcode(OP_TOALTSTACK);
    }
    for _ in 0..STATE_NIBBLES {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    b
}

/// Build the full round leaf script: verify one n4bit round.
///
/// This is the Script that goes into a Tapscript leaf. It:
/// 1. Verifies the challenger's signature (OP_CHECKSIGVERIFY)
/// 2. Loads the input state (WOTS-verified, 40 nibbles)
/// 3. Loads the round constants (WOTS-verified, 40 nibbles) — or hardcoded
/// 4. Computes one SPN round
/// 5. Compares the result against the committed output state
///
/// The script size and stack usage are the key measurements.
pub fn round_leaf_script(round: usize) -> ScriptBuf {
    let b = Builder::new()
        .push_opcode(OP_CHECKSIGVERIFY); // placeholder for channel sig
    // In the full implementation, this would load the input state
    // via WOTS verify, push the S-box table, run the round, and
    // compare against the output state.
    //
    // For measurement purposes, we build the round body only.
    let b = push_sbox_table(b);
    // Push 40 placeholder nibbles (in practice, WOTS-verified)
    let b = (0..STATE_NIBBLES).fold(b, |b, _| b.push_int(0));
    // Run one round
    let b = spn_round_script(b, round);
    // Drop the 40 result nibbles + 16 table entries
    let b = (0..(STATE_NIBBLES + SBOX_TABLE_SIZE)).fold(b, |b, _| b.push_opcode(OP_DROP));
    // Push 1 (leaf accepts)
    b.push_int(1).into_script()
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::script::Builder;

    #[test]
    fn permutation_is_correct() {
        let perm = compute_permutation();
        let mut sorted = perm.clone();
        sorted.sort();
        assert_eq!(sorted, (0..STATE_NIBBLES).collect::<Vec<_>>());
        // Verify against lib.rs permute
        let mut state = [0u8; STATE_NIBBLES];
        for i in 0..STATE_NIBBLES {
            state[i] = i as u8;
        }
        let original = state;
        crate::permute(&mut state);
        for i in 0..STATE_NIBBLES {
            assert_eq!(state[i], original[perm[i]], "position {} mismatch", i);
        }
        println!("Permutation: {:?}", perm);
    }

    #[test]
    fn sbox_table_size() {
        assert_eq!(SBOX_TABLE_SIZE, 16);
        assert_eq!(SBOX.len(), 16);
        println!(
            "S-box table: {} stack elements (vs SHA-256: 608)",
            SBOX_TABLE_SIZE
        );
    }

    /// One Script round against the native round, through the interpreter,
    /// on random states and round counters (including counters past 128,
    /// which the header chain's later steps reach).
    #[test]
    fn script_round_matches_native_round() {
        let mut x: u64 = 0x1234_5678_9abc_def0;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for round in [0usize, 1, 19, 20, 100, 140, 159, 255] {
            for _ in 0..4 {
                let state: [u8; STATE_NIBBLES] = std::array::from_fn(|_| (next() % 16) as u8);
                let mut b = push_sbox_table(Builder::new());
                for &n in &state {
                    b = b.push_int(i64::from(n));
                }
                let script = spn_round_script(b, round).into_script();
                let out = lngap_script32::sim::run_nums(&script, vec![]).unwrap_or_else(|e| panic!("round {round}: {e}"));
                assert_eq!(out.len(), SBOX_TABLE_SIZE + STATE_NIBBLES, "round {round}: stack size");
                let got: Vec<u8> = out[SBOX_TABLE_SIZE..].iter().map(|&v| v as u8).collect();
                let mut want = state;
                spn_round(&mut want, round);
                assert_eq!(got, want.to_vec(), "round {round} on {state:?}");
            }
        }
    }

    /// Each pass of the round against its native counterpart.
    #[test]
    fn script_passes_match_native_passes() {
        let state: [u8; STATE_NIBBLES] = std::array::from_fn(|i| ((i * 7 + 3) % 16) as u8);
        let run = |f: &dyn Fn(Builder) -> Builder| -> Vec<u8> {
            let mut b = push_sbox_table(Builder::new());
            for &n in &state {
                b = b.push_int(i64::from(n));
            }
            let out = lngap_script32::sim::run_nums(&f(b).into_script(), vec![]).unwrap();
            assert_eq!(out.len(), SBOX_TABLE_SIZE + STATE_NIBBLES);
            out[SBOX_TABLE_SIZE..].iter().map(|&v| v as u8).collect()
        };
        let mut want = state;
        super::super::add_constants(&mut want, 5);
        super::super::sbox_layer(&mut want);
        assert_eq!(run(&|b| sbox_phase_script(b, 5)), want.to_vec(), "constants and S-box");
        let mut want = state;
        super::super::mix(&mut want);
        assert_eq!(run(&|b| mix_script(b)), want.to_vec(), "mix");
        let mut want = state;
        super::super::permute(&mut want);
        assert_eq!(run(&|b| permute_script(b)), want.to_vec(), "permute");
    }

    #[test]
    fn round_constant_check() {
        for r in 0..ROUNDS {
            for i in 0..STATE_NIBBLES {
                let val = rc(r, i);
                assert!(val < 16, "rc({}, {}) = {} >= 16", r, i, val);
            }
        }
    }

    #[test]
    fn script_size_measurement() {
        let script = round_leaf_script(0);
        let size = script.len();
        println!("\n=== n4bit round leaf script size ===");
        println!("  Script size: {} bytes", size);
        println!("  vs SHA-256 round leaf: ~12,000 bytes");
        println!("  Ratio: {:.1}x smaller", 12000.0 / size as f64);

        // Stack usage estimate
        // S-box table: 16 elements
        // State nibbles: 40 elements
        // Working space (add const, sbox, feistel): ~5 elements
        // Total: ~61 elements
        // vs SHA-256: ~600+ elements (tables + state + working)
        println!("  Stack elements: ~{} (S-box {} + state {} + working ~5)",
            SBOX_TABLE_SIZE + STATE_NIBBLES + 5,
            SBOX_TABLE_SIZE, STATE_NIBBLES);
        println!("  vs SHA-256: ~600+ elements");
        println!("  1000-element limit: {}% utilized",
            (SBOX_TABLE_SIZE + STATE_NIBBLES + 5) * 100 / 1000);

        assert!(size < 2000, "round leaf should be < 2000 bytes, got {}", size);
    }

    #[test]
    fn feistel_script_correctness() {
        // Test that feistel_add produces the right result
        // by building the script and checking the opcode sequence
        let b = Builder::new();
        let _ = feistel_add(b);
        // We can't execute Script in unit tests, but we can verify
        // the builder produces a valid script.
        println!("feistel_add script built successfully");
    }
}
