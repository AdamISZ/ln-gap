//! A 4-bit-word SPN sponge hash function using ADD for key mixing.
//!
//! Design rationale: see docs/planning/hermes-research/SCRIPT_NATIVE_HASH.md.
//! In short, Bitcoin Script's only arithmetic is OP_ADD/OP_SUB on 4-byte
//! CScriptNums; XOR is a disabled opcode that must be emulated with a 256-entry
//! lookup table (256 stack elements). By using a 4-bit S-box (16-entry table, 16
//! stack elements) and ADD for key mixing, the per-round Script leaf is projected
//! at ~600 B vs SHA-256's ~12 KB, and the fixed table overhead drops from 608 to
//! 16 stack elements.
//!
//! This is a TOY hash for PoC prototyping. No security claim is made; the
//! cryptanalysis is deferred (see SCRIPT_NATIVE_HASH.md §5.3). The point is to
//! have the right structural shape for measuring Script costs, not to be
//! collision-resistant yet.
//!
//! # Construction
//!
//! Sponge with:
//! - State: 40 nibbles (160 bits), arranged as 5 rows × 8 columns.
//! - Rate: 20 nibbles (80 bits, 10 bytes).
//! - Capacity: 20 nibbles (80 bits, 10 bytes).
//! - Digest: 160 bits (20 bytes) = two squeezes of the rate part.
//!
//! # Round function (one SPN round)
//!
//! 1. **ADD key mixing**: add a round constant to each nibble (mod 16).
//! 2. **S-box**: apply a 4-bit S-box (PRESENT's) to each nibble.
//! 3. **Permutation**: ShiftRows (row *i* shifted left by *i*) + column
//!    rotation (column *j* rotated up by *j* mod 5).
//!
//! # Sponge operation
//!
//! - **Absorb**: for each 10-byte block, ADD its nibbles to state[0..20] (mod 16)
//!   and apply `ROUNDS` SPN rounds.
//! - **Pad**: after the last block, ADD 1 to state[0] and apply `ROUNDS` rounds.
//! - **Squeeze**: output state[0..20] (10 bytes), apply `ROUNDS` rounds, output
//!   state[0..20] again (10 bytes) = 20 bytes total.

pub mod cryptanalysis;
pub mod script;

/// PRESENT's 4-bit S-box (ISO/IEC 29192-2).
pub const SBOX: [u8; 16] = [0xC, 0x5, 0x6, 0xB, 0x9, 0x0, 0xA, 0xD, 0x3, 0xE, 0xF, 0x8, 0x4, 0x7, 0x1, 0x2];

/// Inverse S-box (for potential future use).
pub const SBOX_INV: [u8; 16] = {
    let mut inv = [0u8; 16];
    let mut i = 0;
    while i < 16 {
        inv[SBOX[i] as usize] = i as u8;
        i += 1;
    }
    inv
};

/// State size in nibbles (5 rows × 8 columns = 160 bits).
pub const STATE_NIBBLES: usize = 40;

/// Rate in nibbles (80 bits = 10 bytes).
pub const RATE_NIBBLES: usize = 20;

/// Capacity in nibbles (80 bits = 10 bytes).
pub const CAPACITY_NIBBLES: usize = STATE_NIBBLES - RATE_NIBBLES;

/// SPN rounds per sponge absorption/squeeze.
pub const ROUNDS: usize = 20;

/// Digest size in bytes (160 bits).
pub const DIGEST_BYTES: usize = 20;

/// Digest type: a 20-byte array.
pub type Digest = [u8; DIGEST_BYTES];

/// The internal state: 40 nibbles, each 0–15.
type State = [u8; STATE_NIBBLES];

/// Row/column layout: nibble at index `i` is at row `i / 8`, col `i % 8`.
const COLS: usize = 8;
const ROWS: usize = 5;

/// Round constant for round `r`, position `i`.
fn rc(r: usize, i: usize) -> u8 {
    ((r * 7 + i * 3 + 1) % 16) as u8
}

/// Apply the S-box to every nibble in place.
fn sbox_layer(state: &mut State) {
    for n in state.iter_mut() {
        *n = SBOX[*n as usize];
    }
}

/// ADD round constants to every nibble (mod 16), in place.
fn add_constants(state: &mut State, round: usize) {
    for (i, n) in state.iter_mut().enumerate() {
        *n = (*n + rc(round, i)) % 16;
    }
}

/// Feistel ADD mixing on nibble pairs: for each pair (2i, 2i+1):
///   new[2i]   = (a + b) % 16
///   new[2i+1] = (b + new[2i]) % 16
///
/// This is invertible: given new, b = (new[2i+1] - new[2i]) % 16,
/// a = (new[2i] - b) % 16. A difference in either input affects both
/// outputs, doubling the number of affected positions each round.
fn mix(state: &mut State) {
    for i in 0..STATE_NIBBLES / 2 {
        let a = state[2 * i];
        let b = state[2 * i + 1];
        let new_a = (a + b) % 16;
        let new_b = (b + new_a) % 16;
        state[2 * i] = new_a;
        state[2 * i + 1] = new_b;
    }
}

/// Permutation: ShiftRows + column rotation + cross-boundary swap, in place.
///
/// The cross-boundary swap (swapping rate/capacity nibble pairs) is essential:
/// without it, the column rotation can trap changes in the capacity rows
/// (shifts 0 and 4 cycle between rows 3–4 without reaching the rate). The swap
/// guarantees that every round exchanges half the rate with the capacity.
fn permute(state: &mut State) {
    // Step 1: ShiftRows — row r shifted left by r.
    let mut tmp = [0u8; STATE_NIBBLES];
    for r in 0..ROWS {
        for c in 0..COLS {
            tmp[r * COLS + c] = state[r * COLS + (c + r) % COLS];
        }
    }
    // Step 2: Column rotation — column c rotated up by c % ROWS.
    for c in 0..COLS {
        let shift = c % ROWS;
        for r in 0..ROWS {
            state[r * COLS + c] = tmp[((r + shift) % ROWS) * COLS + c];
        }
    }
    // Step 3: Cross-boundary swap — swap rate[i] with capacity[i] for even i.
    // This is a bijection (pure permutation) that guarantees rate ↔ capacity
    // diffusion every round.
    for i in (0..RATE_NIBBLES).step_by(2) {
        state.swap(i, i + RATE_NIBBLES);
    }
}

/// One SPN round: add constants, S-box, mix, permute. Transforms state in place.
///
/// The mix step (Feistel ADD on nibble pairs) is what creates diffusion: a
/// difference at one nibble propagates to its paired nibble, doubling the
/// number of affected positions each round. Without it, the S-box + permutation
/// can only move differences, not create them, giving ~0-bit avalanche.
pub fn spn_round(state: &mut State, round: usize) {
    add_constants(state, round);
    sbox_layer(state);
    mix(state);
    permute(state);
}

/// Apply `ROUNDS` SPN rounds to the state.
fn apply_rounds(state: &mut State, starting_round: usize) {
    for r in 0..ROUNDS {
        spn_round(state, starting_round + r);
    }
}

/// Convert bytes to nibbles (high nibble first, little-endian byte order).
fn bytes_to_nibbles(bytes: &[u8]) -> Vec<u8> {
    let mut nibbles = Vec::with_capacity(bytes.len() * 2);
    for &b in bytes {
        nibbles.push((b >> 4) & 0xF);
        nibbles.push(b & 0xF);
    }
    nibbles
}

/// Convert 40 nibbles to 20 bytes (high nibble first).
fn nibbles_to_bytes(nibbles: &[u8]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(nibbles.len() / 2);
    for chunk in nibbles.chunks(2) {
        bytes.push((chunk[0] << 4) | chunk[1]);
    }
    bytes
}

/// Split nibbles into rate blocks of `RATE_NIBBLES` each, padding the last
/// with zeros.
fn rate_blocks(nibbles: &[u8]) -> Vec<[u8; RATE_NIBBLES]> {
    let mut blocks = Vec::new();
    let mut i = 0;
    while i < nibbles.len() {
        let mut block = [0u8; RATE_NIBBLES];
        let end = (i + RATE_NIBBLES).min(nibbles.len());
        block[..end - i].copy_from_slice(&nibbles[i..end]);
        blocks.push(block);
        i += RATE_NIBBLES;
    }
    if blocks.is_empty() {
        blocks.push([0u8; RATE_NIBBLES]);
    }
    blocks
}

/// Hash an arbitrary-length input to a 160-bit (20-byte) digest.
pub fn hash(input: &[u8]) -> Digest {
    let nibbles = bytes_to_nibbles(input);
    let blocks = rate_blocks(&nibbles);

    // Initialize state to zeros.
    let mut state = [0u8; STATE_NIBBLES];

    // Absorb.
    let mut round_counter = 0;
    for block in &blocks {
        // ADD block nibbles to the rate part (mod 16).
        for i in 0..RATE_NIBBLES {
            state[i] = (state[i] + block[i]) % 16;
        }
        apply_rounds(&mut state, round_counter);
        round_counter += ROUNDS;
    }

    // Padding: ADD 1 to state[0] and apply rounds.
    state[0] = (state[0] + 1) % 16;
    apply_rounds(&mut state, round_counter);
    round_counter += ROUNDS;

    // Squeeze: output rate, permute, output rate again.
    let mut output_nibbles = Vec::with_capacity(STATE_NIBBLES);
    output_nibbles.extend_from_slice(&state[..RATE_NIBBLES]);
    apply_rounds(&mut state, round_counter);
    output_nibbles.extend_from_slice(&state[..RATE_NIBBLES]);

    let bytes = nibbles_to_bytes(&output_nibbles);
    let mut digest = [0u8; DIGEST_BYTES];
    digest.copy_from_slice(&bytes);
    digest
}

/// Check whether a digest meets a target (digest <= target, big-endian
/// comparison). This mirrors the LeTarget predicate in the claim model but
/// in native code.
pub fn meets_target(digest: &Digest, target: &[u8; DIGEST_BYTES]) -> bool {
    for i in 0..DIGEST_BYTES {
        if digest[i] != target[i] {
            return digest[i] < target[i];
        }
    }
    true
}

/// Convert a number of leading zero bits to a 20-byte target (big-endian).
pub fn target_from_difficulty(bits: u32) -> [u8; DIGEST_BYTES] {
    let mut target = [0u8; DIGEST_BYTES];
    let full_bytes = (bits / 8) as usize;
    let remaining_bits = bits % 8;
    if full_bytes < DIGEST_BYTES {
        target[full_bytes] = (1u8 << (8 - remaining_bits)) - 1;
        for i in full_bytes + 1..DIGEST_BYTES {
            target[i] = 0xFF;
        }
    }
    target
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sbox_is_permutation() {
        let mut seen = [false; 16];
        for &s in &SBOX {
            assert!(!seen[s as usize], "S-box not a permutation: {} appears twice", s);
            seen[s as usize] = true;
        }
        assert!(seen.iter().all(|&x| x), "S-box not surjective");
    }

    #[test]
    fn sbox_inv_is_correct() {
        for x in 0..16u8 {
            assert_eq!(SBOX_INV[SBOX[x as usize] as usize], x);
        }
    }

    #[test]
    fn permute_is_permutation() {
        let mut state = [0u8; STATE_NIBBLES];
        for i in 0..STATE_NIBBLES {
            state[i] = (i % 16) as u8;
        }
        let original = state;
        permute(&mut state);
        // Check it's a permutation: every value appears the same number of times
        let mut counts = [0u8; 16];
        for &n in &state {
            counts[n as usize] += 1;
        }
        for i in 0..16 {
            let expected = original.iter().filter(|&&x| x == i as u8).count() as u8;
            assert_eq!(counts[i as usize], expected, "value {} count changed", i);
        }
    }

    #[test]
    fn hash_empty() {
        let h = hash(&[]);
        // Non-zero digest for empty input (sponge with padding)
        assert_ne!(h, [0u8; DIGEST_BYTES]);
    }

    #[test]
    fn hash_deterministic() {
        let input = b"hello world";
        assert_eq!(hash(input), hash(input));
    }

    #[test]
    fn hash_different_inputs() {
        let a = hash(b"alice");
        let b = hash(b"bob");
        assert_ne!(a, b, "different inputs must hash differently");
    }

    #[test]
    fn hash_avalanche() {
        // A one-bit change in the input should change many output bits
        let input1 = [0x48u8; 48]; // 48-byte header
        let mut input2 = input1;
        input2[0] ^= 1; // flip one bit
        let h1 = hash(&input1);
        let h2 = hash(&input2);
        let mut diff_bits = 0;
        for i in 0..DIGEST_BYTES {
            diff_bits += (h1[i] ^ h2[i]).count_ones();
        }
        // With 160 bits of output, expect ~80 bits to change (50% avalanche)
        assert!(diff_bits > 40, "avalanche too weak: {} bits changed out of 160", diff_bits);
    }

    #[test]
    fn hash_header_size() {
        // 48-byte header (the actual use case)
        let header = [0xABu8; 48];
        let h = hash(&header);
        assert_eq!(h.len(), DIGEST_BYTES);
    }

    #[test]
    fn hash_entry_size() {
        // 64-byte entry (the names registry entry size)
        let entry = [0xCDu8; 64];
        let h = hash(&entry);
        assert_eq!(h.len(), DIGEST_BYTES);
    }

    #[test]
    fn meets_target_5bits() {
        let target = target_from_difficulty(5);
        // 5 leading zero bits: target = 0x07FF...FF
        assert_eq!(target[0], 0x07);
        assert_eq!(target[1], 0xFF);

        // A digest below the target
        let mut d_low = [0u8; DIGEST_BYTES];
        d_low[0] = 0x03;
        assert!(meets_target(&d_low, &target));

        // A digest above the target
        let mut d_high = [0u8; DIGEST_BYTES];
        d_high[0] = 0x08;
        assert!(!meets_target(&d_high, &target));

        // A digest at the target
        let mut d_eq = [0u8; DIGEST_BYTES];
        d_eq[0] = 0x07;
        d_eq[1] = 0xFF;
        for i in 2..DIGEST_BYTES {
            d_eq[i] = 0xFF;
        }
        assert!(meets_target(&d_eq, &target));
    }

    #[test]
    fn pow_mining_loop() {
        // Simulate mining: find a nonce such that hash(header) <= target
        let target = target_from_difficulty(5);
        let mut header = [0u8; 48];
        // Fill with some fixed data (prev, root, height)
        header[0..20].copy_from_slice(&[0xAA; 20]);
        header[20..40].copy_from_slice(&[0xBB; 20]);
        header[40..44].copy_from_slice(&100u32.to_le_bytes());

        let mut nonce = 0u32;
        loop {
            header[44..48].copy_from_slice(&nonce.to_le_bytes());
            let h = hash(&header);
            if meets_target(&h, &target) {
                break;
            }
            nonce += 1;
            assert!(nonce < 100_000, "mining took too long for 5-bit difficulty");
        }
        // Verify
        header[44..48].copy_from_slice(&nonce.to_le_bytes());
        let h = hash(&header);
        assert!(meets_target(&h, &target), "mined nonce does not meet target");
    }

    #[test]
    fn print_test_vectors() {
        // Test vectors for cross-checking the Script implementation later
        let h_empty = hash(&[]);
        let h_48 = hash(&[0xABu8; 48]);
        let h_64 = hash(&[0xCDu8; 64]);
        println!("n4bit(empty) = {}", hex::encode(h_empty));
        println!("n4bit(48×0xAB) = {}", hex::encode(h_48));
        println!("n4bit(64×0xCD) = {}", hex::encode(h_64));
    }
}
