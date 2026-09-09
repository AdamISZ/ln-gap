//! One SHA-256 compression as a Script: midstate in, midstate out.
//! Adapted from BitVM's `bitvm/src/hash/sha256_u4.rs` (MIT): the code path
//! it uses for chunks after the first, which takes the running state from
//! the altstack, with a prologue that puts the input state there.
//!
//! Stack in (top first): 64 state nibbles (digest layout: word a first,
//! high nibble first, so the *last* nibble is on top), then 128 block
//! nibbles (message order, last nibble on top).
//! Stack out: 64 nibbles of the new state, same layout.

use bitvm::hash::sha256_u4::{calculate_s, ch_calculation, maj_calculation, schedule_iteration};
use bitvm::treepp::{script, Script};
#[allow(unused_imports)]
use bitcoin_script;
use bitvm::u4::u4_add::*;
use bitvm::u4::u4_logic::*;
use bitvm::u4::u4_rot::*;
use bitvm::u4::u4_std::*;

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

fn get_extra_pos(i: u32) -> u32 {
    (i - 16) * 8
}
fn get_pos_var(name: char) -> u32 {
    let i = match name {
        'a' => 0,
        'b' => 1,
        'c' => 2,
        'd' => 3,
        'e' => 4,
        'f' => 5,
        'g' => 6,
        'h' => 7,
        _ => 0,
    };
    let top = 8 * 8;
    let base = top - 8;
    base - i * 8
}
fn get_full_w_pos(top_table: u32, i: u32) -> u32 {
    top_table - (i + 1) * 8
}

pub fn sha256_compress_u4(use_add_table: bool) -> Script {
    let sched_size = 128;
    let rrot_size = 16 * 5;
    let half_logic_size = 136 + 16;
    let mut tables_size = rrot_size + half_logic_size;
    if use_add_table {
        tables_size += 128;
    }
    let sched_loop_offset_and = sched_size;
    let sched_loop_offset_rrot = sched_loop_offset_and + half_logic_size;
    let sched_loop_offset_add = sched_loop_offset_rrot + rrot_size;
    let full_sched_size = 512;
    let temp_vars_size = 8 * 8;
    let vars_top = temp_vars_size + full_sched_size;
    let main_loop_offset_and = vars_top;
    let main_loop_offset_rrot = main_loop_offset_and + half_logic_size;
    let main_loop_offset_add = main_loop_offset_rrot + rrot_size;

    script! {
        // prologue: two copies of the input state onto the altstack
        for _ in 0..64 {
            { 63 }
            OP_PICK
        }
        { u4_toaltstack(128) }

        if use_add_table {
            { u4_push_add_tables() }
        }
        { u4_push_rrot_tables() }
        { u4_push_half_xor_table() }
        { u4_push_half_lookup() }

        // bring the block's 128 nibbles above the tables (no padding: it is a full chunk)
        for _ in 0..128 {
            { tables_size + 128 - 1 }
            OP_ROLL
        }

        // message schedule
        for i in 16..64 {
            { schedule_iteration(i, sched_size + get_extra_pos(i), sched_loop_offset_rrot + get_extra_pos(i), sched_loop_offset_and + get_extra_pos(i), sched_loop_offset_add + get_extra_pos(i), use_add_table, false) }
        }

        // swap the xor table for the and table
        { u4_toaltstack(full_sched_size) }
        { u4_drop_half_lookup() }
        { u4_drop_half_table() }
        { u4_push_half_and_table() }
        { u4_push_half_lookup() }
        { u4_fromaltstack(full_sched_size) }

        // working variables a..h from the input state
        { u4_fromaltstack(64) }

        for i in 0..64 {
            { calculate_s( get_pos_var('e'), main_loop_offset_rrot, main_loop_offset_and, vec![6, 11, 25], false, true ) }
            { u4_fromaltstack(8) }
            { ch_calculation(8 + get_pos_var('e'), 8 + get_pos_var('f'), 8 + get_pos_var('g'), 8 + main_loop_offset_and ) }
            { u4_copy_u32_from( 16 + get_full_w_pos(vars_top, i) ) }
            { u4_number_to_nibble(K[i as usize]) }
            if use_add_table {
                { u4_add(8, vec![0, 8], 32 + main_loop_offset_add, true) }
                { u4_fromaltstack(8) }
                { u4_add(8, vec![0, 8, 16, 24 + get_pos_var('h') ], 24 + main_loop_offset_add, true) }
            } else {
                { u4_add_no_table(8, vec![0, 8, 16, 24, 32 + get_pos_var('h') ]) }
            }
            { u4_fromaltstack(8) }
            { calculate_s( get_pos_var('a'), main_loop_offset_rrot, main_loop_offset_and, vec![2, 13, 22], false, true ) }
            { maj_calculation( get_pos_var('a'), get_pos_var('b'), get_pos_var('c'), main_loop_offset_and ) }
            { u4_copy_u32_from(8) }
            { u4_fromaltstack(8) }
            { u4_add(8, vec![0, 8, 16], main_loop_offset_add + 24, use_add_table) }
            { u4_fromaltstack(8) }
            { u4_move_u32_from( temp_vars_size ) }
            { u4_move_u32_from( temp_vars_size ) }
            { u4_move_u32_from( temp_vars_size ) }
            { u4_add(8, vec![32, temp_vars_size], main_loop_offset_add + 8, use_add_table ) }
            { u4_fromaltstack(8) }
            { u4_move_u32_from( temp_vars_size - 8 ) }
            { u4_move_u32_from( temp_vars_size - 8 ) }
            { u4_move_u32_from( temp_vars_size - 8 ) }
        }

        // add the input state (second saved copy); results go to the altstack
        { u4_fromaltstack(64) }
        for i in 0..8 {
            { u4_add_no_table(8, vec![0, 64 - i * 8]) }
        }
        { u4_drop(64 * 8) }

        { u4_drop_half_lookup() }
        { u4_drop_half_table() }
        { u4_drop_rrot_tables() }
        if use_add_table {
            { u4_drop_add_tables() }
        }
        { u4_fromaltstack(64) }
    }
}

/// Nibbles of a 32-byte digest / midstate in big-endian word order.
pub fn state_nibbles(state: &[u32; 8]) -> Vec<u8> {
    state.iter().flat_map(|w| w.to_be_bytes()).flat_map(|b| [b >> 4, b & 0xf]).collect()
}

/// Self-test with BitVM's executor against sha2's compression function.
pub fn self_test(use_add_table: bool) -> Result<(usize, usize), String> {
    use sha2::compress256;
    let mut state = [0x6a09e667u32, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    // a non-initial midstate: compress a random block first
    let block0: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(31).wrapping_add(5));
    compress256(&mut state, &[block0.into()]);
    let block: [u8; 64] = core::array::from_fn(|i| (i as u8).wrapping_mul(97).wrapping_add(13));
    let mut expected = state;
    compress256(&mut expected, &[block.into()]);

    let block_nibbles: Vec<u8> = block.iter().flat_map(|b| [b >> 4, b & 0xf]).collect();
    let s = sha256_compress_u4(use_add_table);
    let script = script! {
        for n in block_nibbles.iter() { { *n } }
        for n in state_nibbles(&state).iter() { { *n } }
        { s.clone() }
        for n in state_nibbles(&expected).iter().rev() { { *n } OP_EQUALVERIFY }
        OP_TRUE
    };
    let res = bitvm::execute_script(script);
    if res.success {
        Ok((s.len(), res.stats.max_nb_stack_items))
    } else {
        Err(format!("failed: {:?} (max stack {})", res.error, res.stats.max_nb_stack_items))
    }
}
