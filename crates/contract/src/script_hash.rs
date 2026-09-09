//! In-Script SHA-256, from the BitVM project's generator (MIT,
//! github.com/BitVM/BitVM, `bitvm/src/hash/sha256.rs`), embedded as bytes
//! produced by `tools/scriptgen` (byte-wise variant; 512 KB for a 32-byte
//! message, ~1 MB for 64 or 80 bytes; the nibble-wise `sha256_u4` variant is
//! about 35% smaller and BLAKE3 is 78 KB per 64-byte block — see
//! docs/planning/SPV_DISPUTE.md, phase 1 findings).
//!
//! Stack convention of the embedded scripts: the input is `n` elements, one
//! per byte, each a *script number* 0..=255 (so 0 is the empty vector and
//! bytes ≥ 0x80 are two bytes), with the message's first byte on top of the
//! stack; the output is 32 such elements. Helpers here convert to and from
//! witness elements and let a leaf compare the digest to a constant.

use bitcoin::opcodes::all::*;
use bitcoin::script::{Builder, PushBytesBuf, ScriptBuf};

const SHA256_32: &[u8] = include_bytes!("../scripts/sha256_32.bin");
const SHA256_64: &[u8] = include_bytes!("../scripts/sha256_64.bin");
const SHA256_80: &[u8] = include_bytes!("../scripts/sha256_80.bin");
const SHA256_U4_32: &[u8] = include_bytes!("../scripts/sha256_u4_32.bin");
const SHA256_U4_64: &[u8] = include_bytes!("../scripts/sha256_u4_64.bin");
const SHA256_U4_80: &[u8] = include_bytes!("../scripts/sha256_u4_80.bin");
const SHA256_COMPRESS_U4: &[u8] = include_bytes!("../scripts/sha256_compress_u4.bin");

/// The SHA-256 script for an `n`-byte message (`n` ∈ {32, 64, 80}).
pub fn sha256_script(n: usize) -> ScriptBuf {
    let bytes = match n {
        32 => SHA256_32,
        64 => SHA256_64,
        80 => SHA256_80,
        _ => panic!("no embedded SHA-256 script for {n} bytes"),
    };
    ScriptBuf::from_bytes(bytes.to_vec())
}

/// One byte as the minimal script-number encoding the scripts expect.
pub fn byte_as_scriptnum(b: u8) -> Vec<u8> {
    match b {
        0 => vec![],
        1..=127 => vec![b],
        _ => vec![b, 0x00],
    }
}

/// Witness elements for message `msg`, in consumption order (first byte
/// of the message consumed first, i.e. on top of the stack).
pub fn message_witness(msg: &[u8]) -> Vec<Vec<u8>> {
    msg.iter().map(|b| byte_as_scriptnum(*b)).collect()
}

/// Append `sha256_script(n)` followed by a check that the 32 output bytes
/// equal `digest`, leaving `1`. Consumes the message elements.
pub fn sha256_equals(b: Builder, n: usize, digest: &[u8; 32]) -> Builder {
    let mut b = append(b, &sha256_script(n));
    // output: 32 script numbers; compare from the top
    for byte in digest_stack_order(digest) {
        b = push_scriptnum(b, byte).push_opcode(OP_EQUALVERIFY);
    }
    b.push_opcode(OP_PUSHNUM_1)
}

/// The digest bytes in the order they sit on the stack after the script,
/// top first. Determined empirically against the interpreter (see tests).
pub fn digest_stack_order(digest: &[u8; 32]) -> Vec<u8> {
    digest.to_vec()
}

fn push_scriptnum(b: Builder, byte: u8) -> Builder {
    match byte {
        0 => b.push_opcode(OP_PUSHBYTES_0),
        1..=16 => b.push_int(i64::from(byte)),
        _ => b.push_slice(PushBytesBuf::try_from(byte_as_scriptnum(byte)).unwrap()),
    }
}

/// Concatenate raw script bytes (the embedded scripts are already valid
/// instruction streams, so byte-appending is safe).
fn append(b: Builder, s: &ScriptBuf) -> Builder {
    let mut v = b.into_script().into_bytes();
    v.extend_from_slice(s.as_bytes());
    Builder::from(v)
}

// ----- nibble-wise variant (`bitvm/src/hash/sha256_u4.rs`): about 35% smaller -----
//
// Convention: input = 2n elements, one per nibble, each a script number
// 0..=15, in message order with the *last* nibble on top; output = 64 nibble
// elements in the same layout (last nibble of the digest on top).

pub fn sha256_u4_script(n: usize) -> ScriptBuf {
    let bytes = match n {
        32 => SHA256_U4_32,
        64 => SHA256_U4_64,
        80 => SHA256_U4_80,
        _ => panic!("no embedded nibble-wise SHA-256 script for {n} bytes"),
    };
    ScriptBuf::from_bytes(bytes.to_vec())
}

fn nibbles(msg: &[u8]) -> Vec<u8> {
    msg.iter().flat_map(|b| [b >> 4, b & 0xf]).collect()
}

/// Witness elements for `msg` in consumption order (last nibble first).
pub fn message_witness_u4(msg: &[u8]) -> Vec<Vec<u8>> {
    nibbles(msg).iter().rev().map(|n| byte_as_scriptnum(*n)).collect()
}

/// Append the nibble-wise script and a check that the digest equals `digest`.
pub fn sha256_u4_equals(b: Builder, n: usize, digest: &[u8; 32]) -> Builder {
    let mut b = append(b, &sha256_u4_script(n));
    for nib in nibbles(digest).iter().rev() {
        b = push_scriptnum(b, *nib).push_opcode(OP_EQUALVERIFY);
    }
    b.push_opcode(OP_PUSHNUM_1)
}

// ----- one compression: midstate in, midstate out (tools/scriptgen/src/compress.rs) -----
//
// Stack in (consumption order): 64 state nibbles with the last nibble first
// (state = 8 big-endian words), then 128 block nibbles with the last first.
// Stack out: 64 nibbles of the new state, last nibble on top.

pub fn sha256_compress_script() -> ScriptBuf {
    ScriptBuf::from_bytes(SHA256_COMPRESS_U4.to_vec())
}

/// A midstate as 32 bytes (big-endian words).
pub fn state_bytes(state: &[u32; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, w) in state.iter().enumerate() {
        out[4 * i..4 * i + 4].copy_from_slice(&w.to_be_bytes());
    }
    out
}

/// Witness elements for one compression, consumption order.
pub fn compress_witness(state: &[u32; 8], block: &[u8; 64]) -> Vec<Vec<u8>> {
    let mut v = message_witness_u4(&state_bytes(state));
    v.extend(message_witness_u4(block));
    v
}

/// Append the compression and a check that the new state equals `expected`.
pub fn sha256_compress_equals(b: Builder, expected: &[u32; 8]) -> Builder {
    let mut b = append(b, &sha256_compress_script());
    for nib in nibbles(&state_bytes(expected)).iter().rev() {
        b = push_scriptnum(b, *nib).push_opcode(OP_EQUALVERIFY);
    }
    b.push_opcode(OP_PUSHNUM_1)
}
