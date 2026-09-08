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
