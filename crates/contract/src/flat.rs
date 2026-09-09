//! The phase-1 terminal: one leaf recomputing a whole compression
//! (`sha256_u4`, 369 KB) for claims with `inner = false`. Kept for
//! measurement; requires an 8-word state and compression-only steps with
//! constant blocks and `init = D`.

use anyhow::Result;
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_lamport::winternitz::{WotsExt, WotsPublic, WotsSig};

use crate::claim::{all_paths, source_key, state_nibbles, step_sources, timeout_leaf, ClaimKeys, ClaimSpec, Init, Src, StateSource, Step};
use crate::script_hash::{append_script, nibbles as byte_nibbles, push_scriptnum, sha256_compress_script};

/// The constant block of a flat step.
pub fn flat_block(step: &Step) -> [u8; 64] {
    let Step::Compress { init: Init::D, block, .. } = step else { panic!("flat claims need compress(D) steps") };
    let mut b = [0u8; 64];
    for (j, src) in block.iter().enumerate() {
        let Src::Const(c) = src else { panic!("flat claims need constant blocks") };
        b[4 * j..4 * j + 4].copy_from_slice(&c.to_be_bytes());
    }
    b
}

/// Terminal leaf body for one path (after `<Q> OP_CHECKSIGVERIFY`).
fn step_body(mut b: Builder, cur: &StateSource, next_pk: &WotsPublic, block: &[u8; 64], keys: &ClaimKeys) -> Builder {
    // claimed next: verify, reverse, park (digit 63 ends on the altstack top)
    b = b.wots_verify(next_pk);
    for i in 1..64i64 {
        b = b.push_int(i).push_opcode(OP_ROLL);
    }
    for _ in 0..64 {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    match cur {
        StateSource::Const(s) => {
            for nib in byte_nibbles(block) {
                b = push_scriptnum(b, nib);
            }
            for nib in state_nibbles(s) {
                b = push_scriptnum(b, nib);
            }
        }
        src => {
            let pk = source_key(src, keys);
            b = b.wots_verify(pk);
            for _ in 0..64 {
                b = b.push_opcode(OP_TOALTSTACK);
            }
            for nib in byte_nibbles(block) {
                b = push_scriptnum(b, nib);
            }
            for _ in 0..64 {
                b = b.push_opcode(OP_FROMALTSTACK);
            }
        }
    }
    b = append_script(b, &sha256_compress_script());
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_EQUAL);
    for _ in 1..64 {
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_ROT).push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
    }
    b.push_opcode(OP_NOT)
}

/// The terminal leaf script for `path`, and its name (a hash of the script:
/// paths with the same sources and block share a leaf).
pub fn terminal_leaf(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec, path: &[u32]) -> (String, bitcoin::ScriptBuf) {
    assert_eq!(spec.n_words, 8, "flat claims use an 8-word state");
    let q = ctx.key(prover.other()).payment;
    let (cur, next, step) = step_sources(spec, path);
    let next_pk = source_key(&next, keys);
    let script = step_body(Builder::new().checksigverify(&q), &cur, next_pk, &flat_block(&spec.steps[step as usize]), keys).into_script();
    let h = lngap_btc::hash160(script.as_bytes());
    (format!("step_{}", hex::encode(&h[..4])), script)
}

/// `R_R'`: the challenger isolates one step and disproves it, or the prover times out.
pub fn terminal_tree(ctx: &CommitCtx, prover: Role, keys: &ClaimKeys, spec: &ClaimSpec) -> Result<TapTree> {
    let mut leaves: Vec<Leaf> = Vec::new();
    for path in all_paths(spec) {
        let (name, script) = terminal_leaf(ctx, prover, keys, spec, &path);
        if !leaves.iter().any(|l| l.name == name) {
            leaves.push(Leaf::new(name, script, Timelock::NONE));
        }
    }
    leaves.push(timeout_leaf(ctx, prover));
    TapTree::new(leaves)
}

/// Witness args for a terminal step leaf (after Q's signature): the
/// prover's signatures for `next` then `cur` (none for a constant `cur`).
pub fn step_witness(cur: &StateSource, next_sig: &WotsSig, cur_sig: Option<&WotsSig>) -> Vec<Vec<u8>> {
    let mut v = next_sig.consumption_order();
    if !matches!(cur, StateSource::Const(_)) {
        v.extend(cur_sig.expect("cur signature").consumption_order());
    }
    v
}
