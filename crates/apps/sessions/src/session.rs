//! The session contract's own pieces (V25_POC_PLAN.md, Phase 6; the
//! failure scenarios of research/scenarios.pdf): its terms, the
//! binary-decomposed payout of a withdrawal `b` on the dispute path, the
//! default to the hub at `T_close`, and the game contract's `settle`.
//!
//! Two contracts, because a withdrawal starts when Alice decides and its
//! deadlines must count from that start:
//! - the SESSION contract, before any withdrawal, carries only `default`
//!   (the hub, after `T_close`) and Alice's unilateral start (`escalate`,
//!   her first move into the on-chain ladder): no absence claims, so a
//!   force-close mid-session gives the hub nothing to spend before `T_close`
//!   (every signed state must be safe to publish);
//! - the GAME contract, signed at a cooperative start, carries the dispute
//!   graph with deadlines counted from that start, `escalate` (either
//!   party takes the game onto the ladder, replaying the moves so far), and
//!   `settle` (the claim accepted at the game's end), and no default.
//!
//! The dispute itself is lngap-v25's graph over the search game
//! (`ZkDated` with pre-signed proofs, so that a proved withdrawal pays
//! exactly `b`).

use anyhow::{ensure, Result};
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{Amount, TxOut};
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_lamport::winternitz::{WotsExt, WotsPublic};

/// A session's terms.
#[derive(Clone, Copy, Debug)]
pub struct Terms {
    /// The contract's identifier `c`, the memo a return must carry.
    pub id: u32,
    /// The payout's granularity `u`.
    pub unit: Amount,
    /// `K`: a withdrawal is `b < 2^K` units, so `V_max = (2^K - 1) u`.
    pub bits: u32,
    /// Alice's deposit `D`, in units.
    pub deposit: u32,
    /// `T_close`: after it, with no claim, everything goes to the hub.
    pub t_close: u32,
}

impl Terms {
    pub fn v_max_units(&self) -> u32 {
        (1 << self.bits) - 1
    }
    pub fn v_max(&self) -> Amount {
        self.unit * u64::from(self.v_max_units())
    }
}

/// Bit `i` of `b`'s input-word signature (the prover's depth-1 key for
/// word 0, which signs `b` big-endian): `want` 1 for Alice's leaf, 0 for
/// the hub's. Alice's leaf waits `delta`, so that if she signed two values
/// of `b` the hub's `equiv_b` takes the output first. Witness, wire order:
/// the word's reveal, the spender's signature.
pub fn bit_leaf(ctx: &CommitCtx, i: u32, b_key: &WotsPublic, want: bool) -> Leaf {
    let who = if want { Role::User } else { Role::Hub };
    let m = b_key.params.message_digits as usize;
    assert_eq!(m, 8, "a word's key signs 4 bytes");
    // digit k (0 the most significant nibble) sits at depth m - 1 - k
    let (nibble, j) = (7 - i / 4, i % 4);
    let (mut b, tl) = if want { (Builder::new().csv(ctx.params.delta), Timelock::csv(ctx.params.delta)) } else { (Builder::new(), Timelock::NONE) };
    b = b.checksigverify(&ctx.key(who).payment).wots_verify(b_key);
    b = b.push_int((m - 1 - nibble as usize) as i64).push_opcode(OP_PICK);
    // reduce the nibble mod 2^(j+1), then compare with 2^j
    for h in (j + 1..4).rev() {
        b = b.push_opcode(OP_DUP).push_int(1 << h).push_opcode(OP_GREATERTHANOREQUAL).push_opcode(OP_IF).push_int(1 << h).push_opcode(OP_SUB).push_opcode(OP_ENDIF);
    }
    b = b.push_int(1 << j).push_opcode(OP_GREATERTHANOREQUAL);
    if !want {
        b = b.push_opcode(OP_NOT);
    }
    b = b.push_opcode(OP_VERIFY);
    for _ in 0..m / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    let name = if want { format!("alice_bit_{i}") } else { format!("hub_bit_{i}") };
    Leaf::new(name, b.push_int(1).into_script(), tl)
}

/// `equiv_b` on each bit output: two different signatures under `b`'s
/// one-time key (Alice signed two values of `b`); the hub takes the
/// output. `i` only makes the leaf distinct per output. Witness, wire
/// order: one reveal, the other, the hub's signature.
pub fn equiv_b_leaf(ctx: &CommitCtx, i: u32, b_key: &WotsPublic) -> Leaf {
    let m = b_key.params.message_digits as usize;
    let mut b = Builder::new().push_int(i64::from(i)).push_opcode(OP_DROP).checksigverify(&ctx.key(Role::Hub).payment).wots_verify(b_key);
    for _ in 0..m {
        b = b.push_opcode(OP_TOALTSTACK);
    }
    b = b.wots_verify(b_key);
    for _ in 0..m {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    // count the digits that differ; at least one must
    b = b.push_int(0);
    for j in 0..m {
        b = b
            .push_int((m - j) as i64)
            .push_opcode(OP_PICK)
            .push_int((2 * m - j + 1) as i64)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SUB)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_ADD);
    }
    b = b.push_opcode(OP_VERIFY);
    for _ in 0..m {
        b = b.push_opcode(OP_2DROP);
    }
    Leaf::new(format!("equiv_b_{i}"), b.push_int(1).into_script(), Timelock::NONE)
}

/// The output for bit `i`: Alice's leaf, the hub's, and `equiv_b`.
pub fn bit_tree(ctx: &CommitCtx, i: u32, b_key: &WotsPublic) -> Result<TapTree> {
    TapTree::new(vec![bit_leaf(ctx, i, b_key, true), bit_leaf(ctx, i, b_key, false), equiv_b_leaf(ctx, i, b_key)])
}

/// The outputs of every split that pays Alice's withdrawal: `K` outputs of
/// `u 2^i`, each Alice's iff bit `i` of her signed `b` is set, and the rest
/// of `available` (less `fee`) to the hub.
pub fn payout(ctx: &CommitCtx, t: &Terms, b_key: &WotsPublic, available: Amount, fee: Amount) -> Result<Vec<TxOut>> {
    let total = available.checked_sub(fee).ok_or_else(|| anyhow::anyhow!("the fee exceeds the output"))?;
    ensure!(total >= t.v_max(), "{total} cannot pay V_max {}", t.v_max());
    let mut outs: Vec<TxOut> = (0..t.bits).map(|i| Ok(TxOut { value: t.unit * (1u64 << i), script_pubkey: bit_tree(ctx, i, b_key)?.script_pubkey() })).collect::<Result<_>>()?;
    let rest = total - t.v_max();
    if rest >= ctx.params.dust {
        outs.push(TxOut { value: rest, script_pubkey: ctx.key(Role::Hub).payout_spk.clone() });
    }
    Ok(outs)
}

/// `settle` on the GAME contract: after the game's end (`at`, a height
/// past the last depth's deadline and the hub's chance to force the last
/// step on chain), Alice's claim is accepted; 2-of-2 pre-signed, paying
/// the withdrawal's decomposition. Witness: the hub's signature, the
/// user's.
pub fn settle_leaf(ctx: &CommitCtx, at: u32) -> Leaf {
    let b = ctx.two_of_two_verify(Builder::new().cltv(at));
    Leaf::new("settle", b.push_int(1).into_script(), Timelock::cltv(at))
}

/// `default` on the SESSION contract: after `T_close`, the hub's key.
pub fn default_leaf(ctx: &CommitCtx, t_close: u32) -> Leaf {
    let b = Builder::new().cltv(t_close).checksig(&ctx.key(Role::Hub).payment);
    Leaf::new("default", b.into_script(), Timelock::cltv(t_close))
}
