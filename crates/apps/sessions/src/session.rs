//! The session contract's own pieces (V25_POC_PLAN.md, Phase 6): its
//! terms, the binary-decomposed payout of a withdrawal `b` on the dispute
//! path, and the default to the hub at `T_close`. The dispute itself is
//! lngap-v25's graph over the search game (`ZkDated` with pre-signed
//! proofs, so that a proved withdrawal pays exactly `b`).

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
/// the hub's. Witness, wire order: the word's reveal, the spender's
/// signature.
pub fn bit_leaf(ctx: &CommitCtx, i: u32, b_key: &WotsPublic, want: bool) -> Leaf {
    let who = if want { Role::User } else { Role::Hub };
    let m = b_key.params.message_digits as usize;
    assert_eq!(m, 8, "a word's key signs 4 bytes");
    // digit k (0 the most significant nibble) sits at depth m - 1 - k
    let (nibble, j) = (7 - i / 4, i % 4);
    let mut b = Builder::new().checksigverify(&ctx.key(who).payment).wots_verify(b_key);
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
    Leaf::new(name, b.push_int(1).into_script(), Timelock::NONE)
}

/// The output for bit `i`: Alice's leaf and the hub's.
pub fn bit_tree(ctx: &CommitCtx, i: u32, b_key: &WotsPublic) -> Result<TapTree> {
    TapTree::new(vec![bit_leaf(ctx, i, b_key, true), bit_leaf(ctx, i, b_key, false)])
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

/// `default` on the contract output: after `T_close`, the hub's key.
pub fn default_leaf(ctx: &CommitCtx, t_close: u32) -> Leaf {
    let b = Builder::new().cltv(t_close).checksig(&ctx.key(Role::Hub).payment);
    Leaf::new("default", b.into_script(), Timelock::cltv(t_close))
}
