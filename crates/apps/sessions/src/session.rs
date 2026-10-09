//! The session contract (LN-GAP v3, research/lngap_v3.pdf): its terms,
//! the contract reserves, the binary-decomposed payout of a withdrawal `b`
//! on the dispute path, the default at `T_close`, and the input-word
//! checks.
//!
//! One contract, no venue. Its output carries two leaves besides the
//! channel's revocation:
//! - `default`: after `T_close`, a pre-signed transaction paying the hub
//!   and returning Alice's reserve (not withdrawing is not a lie);
//! - `escalate`: Alice's claim on chain, as move 1 of BitVMX's search with
//!   her signed input words; the search continues on lngap-v25's ladder
//!   (`ZkDated` with pre-signed proofs, so that a proved withdrawal pays
//!   exactly `b`), and the first ladder output carries the hub's
//!   input-word checks.
//!
//! The cooperative withdrawal is a fold of the channel and never touches
//! the contract.

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Terms {
    /// The contract's identifier `c`, the memo a return must carry.
    pub id: u32,
    /// The payout's granularity `u`.
    pub unit: Amount,
    /// `K`: a withdrawal is `b < 2^K` units, so `V_max = (2^K - 1) u`.
    pub bits: u32,
    /// On the dispute path, bits below this get no output (they would be
    /// dust): `b` is paid rounded down to a multiple of `2^low_bits` units,
    /// the remainder to the hub. 0 pays every bit; with sats as the unit,
    /// 9 (512 sats).
    pub low_bits: u32,
    /// Alice's deposit `D`, in units.
    pub deposit: u32,
    /// `T_close`: after it, with no claim, everything goes to the hub.
    pub t_close: u32,
    /// The contract reserves `r_A`, `r_H`: returned in every honest
    /// outcome, forfeited to the other side by losing a dispute.
    pub reserve_alice: Amount,
    pub reserve_hub: Amount,
}

impl Terms {
    pub fn v_max_units(&self) -> u32 {
        (1 << self.bits) - 1
    }
    pub fn v_max(&self) -> Amount {
        self.unit * u64::from(self.v_max_units())
    }
    /// Both reserves: what the winner of a dispute takes on top of its
    /// share of `V_max`.
    pub fn reserves(&self) -> Amount {
        self.reserve_alice + self.reserve_hub
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

/// `alice_reserve` on the reserve output: Alice, after `delta` (the hub's
/// chance to show an equivocation on `b`). Witness: her signature.
pub fn reserve_leaf(ctx: &CommitCtx) -> Leaf {
    let b = Builder::new().csv(ctx.params.delta).checksig(&ctx.key(Role::User).payment);
    Leaf::new("alice_reserve", b.into_script(), Timelock::csv(ctx.params.delta))
}

/// The reserve output of a payout to Alice: both reserves, hers after
/// `delta`, the hub's with `equiv_b` (index `K`, after the bit outputs').
pub fn reserve_tree(ctx: &CommitCtx, t: &Terms, b_key: &WotsPublic) -> Result<TapTree> {
    TapTree::new(vec![reserve_leaf(ctx), equiv_b_leaf(ctx, t.bits, b_key)])
}

/// The outputs of every transaction that pays Alice's withdrawal (her
/// proof, the hub's timeout): for each bit `i` from `low_bits` to `K - 1`,
/// an output of `u 2^i`, Alice's iff bit `i` of her signed `b` is set; then
/// both reserves, Alice's; the rest of `available` (less `fee`) to the
/// hub.
pub fn payout(ctx: &CommitCtx, t: &Terms, b_key: &WotsPublic, available: Amount, fee: Amount) -> Result<Vec<TxOut>> {
    let total = available.checked_sub(fee).ok_or_else(|| anyhow::anyhow!("the fee exceeds the output"))?;
    ensure!(total >= t.v_max() + t.reserves(), "{total} cannot pay V_max {} and the reserves", t.v_max());
    let mut outs: Vec<TxOut> = (t.low_bits..t.bits).map(|i| Ok(TxOut { value: t.unit * (1u64 << i), script_pubkey: bit_tree(ctx, i, b_key)?.script_pubkey() })).collect::<Result<_>>()?;
    let paid: Amount = outs.iter().map(|o| o.value).sum();
    outs.push(TxOut { value: t.reserves(), script_pubkey: reserve_tree(ctx, t, b_key)?.script_pubkey() });
    let rest = total - paid - t.reserves();
    if rest >= ctx.params.dust {
        outs.push(TxOut { value: rest, script_pubkey: ctx.key(Role::Hub).payout_spk.clone() });
    }
    Ok(outs)
}

/// The outputs of the transaction that ends the session by default after
/// `T_close`: Alice's reserve back to her, the rest (less `fee`) to the
/// hub.
pub fn default_outputs(ctx: &CommitCtx, t: &Terms, available: Amount, fee: Amount) -> Result<Vec<TxOut>> {
    let total = available.checked_sub(fee).ok_or_else(|| anyhow::anyhow!("the fee exceeds the output"))?;
    ensure!(total > t.reserve_alice, "{total} cannot return the reserve");
    Ok(vec![
        TxOut { value: t.reserve_alice, script_pubkey: ctx.key(Role::User).payout_spk.clone() },
        TxOut { value: total - t.reserve_alice, script_pubkey: ctx.key(Role::Hub).payout_spk.clone() },
    ])
}

/// An input-word check on the FIRST LADDER OUTPUT (the one `escalate`
/// creates, which carries Alice's signed input words), the hub's leaf:
/// Alice's signature (her input key for word `j`) on a value that is NOT
/// `expected` gives the hub everything, both reserves included. The statement's input must carry
/// the session's constants in fixed words: the journal's length, the
/// image id (otherwise Alice could prove another program's output, which
/// the verifier would accept), the memo `c` (otherwise another session's
/// return could be redeemed here). Witness, wire order: the word's
/// reveal, the hub's signature.
pub fn input_word_leaf(ctx: &CommitCtx, name: &str, key: &WotsPublic, expected: u32) -> Leaf {
    let m = key.params.message_digits as usize;
    assert_eq!(m, 8, "a word's key signs 4 bytes");
    let mut b = Builder::new().checksigverify(&ctx.key(Role::Hub).payment).wots_verify(key);
    // the digits are the word big-endian, digit 0 deepest: compare each
    // with the expected nibble, from the top down, and count differences
    let nibbles: Vec<i64> = expected.to_be_bytes().iter().flat_map(|x| [i64::from(x >> 4), i64::from(x & 15)]).collect();
    for k in (0..m).rev() {
        b = b.push_int(nibbles[k]).push_opcode(OP_NUMNOTEQUAL).push_opcode(OP_TOALTSTACK);
    }
    b = b.push_opcode(OP_FROMALTSTACK);
    for _ in 1..m {
        b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_ADD);
    }
    Leaf::new(name.to_string(), b.into_script(), Timelock::NONE)
}

/// `default` on the session contract: after `T_close`, 2-of-2 pre-signed
/// at the session's start, paying [`default_outputs`]. Witness: the hub's
/// signature, the user's.
pub fn default_leaf(ctx: &CommitCtx, t_close: u32) -> Leaf {
    let b = ctx.two_of_two_verify(Builder::new().cltv(t_close));
    Leaf::new("default", b.push_int(1).into_script(), Timelock::cltv(t_close))
}
