//! Script gadgets over bit commitments. Each consumes witness elements from
//! the top of the stack and leaves a result (or verifies and leaves nothing).

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::Hash160;

use crate::{BitCommit, PublicKey};

/// Gadget extension trait on `Builder`.
pub trait LamportExt: Sized {
    /// Witness: `p`. Leaves the bit (0/1) on the stack; fails if `p` matches
    /// neither hash.
    /// ```text
    /// OP_HASH160 OP_DUP <h1> OP_EQUAL OP_IF OP_DROP 1 OP_ELSE <h0> OP_EQUALVERIFY 0 OP_ENDIF
    /// ```
    fn bit_decode(self, c: &BitCommit) -> Self;

    /// Witness: `p`. `OP_HASH160 <h_expected> OP_EQUALVERIFY`. For constants.
    fn expect_bit(self, h_expected: &Hash160) -> Self;

    /// Witness: the reveal of `pk` (msb on top). Verifies every preimage
    /// matches the constant `value` and leaves nothing.
    fn expect_uint(self, pk: &PublicKey, value: u32) -> Self;

    /// Witness: the reveal of `pk` (msb on top). Leaves the decoded number
    /// (script number, `n_bits ≤ 31`) on the stack.
    /// Per bit from the msb: `OP_DUP OP_ADD OP_SWAP bit_decode OP_ADD`.
    fn decode_uint(self, pk: &PublicKey) -> Self;

    /// Witness: `p0 p1` (p1 on top). Verifies both preimages of one bit; used
    /// by equivocation-slashing leaves. Leaves nothing.
    fn equivocation(self, c: &BitCommit) -> Self;
}

impl LamportExt for Builder {
    fn bit_decode(self, c: &BitCommit) -> Self {
        self.push_opcode(OP_HASH160)
            .push_opcode(OP_DUP)
            .push_bytes(&c.h1)
            .push_opcode(OP_EQUAL)
            .push_opcode(OP_IF)
            .push_opcode(OP_DROP)
            .push_int(1)
            .push_opcode(OP_ELSE)
            .push_bytes(&c.h0)
            .push_opcode(OP_EQUALVERIFY)
            .push_int(0)
            .push_opcode(OP_ENDIF)
    }

    fn expect_bit(self, h_expected: &Hash160) -> Self {
        self.hash160_verify(h_expected)
    }

    fn expect_uint(mut self, pk: &PublicKey, value: u32) -> Self {
        assert!(pk.n_bits() <= 32 && (pk.n_bits() == 32 || value >> pk.n_bits() == 0), "value fits key");
        for i in (0..pk.n_bits()).rev() {
            let bit = (value >> i) & 1 == 1;
            let h = if bit { &pk.bits[i].h1 } else { &pk.bits[i].h0 };
            self = self.expect_bit(h);
        }
        self
    }

    fn decode_uint(mut self, pk: &PublicKey) -> Self {
        assert!(pk.n_bits() <= 31, "script numbers: ≤ 31 bits");
        self = self.push_int(0);
        for i in (0..pk.n_bits()).rev() {
            self = self
                .push_opcode(OP_DUP)
                .push_opcode(OP_ADD)
                .push_opcode(OP_SWAP)
                .bit_decode(&pk.bits[i])
                .push_opcode(OP_ADD);
        }
        self
    }

    fn equivocation(self, c: &BitCommit) -> Self {
        self.hash160_verify(&c.h1).hash160_verify(&c.h0)
    }
}
