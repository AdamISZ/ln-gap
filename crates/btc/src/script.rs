//! Small Script fragments shared by every leaf in LN-GAP.

use bitcoin::key::XOnlyPublicKey;
use bitcoin::opcodes::all::*;
use bitcoin::script::{Builder, PushBytesBuf};
use bitcoin::{absolute, Sequence};

use crate::Hash160;

/// Fragment helpers on top of rust-bitcoin's `Builder`.
pub trait BuilderExt: Sized {
    /// Push arbitrary bytes (≤ 520).
    fn push_bytes(self, data: &[u8]) -> Self;
    /// `<key> OP_CHECKSIG`
    fn checksig(self, key: &XOnlyPublicKey) -> Self;
    /// `<key> OP_CHECKSIGVERIFY`
    fn checksigverify(self, key: &XOnlyPublicKey) -> Self;
    /// `<a> OP_CHECKSIG <b> OP_CHECKSIGADD 2 OP_NUMEQUAL` — the PoC's 2-of-2.
    /// Witness: `<sig_b> <sig_a>` (a's signature on top, consumed first).
    fn two_of_two(self, a: &XOnlyPublicKey, b: &XOnlyPublicKey) -> Self;
    /// Same as [`two_of_two`] but `OP_NUMEQUALVERIFY`, for leaves that continue.
    fn two_of_two_verify(self, a: &XOnlyPublicKey, b: &XOnlyPublicKey) -> Self;
    /// `<height> OP_CHECKLOCKTIMEVERIFY OP_DROP`
    fn cltv(self, height: u32) -> Self;
    /// `<blocks> OP_CHECKSEQUENCEVERIFY OP_DROP`
    fn csv(self, blocks: u16) -> Self;
    /// `OP_HASH160 <h> OP_EQUALVERIFY` — consumes one witness element.
    fn hash160_verify(self, h: &Hash160) -> Self;
}

impl BuilderExt for Builder {
    fn push_bytes(self, data: &[u8]) -> Self {
        let pb = PushBytesBuf::try_from(data.to_vec()).expect("push ≤ 520 bytes");
        self.push_slice(pb)
    }
    fn checksig(self, key: &XOnlyPublicKey) -> Self {
        self.push_x_only_key(key).push_opcode(OP_CHECKSIG)
    }
    fn checksigverify(self, key: &XOnlyPublicKey) -> Self {
        self.push_x_only_key(key).push_opcode(OP_CHECKSIGVERIFY)
    }
    fn two_of_two(self, a: &XOnlyPublicKey, b: &XOnlyPublicKey) -> Self {
        self.push_x_only_key(a)
            .push_opcode(OP_CHECKSIG)
            .push_x_only_key(b)
            .push_opcode(OP_CHECKSIGADD)
            .push_int(2)
            .push_opcode(OP_NUMEQUAL)
    }
    fn two_of_two_verify(self, a: &XOnlyPublicKey, b: &XOnlyPublicKey) -> Self {
        self.push_x_only_key(a)
            .push_opcode(OP_CHECKSIG)
            .push_x_only_key(b)
            .push_opcode(OP_CHECKSIGADD)
            .push_int(2)
            .push_opcode(OP_NUMEQUALVERIFY)
    }
    fn cltv(self, height: u32) -> Self {
        let lt = absolute::LockTime::from_height(height).expect("height < 500_000_000");
        self.push_lock_time(lt).push_opcode(OP_CLTV).push_opcode(OP_DROP)
    }
    fn csv(self, blocks: u16) -> Self {
        self.push_sequence(Sequence::from_height(blocks)).push_opcode(OP_CSV).push_opcode(OP_DROP)
    }
    fn hash160_verify(self, h: &Hash160) -> Self {
        self.push_opcode(OP_HASH160).push_bytes(h).push_opcode(OP_EQUALVERIFY)
    }
}
