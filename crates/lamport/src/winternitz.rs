//! Winternitz one-time signatures for 256-bit values (midstates, digests):
//! 4-bit digits, so a 32-byte message is 64 digits plus 3 checksum digits.
//! Witness: 1.4 KB; verify script: ~5 KB. Compared to per-bit Lamport
//! (5.4 KB witness, 14 KB script) this is what makes a compression step with
//! two committed midstates fit a standard transaction.
//!
//! Wire format and verifier ported from BitVM's `ListpickVerifier`
//! (github.com/BitVM/BitVM, `bitvm/src/signatures/winternitz.rs`, MIT).
//! Digit convention here: digit `i` is nibble `i` of the message in message
//! order (high nibble of byte 0 first), so after verification the digits sit
//! on the stack with the *last* nibble on top — the layout the in-Script
//! SHA-256 expects for a midstate.

use anyhow::{ensure, Result};
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use lngap_btc::script::BuilderExt;
use lngap_btc::{hash160, Hash160};
use serde::{Deserialize, Serialize};

pub const LOG2_BASE: u32 = 4;
pub const MAX_DIGIT: u32 = 15;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WotsParams {
    pub message_digits: u32,
    pub checksum_digits: u32,
}

impl WotsParams {
    pub fn for_bytes(n_bytes: u32) -> WotsParams {
        let message_digits = n_bytes * 2;
        // checksum ≤ MAX_DIGIT * message_digits; digits in base 16
        let mut checksum_digits = 0;
        let mut cur: u64 = 1;
        while cur < u64::from(MAX_DIGIT * message_digits + 1) {
            cur *= 16;
            checksum_digits += 1;
        }
        WotsParams { message_digits, checksum_digits }
    }
    pub fn total_digits(&self) -> u32 {
        self.message_digits + self.checksum_digits
    }
}

/// Public key: one hash per digit (message digits, then checksum digits).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WotsPublic {
    pub params: WotsParams,
    pub digits: Vec<Hash160>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct WotsSecret {
    pub params: WotsParams,
    secret: [u8; 32],
}

impl std::fmt::Debug for WotsSecret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "WotsSecret({} digits)", self.params.total_digits())
    }
}

/// A signature: per digit, `(H^digit(sk_i), digit)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WotsSig {
    pub params: WotsParams,
    pub hashes: Vec<Hash160>,
    pub digits: Vec<u8>,
}

fn digit_secret(secret: &[u8; 32], index: u32) -> Hash160 {
    let mut s = secret.to_vec();
    let mut i = index;
    while i > 0 {
        s.push((i & 255) as u8);
        i >>= 8;
    }
    hash160(&s)
}

fn hash_times(mut h: Hash160, n: u32) -> Hash160 {
    for _ in 0..n {
        h = hash160(&h);
    }
    h
}

pub fn message_digits(msg: &[u8]) -> Vec<u8> {
    msg.iter().flat_map(|b| [b >> 4, b & 0xf]).collect()
}

fn checksum_digits(ps: &WotsParams, digits: &[u8]) -> Vec<u8> {
    let sum: u32 = digits.iter().map(|d| u32::from(*d)).sum();
    let mut c = MAX_DIGIT * ps.message_digits - sum;
    let mut out = vec![0u8; ps.checksum_digits as usize];
    for d in out.iter_mut().rev() {
        *d = (c % 16) as u8;
        c /= 16;
    }
    out
}

impl WotsSecret {
    pub fn from_entropy(params: WotsParams, secret: [u8; 32]) -> WotsSecret {
        WotsSecret { params, secret }
    }
    pub fn public(&self) -> WotsPublic {
        let digits = (0..self.params.total_digits()).map(|i| hash_times(digit_secret(&self.secret, i), MAX_DIGIT)).collect();
        WotsPublic { params: self.params, digits }
    }
    pub fn sign(&self, msg: &[u8]) -> Result<WotsSig> {
        let mut digits = message_digits(msg);
        ensure!(digits.len() as u32 == self.params.message_digits, "message has {} digits, key has {}", digits.len(), self.params.message_digits);
        digits.extend(checksum_digits(&self.params, &digits));
        let hashes = digits.iter().enumerate().map(|(i, d)| hash_times(digit_secret(&self.secret, i as u32), u32::from(*d))).collect();
        Ok(WotsSig { params: self.params, hashes, digits })
    }
}

impl WotsSig {
    /// Witness elements in consumption order (top of stack first):
    /// `digit[last], hash[last], ..., digit[0], hash[0]`.
    pub fn consumption_order(&self) -> Vec<Vec<u8>> {
        let mut v = Vec::with_capacity(2 * self.digits.len());
        for i in (0..self.digits.len()).rev() {
            v.push(scriptnum(self.digits[i]));
            v.push(self.hashes[i].to_vec());
        }
        v
    }
    /// The message bytes this signature commits to.
    pub fn message(&self) -> Vec<u8> {
        self.digits[..self.params.message_digits as usize].chunks(2).map(|p| (p[0] << 4) | p[1]).collect()
    }
    /// Rebuild from witness elements in consumption order.
    pub fn from_consumption_order(params: WotsParams, items: &[Vec<u8>]) -> Result<WotsSig> {
        let n = params.total_digits() as usize;
        ensure!(items.len() == 2 * n, "expected {} witness elements, got {}", 2 * n, items.len());
        let mut digits = vec![0u8; n];
        let mut hashes = vec![[0u8; 20]; n];
        for i in 0..n {
            let d = &items[2 * (n - 1 - i)];
            let h = &items[2 * (n - 1 - i) + 1];
            digits[i] = match d.len() {
                0 => 0,
                1 => d[0],
                _ => anyhow::bail!("digit element too long"),
            };
            ensure!(h.len() == 20, "hash element not 20 bytes");
            hashes[i].copy_from_slice(h);
        }
        Ok(WotsSig { params, hashes, digits })
    }
}

impl WotsPublic {
    /// Off-chain verification; returns the message.
    pub fn verify(&self, sig: &WotsSig) -> Result<Vec<u8>> {
        ensure!(sig.params == self.params, "params mismatch");
        let n = self.params.total_digits() as usize;
        for i in 0..n {
            ensure!(sig.digits[i] <= MAX_DIGIT as u8, "digit {i} out of range");
            let expect = hash_times(sig.hashes[i], MAX_DIGIT - u32::from(sig.digits[i]));
            ensure!(expect == self.digits[i], "digit {i}: hash chain does not reach the public key");
        }
        let msg_digits = &sig.digits[..self.params.message_digits as usize];
        ensure!(sig.digits[self.params.message_digits as usize..] == checksum_digits(&self.params, msg_digits)[..], "checksum mismatch");
        Ok(sig.message())
    }
}

fn scriptnum(d: u8) -> Vec<u8> {
    if d == 0 { vec![] } else { vec![d] }
}

/// Script gadget: verify a Winternitz signature against `pk`, consuming the
/// witness and leaving the message digits `d_0 … d_{n-1}` on the stack with
/// `d_{n-1}` on top. Checksum verified in-script.
pub trait WotsExt: Sized {
    fn wots_verify(self, pk: &WotsPublic) -> Self;
}

impl WotsExt for Builder {
    fn wots_verify(mut self, pk: &WotsPublic) -> Self {
        let ps = &pk.params;
        let total = ps.total_digits() as usize;
        // digits, last first: for each, check the hash chain via a pick list
        for k in 0..total {
            let i = total - 1 - k; // digit index being verified
            self = self
                .push_opcode(OP_SWAP)
                .push_opcode(OP_SIZE)
                .push_int(20)
                .push_opcode(OP_EQUALVERIFY)
                .push_opcode(OP_SWAP)
                .push_int(i64::from(MAX_DIGIT))
                .push_opcode(OP_MIN)
                .push_opcode(OP_DUP)
                .push_opcode(OP_TOALTSTACK)
                .push_int(i64::from(MAX_DIGIT.div_ceil(2)))
                .push_opcode(OP_2DUP)
                .push_opcode(OP_LESSTHAN)
                .push_opcode(OP_IF)
                .push_opcode(OP_DROP)
                .push_opcode(OP_TOALTSTACK);
            for _ in 0..MAX_DIGIT.div_ceil(2) {
                self = self.push_opcode(OP_HASH160);
            }
            self = self.push_opcode(OP_ELSE).push_opcode(OP_SUB).push_opcode(OP_TOALTSTACK).push_opcode(OP_ENDIF);
            for _ in 0..MAX_DIGIT / 2 {
                self = self.push_opcode(OP_DUP).push_opcode(OP_HASH160);
            }
            self = self.push_opcode(OP_FROMALTSTACK).push_opcode(OP_PICK).push_bytes(&pk.digits[i]).push_opcode(OP_EQUALVERIFY);
            for _ in 0..(MAX_DIGIT + 1) / 4 {
                self = self.push_opcode(OP_2DROP);
            }
        }
        // checksum: alt stack top is d_0
        self = self.push_opcode(OP_FROMALTSTACK).push_opcode(OP_DUP).push_opcode(OP_NEGATE);
        for _ in 1..ps.message_digits {
            self = self.push_opcode(OP_FROMALTSTACK).push_opcode(OP_TUCK).push_opcode(OP_SUB);
        }
        self = self.push_int(i64::from(MAX_DIGIT * ps.message_digits)).push_opcode(OP_ADD).push_opcode(OP_FROMALTSTACK);
        for _ in 0..ps.checksum_digits - 1 {
            for _ in 0..LOG2_BASE {
                self = self.push_opcode(OP_DUP).push_opcode(OP_ADD);
            }
            self = self.push_opcode(OP_FROMALTSTACK).push_opcode(OP_ADD);
        }
        self.push_opcode(OP_EQUALVERIFY)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_verify_roundtrip_and_forgery() {
        let ps = WotsParams::for_bytes(32);
        assert_eq!((ps.message_digits, ps.checksum_digits), (64, 3));
        let sk = WotsSecret::from_entropy(ps, [9u8; 32]);
        let pk = sk.public();
        let msg: Vec<u8> = (0..32u8).map(|i| i.wrapping_mul(77)).collect();
        let sig = sk.sign(&msg).unwrap();
        assert_eq!(pk.verify(&sig).unwrap(), msg);
        let items = sig.consumption_order();
        assert_eq!(WotsSig::from_consumption_order(ps, &items).unwrap(), sig);
        // forging a higher digit by hashing once more fails the checksum
        let mut forged = sig.clone();
        forged.digits[5] += 1;
        forged.hashes[5] = hash160(&forged.hashes[5]);
        assert!(pk.verify(&forged).is_err());
    }
}
