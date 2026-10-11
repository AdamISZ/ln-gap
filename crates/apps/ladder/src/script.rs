//! Rule leaves over re-revealed moves.
//!
//! A rule names the signed messages it reads (moves, by depth, or input
//! words), verifies each signature in turn (the first's reveal on top of
//! the witness), keeps only the digits its check uses (parked on the
//! altstack while the next is verified), then arranges its inputs in the
//! check's order (digits, nibbles of the poster's own witness, constants)
//! and runs the check, which consumes them and leaves nothing.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};

/// A signed message a rule reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Msg {
    /// Field `f` of the move at depth `d` (`Field(d, f)`).
    Field(u32, usize),
    /// Alice's input word `j` (published with the escalation).
    Word(usize),
    /// Field `f` of the hub's path link `l` (0 or 1), after the final move.
    Path(usize, usize),
    /// Alice's choice of hop to challenge, after path link `l`.
    Hop(usize),
}

/// One input of a rule's check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum In {
    /// Digit `d` of the rule's `m`-th message (in its verify order).
    M(usize, usize),
    /// Nibble `i` of the poster's own witness (the deepest items).
    W(usize),
    /// A constant.
    K(i64),
}

/// Inputs `M(m, d)` for each digit in `ds`.
pub fn ms(m: usize, ds: std::ops::Range<usize>) -> Vec<In> {
    ds.map(|d| In::M(m, d)).collect()
}

/// `n` zeros.
pub fn zeros(n: usize) -> Vec<In> {
    vec![In::K(0); n]
}

/// A word's eight nibbles, big-endian, as constants.
pub fn konst_word(v: u32) -> Vec<In> {
    (0..8).map(|i| In::K(i64::from((v >> (28 - 4 * i)) & 15))).collect()
}

/// A bytes value's nibbles as constants.
pub fn konst_bytes(b: &[u8]) -> Vec<In> {
    b.iter().flat_map(|x| [In::K(i64::from(x >> 4)), In::K(i64::from(x & 15))]).collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Item {
    W(usize),
    M(usize, usize),
    K,
}

/// The rule's script after `prefix`: verify `keys` in order, keeping the
/// digits `inputs` use; arrange `inputs` on top of the `wit` witness
/// nibbles (which sit below the reveals); run `check`; drop what's left;
/// push 1.
pub fn rule_script(prefix: Builder, keys: &[&WotsPublic], wit: usize, inputs: &[In], check: &ScriptBuf) -> ScriptBuf {
    let mut b = prefix;
    // the stack below the reveals: the witness nibbles, W(0) deepest
    let mut model: Vec<Item> = (0..wit).map(Item::W).collect();
    let mut parked: Vec<Item> = vec![];
    for (m, k) in keys.iter().enumerate() {
        let n = k.params.message_digits as usize;
        for &x in inputs {
            if let In::M(mm, d) = x {
                assert!(mm < keys.len() && (mm != m || d < n), "input {x:?} beyond its message");
            }
        }
        b = b.wots_verify(k);
        // d_{n-1} on top: park the kept digits, drop the others
        let keep = |d: usize| inputs.iter().any(|x| *x == In::M(m, d));
        let mut d = n;
        while d > 0 {
            d -= 1;
            if keep(d) {
                b = b.push_opcode(OP_TOALTSTACK);
                parked.push(Item::M(m, d));
            } else if d > 0 && !keep(d - 1) {
                b = b.push_opcode(OP_2DROP);
                d -= 1;
            } else {
                b = b.push_opcode(OP_DROP);
            }
        }
    }
    for x in parked.into_iter().rev() {
        b = b.push_opcode(OP_FROMALTSTACK);
        model.push(x);
    }
    // arrange: move each input to the top, copying it if a later input
    // uses it again
    for (j, &x) in inputs.iter().enumerate() {
        let item = match x {
            In::K(v) => {
                b = b.push_int(v);
                model.push(Item::K);
                continue;
            }
            In::W(i) => {
                assert!(i < wit, "witness nibble {i} of {wit}");
                Item::W(i)
            }
            In::M(m, d) => Item::M(m, d),
        };
        let pos = model.iter().rposition(|y| *y == item).expect("an input on the stack");
        let depth = model.len() - 1 - pos;
        let again = inputs[j + 1..].contains(&x);
        if again {
            b = pick(b, depth);
            model.push(Item::K);
        } else {
            b = roll(b, depth);
            let it = model.remove(pos);
            model.push(it);
        }
    }
    let n = inputs.len();
    let left = model.len() - n;
    let mut bytes = b.into_script().into_bytes();
    bytes.extend_from_slice(check.as_bytes());
    let mut b = Builder::from(bytes);
    for _ in 0..left / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    if left % 2 == 1 {
        b = b.push_opcode(OP_DROP);
    }
    b.push_opcode(OP_PUSHNUM_1).into_script()
}

fn pick(b: Builder, depth: usize) -> Builder {
    match depth {
        0 => b.push_opcode(OP_DUP),
        1 => b.push_opcode(OP_OVER),
        d => b.push_int(d as i64).push_opcode(OP_PICK),
    }
}

fn roll(b: Builder, depth: usize) -> Builder {
    match depth {
        0 => b,
        1 => b.push_opcode(OP_SWAP),
        2 => b.push_opcode(OP_ROT),
        d => b.push_int(d as i64).push_opcode(OP_ROLL),
    }
}

/// A one-time signature's witness items, wire order (lngap-pos's layout:
/// for each digit, the chain value then the digit).
pub fn wots_wire(sig: &lngap_lamport::winternitz::WotsSig) -> Vec<Vec<u8>> {
    lngap_pos_wire(sig)
}

fn lngap_pos_wire(sig: &lngap_lamport::winternitz::WotsSig) -> Vec<Vec<u8>> {
    let n = sig.params.total_digits() as usize;
    let mut w = Vec::with_capacity(2 * n);
    for i in 0..n {
        w.push(sig.hashes[i].to_vec());
        w.push(snum(sig.digits[i]));
    }
    w
}

/// A small number as a minimal script number push's bytes.
fn snum(d: u8) -> Vec<u8> {
    if d == 0 {
        vec![]
    } else {
        vec![d]
    }
}

/// A rule's witness below its gate: the poster's own nibbles (deepest),
/// then each message's reveal, the last verified first in wire order (so
/// the first verified is on top). `reveals[m]` is message `m`'s wire.
pub fn rule_wire(wit: &[u8], reveals: &[Vec<Vec<u8>>]) -> Vec<Vec<u8>> {
    let mut w = nibbles(wit);
    for r in reveals.iter().rev() {
        w.extend(r.iter().cloned());
    }
    w
}

/// Bytes as witness nibbles, the first deepest.
pub fn nibbles(bytes: &[u8]) -> Vec<Vec<u8>> {
    bytes.iter().flat_map(|x| [snum(x >> 4), snum(x & 15)]).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use lngap_lamport::winternitz::{WotsParams, WotsSecret};

    fn run(script: &ScriptBuf, wire: Vec<Vec<u8>>) -> bool {
        crate::rules::spends(script, wire).0
    }

    #[test]
    fn a_rule_reads_two_messages_and_its_witness() {
        let k1 = WotsSecret::from_entropy(WotsParams::for_bytes(3), [1; 32]);
        let k2 = WotsSecret::from_entropy(WotsParams::for_bytes(2), [2; 32]);
        let (s1, s2) = (k1.sign(&[0x12, 0x34, 0x56]).unwrap(), k2.sign(&[0xab, 0xcd]).unwrap());
        // check: message 1's digit 3 (4) + witness nibble 1 (5) == message
        // 2's digit 1 (b = 11) - 2; and message 1's digit 3 again is 4
        let check = {
            Builder::new()
                .push_opcode(OP_PUSHNUM_4)
                .push_opcode(OP_EQUALVERIFY)
                .push_opcode(OP_ROT)
                .push_opcode(OP_ROT)
                .push_opcode(OP_ADD)
                .push_opcode(OP_SWAP)
                .push_opcode(OP_SUB)
                .push_int(-2)
                .push_opcode(OP_EQUALVERIFY)
                .into_script()
        };
        // inputs: [M(0,3), W(1), M(1,1), K(2)... ] arranged as a, w, b, 2, a
        let inputs = [In::M(0, 3), In::W(1), In::M(1, 1), In::M(0, 3)];
        // stack before check: a w b a; check: a == 4; then a w b -> (a + w) - b == -2
        let script = rule_script(Builder::new(), &[&k1.public(), &k2.public()], 2, &inputs, &check);
        let wire = rule_wire(&[0x05], &[wots_wire(&s1), wots_wire(&s2)]);
        assert!(run(&script, wire.clone()), "4 + 5 - 11 == -2");
        let bad = rule_wire(&[0x06], &[wots_wire(&s1), wots_wire(&s2)]);
        assert!(!run(&script, bad), "4 + 6 - 11 != -2");
    }
}
