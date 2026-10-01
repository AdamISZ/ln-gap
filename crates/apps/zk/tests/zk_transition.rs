//! Experiment (ZK_Z3_PLAN.md, step 1): a transition leaf for the search
//! played in the channel. As in chess, each head carries the game's state
//! after the move; here the state (64 bytes, one BLAKE3 block) doesn't fit,
//! so the head carries its 20-byte digest and the entry body the state. A
//! disprove leaf takes both states (prior and new) as witness nibbles,
//! checks each against its head's digest, and fires if the transition rule
//! is broken. Does it fit under the 1,000-element stack limit, and at what
//! script size?
//!
//! The rule measured: the verifier's choice at round `r`. State nibbles:
//! lo 0..40, hi 40..80, mid 80..120 (the prover's midpoint), path 120..128
//! (the choices so far, a big-endian u32, bit `r` for round `r`). Legal:
//! left (lo, mid, path) or right (mid, hi, path + 2^r).
//!
//! The leaf, after the pair signature: the rule's verdict to the altstack
//! (picks through the register file), both digests to the altstack, drop
//! the file, then BLAKE3 the new state and the prior state against their
//! digests (each an equality verify), then the verdict.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_functions::hash::blake3;
use bitcoin_script_stack::stack::StackTracker;
use lngap_lamport::winternitz::{WotsExt, WotsPublic, WotsSecret};
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{disprove_witness, pair_key};
use lngap_pos::ttt::Layout;
use rand::{Rng, SeedableRng};

const GAME: u16 = 1;
const D: u32 = 2;
/// Where the state digest sits in each head (bytes 4..24).
const DIGEST_AT: usize = 4;
/// The state: one BLAKE3 block.
const N: usize = 64;
const LO: usize = 0;
const HI: usize = 40;
const MID: usize = 80;
const PATH: usize = 120;

fn digest(data: &[u8]) -> [u8; 20] {
    let mut h = ::blake3::Hasher::new();
    h.update(data);
    let mut out = [0u8; 20];
    h.finalize_xof().fill(&mut out);
    out
}

fn nib(s: &[u8], i: usize) -> u8 {
    if i % 2 == 0 {
        s[i / 2] >> 4
    } else {
        s[i / 2] & 15
    }
}

/// The path nibble holding round `r`'s bit, and the bit's value in it.
fn path_bit(r: u32) -> (usize, u8) {
    (PATH + 7 - (r / 4) as usize, 1 << (r % 4))
}

/// The rule, natively: is (old, new) a legal verifier's choice at round r?
fn legal(r: u32, old: &[u8], new: &[u8]) -> bool {
    let eq = |a: usize, b: usize, len: usize| (0..len).all(|k| nib(new, a + k) == nib(old, b + k));
    let (pk, bit) = path_bit(r);
    let path_right = (PATH..PATH + 8).all(|k| {
        if k == pk {
            nib(new, k) == nib(old, k) + bit
        } else {
            nib(new, k) == nib(old, k)
        }
    });
    let left = eq(LO, LO, 40) && eq(HI, MID, 40) && eq(PATH, PATH, 8);
    let right = eq(LO, MID, 40) && eq(HI, HI, 40) && path_right;
    left || right
}

/// The leaf's semantics: both states open their heads' digests and the
/// transition is illegal.
fn fires(r: u32, old: &[u8], new: &[u8], prior_head: &[u8; 48], new_head: &[u8; 48]) -> bool {
    digest(old)[..] == prior_head[DIGEST_AT..DIGEST_AT + 20]
        && digest(new)[..] == new_head[DIGEST_AT..DIGEST_AT + 20]
        && !legal(r, old, new)
}

/// BLAKE3 of the `n`-byte message below against the 40-nibble digest on
/// top; an equality verify.
fn check_script(n: u32) -> ScriptBuf {
    let mut st = StackTracker::new();
    let _ = st.define(n * 2, "msg");
    let _ = st.define(40, "digest");
    st.to_altstack();
    let h = blake3::blake3(&mut st, n, 5);
    let dg = st.from_altstack();
    st.equals(h, true, dg, true);
    st.get_script()
}

/// Emits a conjunction of nibble equalities over the two states below the
/// file: `new[a + k] == old[b + k] (+ add)`. `base` is the stack length
/// (states plus file) and `extra` the items already above it.
struct Rule {
    b: Builder,
    base: usize,
    file: usize,
}

impl Rule {
    /// Stack index (from the bottom) of old nibble i / new nibble i.
    fn old(&self, i: usize) -> usize {
        i
    }
    fn new(&self, i: usize) -> usize {
        2 * N + i
    }
    fn pick(mut self, idx: usize, extra: usize) -> Self {
        self.b = self
            .b
            .push_int((self.base - 1 - idx + extra) as i64)
            .push_opcode(OP_PICK);
        self
    }
    /// acc on top (extra items above base including acc = `extra`).
    fn and_eq(mut self, new_i: usize, old_i: usize, add: u8, extra: usize) -> Self {
        let (n, o) = (self.new(new_i), self.old(old_i));
        self = self.pick(n, extra).pick(o, extra + 1);
        if add != 0 {
            self.b = self.b.push_int(add as i64).push_opcode(OP_ADD);
        }
        self.b = self.b.push_opcode(OP_EQUAL).push_opcode(OP_BOOLAND);
        self
    }
    fn branch(
        mut self,
        pairs: &[(usize, usize, usize)],
        path_add: Option<(usize, u8)>,
        extra: usize,
    ) -> Self {
        self.b = self.b.push_opcode(OP_PUSHNUM_1);
        for &(a, b, len) in pairs {
            for k in 0..len {
                self = self.and_eq(a + k, b + k, 0, extra + 1);
            }
        }
        for k in PATH..PATH + 8 {
            let add = match path_add {
                Some((pk, bit)) if pk == k => bit,
                _ => 0,
            };
            self = self.and_eq(k, k, add, extra + 1);
        }
        self
    }
}

fn leaf(r: u32, key: &WotsPublic) -> ScriptBuf {
    let l = Layout::at(D, GAME, mover_at(D));
    let base = 4 * N + l.file;
    let mut rule = Rule {
        b: Builder::new().wots_verify(key),
        base,
        file: l.file,
    };
    rule = rule.branch(&[(LO, LO, 40), (HI, MID, 40)], None, 0);
    rule = rule.branch(&[(LO, MID, 40), (HI, HI, 40)], Some(path_bit(r)), 1);
    let _ = rule.file;
    let b = rule
        .b
        .push_opcode(OP_BOOLOR)
        .push_opcode(OP_NOT)
        .push_opcode(OP_TOALTSTACK);
    let mut bytes = b.into_script().into_bytes();
    bytes.extend_from_slice(two_checks(N, N).as_bytes());
    bytes.extend_from_slice(
        Builder::new()
            .push_opcode(OP_FROMALTSTACK)
            .into_script()
            .as_bytes(),
    );
    ScriptBuf::from_bytes(bytes)
}

/// With `[prior state (a bytes), new state (b bytes), file]` on the stack
/// (anything else on the altstack): check both states against their
/// heads' digests, leaving the stack empty and the altstack as found.
/// BitVMX's BLAKE3 gadget finds its tables by OP_DEPTH, so the message it
/// hashes must be alone on the main stack: the new state and both digests
/// wait on the altstack while the prior state is hashed.
fn two_checks(a: usize, b_: usize) -> ScriptBuf {
    let l = Layout::at(D, GAME, mover_at(D));
    let file = l.file;
    let mut b = Builder::new();
    // New digest, then prior digest, to the altstack.
    for d0 in [l.new + 2 * DIGEST_AT, l.prior.unwrap() + 2 * DIGEST_AT] {
        for j in (d0..d0 + 40).rev() {
            b = b
                .push_int((file - 1 - j) as i64)
                .push_opcode(OP_PICK)
                .push_opcode(OP_TOALTSTACK);
        }
    }
    for _ in 0..file / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    // Prior digest back on top; the new state under it to the altstack
    // (top first, so it comes back in order).
    for _ in 0..40 {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    for _ in 0..2 * b_ {
        b = b
            .push_int(40)
            .push_opcode(OP_ROLL)
            .push_opcode(OP_TOALTSTACK);
    }
    let mut bytes = b.into_script().into_bytes();
    bytes.extend_from_slice(check_script(a as u32).as_bytes());
    let mut b = Builder::new();
    for _ in 0..2 * b_ + 40 {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    bytes.extend_from_slice(b.into_script().as_bytes());
    bytes.extend_from_slice(check_script(b_ as u32).as_bytes());
    ScriptBuf::from_bytes(bytes)
}

fn nibbles(data: &[u8]) -> Vec<Vec<u8>> {
    data.iter()
        .flat_map(|b| [b >> 4, b & 15])
        .map(|v| if v == 0 { vec![] } else { vec![v] })
        .collect()
}

fn heads(old: &[u8], new: &[u8]) -> ([u8; 48], [u8; 48]) {
    let (mut p, mut n) = ([0u8; 48], [0u8; 48]);
    p[DIGEST_AT..DIGEST_AT + 20].copy_from_slice(&digest(old));
    n[DIGEST_AT..DIGEST_AT + 20].copy_from_slice(&digest(new));
    (p, n)
}

fn witness(sk: &WotsSecret, old: &[u8], new: &[u8], ph: &[u8; 48], nh: &[u8; 48]) -> Vec<Vec<u8>> {
    let mut w = nibbles(old);
    w.extend(nibbles(new));
    w.extend(disprove_witness(
        &sk.sign(&[ph.as_slice(), nh.as_slice()].concat()).unwrap(),
    ));
    w
}

/// (spends, peak stack).
fn run(script: &ScriptBuf, w: Vec<Vec<u8>>) -> (bool, usize) {
    match lngap_script32::sim::run_peak(script.as_script(), w) {
        Ok((st, peak)) => (st.len() == 1 && !st[0].is_empty() && st[0] != [0x80], peak),
        Err(_) => (false, 0),
    }
}

/// An honest round: a state, and the verifier's legal choice.
fn honest(rng: &mut impl Rng, r: u32, right: bool) -> (Vec<u8>, Vec<u8>) {
    let mut old: Vec<u8> = (0..N).map(|_| rng.gen()).collect();
    // The path: bits below r arbitrary, bit r and above clear.
    let path: u32 = rng.gen::<u32>() & ((1u32 << r) - 1);
    old[60..64].copy_from_slice(&path.to_be_bytes());
    let mut new = old.clone();
    if right {
        new[0..20].copy_from_slice(&old[40..60]);
        new[60..64].copy_from_slice(&(path | 1 << r).to_be_bytes());
    } else {
        new[20..40].copy_from_slice(&old[40..60]);
    }
    // The new mid is free (the prover's next move sets it).
    for b in &mut new[40..60] {
        *b = rng.gen();
    }
    (old, new)
}

#[test]
fn transition_leaf_limits() {
    let sk = pair_key([11; 32]);
    let mut rng = rand::rngs::StdRng::seed_from_u64(12);
    for r in [1u32, 13, 28] {
        let script = leaf(r, &sk.public());
        let mut peaks = Vec::new();
        for right in [false, true] {
            let (old, new) = honest(&mut rng, r, right);
            assert!(legal(r, &old, &new));
            let (ph, nh) = heads(&old, &new);
            let (ok, peak) = run(&script, witness(&sk, &old, &new, &ph, &nh));
            assert!(!ok, "round {r}: an honest choice must not be disprovable");
            assert_eq!(ok, fires(r, &old, &new, &ph, &nh));
            // Malformations: each must fire, with the states opening the heads.
            let bad: Vec<(&str, Box<dyn Fn(&mut Vec<u8>)>)> = vec![
                ("lo not copied", Box::new(|s: &mut Vec<u8>| s[3] ^= 0x10)),
                ("hi not copied", Box::new(|s: &mut Vec<u8>| s[39] ^= 1)),
                (
                    "path bit wrong",
                    Box::new(move |s: &mut Vec<u8>| s[63 - (r / 8) as usize] ^= 1 << (r % 8)),
                ),
                (
                    "path other bit",
                    Box::new(move |s: &mut Vec<u8>| s[60 + ((r as usize / 8 + 1) % 4)] ^= 0x40),
                ),
            ];
            for (what, f) in &bad {
                let mut nb = new.clone();
                f(&mut nb);
                let (ph, nh2) = heads(&old, &nb);
                let fire = fires(r, &old, &nb, &ph, &nh2);
                let (ok, peak) = run(&script, witness(&sk, &old, &nb, &ph, &nh2));
                assert_eq!(ok, fire, "round {r} {what}: script and mirror disagree");
                assert!(ok, "round {r} {what}: must fire");
                peaks.push(peak);
                // The same malformed state against a head it doesn't open.
                let (ok, _) = run(&script, witness(&sk, &old, &nb, &ph, &nh));
                assert!(
                    !ok,
                    "round {r} {what}: a state that doesn't open its head must not spend"
                );
                let mut ob = old.clone();
                ob[10] ^= 2;
                let (ok, _) = run(&script, witness(&sk, &ob, &nb, &ph, &nh2));
                assert!(
                    !ok,
                    "round {r} {what}: a prior state that doesn't open its head must not spend"
                );
            }
            peaks.push(peak);
        }
        let max = peaks.iter().max().unwrap();
        println!(
            "round {r:>2}: leaf {} B, peak {max} (limit 1000)",
            script.len()
        );
        assert!(*max <= 1000, "over the stack limit");
    }
}

/// Random transitions: script == mirror.
#[test]
fn transition_leaf_matches_mirror() {
    let sk = pair_key([13; 32]);
    let mut rng = rand::rngs::StdRng::seed_from_u64(14);
    let r = 6;
    let script = leaf(r, &sk.public());
    let (mut fired, mut held) = (0, 0);
    for i in 0..40 {
        let (old, mut new) = honest(&mut rng, r, i % 2 == 0);
        if i % 4 >= 2 {
            let k = rng.gen_range(0..N);
            new[k] ^= 1 << rng.gen_range(0..8);
        }
        let (ph, nh) = heads(&old, &new);
        let (ok, _) = run(&script, witness(&sk, &old, &new, &ph, &nh));
        assert_eq!(ok, fires(r, &old, &new, &ph, &nh), "case {i}");
        if ok {
            fired += 1
        } else {
            held += 1
        }
    }
    println!("{fired} fired, {held} held");
    assert!(fired > 0 && held > 0);
}

/// How far two state checks go: the leaf with no rule, states of `a` and
/// `b` bytes (a 4-ary state is two blocks).
#[test]
fn two_digest_limits() {
    let sk = pair_key([15; 32]);
    let mut rng = rand::rngs::StdRng::seed_from_u64(16);
    println!(
        "{:>5} {:>5} {:>9} {:>6}",
        "prior", "new", "script B", "peak"
    );
    for (a, bsz) in [(64usize, 64usize), (64, 128), (128, 64), (128, 128)] {
        let mut bytes = Builder::new()
            .wots_verify(&sk.public())
            .into_script()
            .into_bytes();
        bytes.extend_from_slice(two_checks(a, bsz).as_bytes());
        bytes.extend_from_slice(
            Builder::new()
                .push_opcode(OP_PUSHNUM_1)
                .into_script()
                .as_bytes(),
        );
        let script = ScriptBuf::from_bytes(bytes);
        let old: Vec<u8> = (0..a).map(|_| rng.gen()).collect();
        let new: Vec<u8> = (0..bsz).map(|_| rng.gen()).collect();
        let (ph, nh) = heads(&old, &new);
        let mut w = nibbles(&old);
        w.extend(nibbles(&new));
        w.extend(disprove_witness(
            &sk.sign(&[ph.as_slice(), nh.as_slice()].concat()).unwrap(),
        ));
        let res = lngap_script32::sim::run_peak(script.as_script(), w);
        let (ok, peak) = match &res {
            Ok((st, p)) => (st.len() == 1 && st[0] == [1], *p),
            Err(_) => (false, 0),
        };
        println!(
            "{a:>5} {bsz:>5} {:>9} {:>6}  {}",
            script.len(),
            if ok { peak.to_string() } else { "-".into() },
            if ok {
                "spends".to_string()
            } else {
                format!("fails: {:?}", res.err())
            }
        );
    }
}

/// The transition leaf on regtest, behind the challenger's key: the node
/// accepts the disprove of a malformed choice and rejects it for an honest
/// one.
#[test]
fn transition_leaf_on_regtest() {
    use bitcoin::key::Keypair;
    use bitcoin::{Amount, TxOut};
    use lngap_btc::keys::{xonly, Seed};
    use lngap_btc::regtest::Regtest;
    use lngap_btc::script::BuilderExt;
    use lngap_btc::sighash::sign_tapscript;
    use lngap_btc::taptree::{Leaf, TapTree};
    use lngap_btc::tx::{build_spend, Timelock};
    use lngap_btc::witness::tapscript_witness;

    let rt = Regtest::start().unwrap();
    let sk = pair_key([17; 32]);
    let challenger: Keypair = Seed::from_label("transition challenger").keypair("pay");
    let mut rng = rand::rngs::StdRng::seed_from_u64(18);
    let r = 20;
    let mut b = Builder::new()
        .checksigverify(&xonly(&challenger))
        .into_script()
        .into_bytes();
    b.extend_from_slice(leaf(r, &sk.public()).as_bytes());
    let script = ScriptBuf::from_bytes(b);
    let tree = TapTree::new(vec![Leaf::new(
        "transition",
        script.clone(),
        Timelock::NONE,
    )])
    .unwrap();
    let spend = |old: &[u8], new: &[u8]| {
        let (op, prev) = rt
            .fund(&tree.script_pubkey(), Amount::from_sat(1_000_000))
            .unwrap();
        let mut tx = build_spend(
            op,
            &Timelock::NONE,
            vec![TxOut {
                value: Amount::from_sat(900_000),
                script_pubkey: tree.script_pubkey(),
            }],
        );
        let sig =
            sign_tapscript(&challenger, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
        let (ph, nh) = heads(old, new);
        let mut w = witness(&sk, old, new, &ph, &nh);
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness =
            tapscript_witness(&w, &script, &tree.control_block("transition").unwrap());
        tx
    };
    let (old, new) = honest(&mut rng, r, true);
    let err = rt
        .test_accept(&spend(&old, &new))
        .expect_err("an honest choice");
    let mut bad = new.clone();
    bad[5] ^= 0x01; // lo not copied from the old mid
    let tx = spend(&old, &bad);
    let (txid, h) = rt.send_and_confirm(&tx).unwrap();
    println!("malformed choice disproved: {txid} confirmed at {h}: {} vB, {} WU, leaf {} B; honest rejected ({err})", tx.vsize(), tx.weight().to_wu(), script.len());
}
