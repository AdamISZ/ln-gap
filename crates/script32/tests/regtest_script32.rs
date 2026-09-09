//! Every word gadget against its native counterpart, through the interpreter.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_script32::sha::{round_body, round_native, schedule_body, schedule_native, K, TABLES};
use lngap_script32::{Stack, Tables};
use rand::{Rng, SeedableRng};

/// Witness elements for a word in consumption order (least-significant nibble first).
fn word_witness(w: u32) -> Vec<Vec<u8>> {
    (0..8).map(|i| { let n = ((w >> (4 * i)) & 15) as u8; if n == 0 { vec![] } else { vec![n] } }).collect()
}

fn expect_word(mut b: Builder, w: u32) -> Builder {
    for i in 0..8 {
        let n = ((w >> (4 * i)) & 15) as i64;
        b = if n == 0 { b.push_opcode(OP_PUSHBYTES_0) } else { b.push_int(n) };
        b = b.push_opcode(OP_EQUALVERIFY);
    }
    b
}

struct Rig {
    rt: Regtest,
    sink: ScriptBuf,
}

impl Rig {
    fn new() -> Rig {
        let rt = Regtest::start().unwrap();
        let sink = TapTree::new(vec![Leaf::new("x", Builder::new().push_int(1).into_script(), Timelock::NONE)]).unwrap().script_pubkey();
        Rig { rt, sink }
    }
    /// Build a leaf: inputs (pushed in order, last on top) -> tables -> `f` -> drop tables -> expect outputs.
    fn leaf(&self, tables: Tables, n_inputs: usize, f: impl Fn(&mut Stack), outputs: &[u32]) -> ScriptBuf {
        let mut s = Stack::new(Builder::new(), tables);
        s.roll_inputs_above(8 * n_inputs);
        f(&mut s);
        s.drop_tables(8 * outputs.len());
        let mut b = s.into_builder();
        // outputs: last word on top; compare top-down
        for w in outputs.iter().rev() {
            b = expect_word(b, *w);
        }
        b.push_opcode(OP_PUSHNUM_1).into_script()
    }
    /// Spend the leaf with `inputs` (in push order) and return Ok(vsize) or the rejection.
    fn run(&self, leaf: &ScriptBuf, inputs: &[u32]) -> Result<u64, String> {
        let tree = TapTree::new(vec![Leaf::new("g", leaf.clone(), Timelock::NONE)]).unwrap();
        let (op, _p) = self.rt.fund(&tree.script_pubkey(), Amount::from_sat(100_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(80_000), script_pubkey: self.sink.clone() }]);
        let mut w = WitnessStack::new();
        // consumption order: last-pushed word first
        for word in inputs.iter().rev() {
            w.extend(word_witness(*word));
        }
        tx.input[0].witness = w.build(leaf, &tree.control_block("g").unwrap());
        self.rt.test_accept(&tx)
    }
    fn check(&self, name: &str, tables: Tables, inputs: &[u32], outputs: &[u32], f: impl Fn(&mut Stack)) {
        let leaf = self.leaf(tables, inputs.len(), f, outputs);
        match self.run(&leaf, inputs) {
            Ok(vs) => eprintln!("{name}: ok, script {} B, vsize {vs}", leaf.len()),
            Err(e) => panic!("{name} inputs {inputs:x?} expected {outputs:x?}: {e}"),
        }
    }
}

#[test]
fn word_gadgets() {
    let rig = Rig::new();
    let mut rng = rand::rngs::StdRng::seed_from_u64(7);
    let t = TABLES;
    for _ in 0..3 {
        let (a, b): (u32, u32) = (rng.gen(), rng.gen());
        rig.check("add", t, &[a, b], &[a.wrapping_add(b)], |s| s.add_word());
        rig.check("xor", t, &[a, b], &[a ^ b], |s| s.xor_word());
        rig.check("and", t, &[a, b], &[a & b], |s| s.and_word());
        rig.check("not", t, &[a], &[!a], |s| s.not_word());
        for n in [2u32, 6, 7, 11, 13, 17, 18, 19, 22, 25] {
            rig.check(&format!("rotr{n}"), t, &[a], &[a.rotate_right(n)], |s| s.rotr_word(n));
        }
        for n in [3u32, 10] {
            rig.check(&format!("shr{n}"), t, &[a], &[a >> n], |s| s.shr_word(n));
        }
    }
    // edge values
    rig.check("add-carry", t, &[0xffff_ffff, 1], &[0], |s| s.add_word());
    rig.check("add-zero", t, &[0, 0], &[0], |s| s.add_word());
    rig.check("rotr-ones", t, &[0xffff_ffff], &[0xffff_ffff], |s| s.rotr_word(13));
    // a wrong expectation must fail
    let leaf = rig.leaf(t, 2, |s| s.add_word(), &[3]);
    assert!(rig.run(&leaf, &[1, 1]).is_err());
}

#[test]
fn sha_round_and_schedule() {
    let rig = Rig::new();
    let mut rng = rand::rngs::StdRng::seed_from_u64(11);
    for i in [0usize, 17, 63] {
        let state: [u32; 8] = core::array::from_fn(|_| rng.gen());
        let w: u32 = rng.gen();
        let expected = round_native(&state, w, K[i]);
        let mut inputs: Vec<u32> = state.to_vec();
        inputs.push(w);
        rig.check(&format!("round{i}"), TABLES, &inputs, &expected, |s| round_body(s, K[i]));
    }
    for _ in 0..2 {
        let (w2, w7, w15, w16): (u32, u32, u32, u32) = (rng.gen(), rng.gen(), rng.gen(), rng.gen());
        rig.check("schedule", TABLES, &[w2, w7, w15, w16], &[schedule_native(w2, w7, w15, w16)], |s| schedule_body(s));
    }
    // wrong output must fail
    let state: [u32; 8] = core::array::from_fn(|_| rng.gen());
    let mut bad = round_native(&state, 5, K[3]);
    bad[0] ^= 1;
    let mut inputs: Vec<u32> = state.to_vec();
    inputs.push(5);
    let leaf = rig.leaf(TABLES, 9, |s| round_body(s, K[3]), &bad);
    assert!(rig.run(&leaf, &inputs).is_err());
}

/// Every gadget, exhaustively over shift amounts and many random inputs, on the native mini-interpreter.
#[test]
fn sim_gadgets() {
    use lngap_script32::sim;
    let mut rng = rand::rngs::StdRng::seed_from_u64(3);
    let run = |f: &dyn Fn(&mut Stack), inputs: &[u32]| -> Vec<u32> {
        let mut s = Stack::new(Builder::new(), TABLES);
        s.roll_inputs_above(8 * inputs.len());
        f(&mut s);
        let script = s.into_builder().into_script();
        let mut stack = Vec::new();
        for w in inputs {
            for i in (0..8).rev() {
                stack.push(((w >> (4 * i)) & 15) as i64);
            }
        }
        let out = sim::run_nums(&script, stack).unwrap();
        let out = &out[TABLES.size()..];
        out.chunks(8).map(|c| c.iter().fold(0u32, |acc, n| (acc << 4) | *n as u32)).collect()
    };
    for _ in 0..50 {
        let (a, b): (u32, u32) = (rng.gen(), rng.gen());
        assert_eq!(run(&|s| s.add_word(), &[a, b]), vec![a.wrapping_add(b)]);
        assert_eq!(run(&|s| s.xor_word(), &[a, b]), vec![a ^ b]);
        assert_eq!(run(&|s| s.and_word(), &[a, b]), vec![a & b]);
        assert_eq!(run(&|s| s.not_word(), &[a]), vec![!a]);
        for n in 1..32u32 {
            assert_eq!(run(&|s| s.rotr_word(n), &[a]), vec![a.rotate_right(n)], "rotr{n} of {a:08x}");
            assert_eq!(run(&|s| s.shr_word(n), &[a]), vec![a >> n], "shr{n} of {a:08x}");
        }
    }
}

/// Round and schedule bodies on the native mini-interpreter, many random inputs.
#[test]
fn sim_sha_pieces() {
    use lngap_script32::sim;
    let mut rng = rand::rngs::StdRng::seed_from_u64(5);
    let run = |f: &dyn Fn(&mut Stack), inputs: &[u32]| -> Vec<u32> {
        let mut s = Stack::new(Builder::new(), TABLES);
        s.roll_inputs_above(8 * inputs.len());
        f(&mut s);
        let script = s.into_builder().into_script();
        let mut stack = Vec::new();
        for w in inputs {
            for i in (0..8).rev() {
                stack.push(((w >> (4 * i)) & 15) as i64);
            }
        }
        let out = sim::run_nums(&script, stack).unwrap();
        let out = &out[TABLES.size()..];
        out.chunks(8).map(|c| c.iter().fold(0u32, |acc, n| (acc << 4) | *n as u32)).collect()
    };
    for r in 0..64 {
        let state: [u32; 8] = core::array::from_fn(|_| rng.gen());
        let w: u32 = rng.gen();
        let mut inputs = state.to_vec();
        inputs.push(w);
        assert_eq!(run(&|s| round_body(s, K[r]), &inputs), round_native(&state, w, K[r]).to_vec(), "round {r}");
        let (w2, w7, w15, w16): (u32, u32, u32, u32) = (rng.gen(), rng.gen(), rng.gen(), rng.gen());
        assert_eq!(run(&|s| schedule_body(s), &[w2, w7, w15, w16]), vec![schedule_native(w2, w7, w15, w16)]);
    }
}

#[test]
fn sim_add_states_and_differs() {
    use lngap_script32::sha::{add_states, differs_and_finish};
    use lngap_script32::sim;
    let mut rng = rand::rngs::StdRng::seed_from_u64(9);
    let nib = |w: u32| -> Vec<i64> { (0..8).rev().map(|i| ((w >> (4 * i)) & 15) as i64).collect() };
    for _ in 0..10 {
        let a: [u32; 8] = core::array::from_fn(|_| rng.gen());
        let b: [u32; 8] = core::array::from_fn(|_| rng.gen());
        let mut claimed: [u32; 8] = core::array::from_fn(|i| a[i].wrapping_add(b[i]));
        let lie = rng.gen_bool(0.5);
        if lie {
            claimed[rng.gen_range(0..8)] ^= 1 << rng.gen_range(0..32);
        }
        let mut s = Stack::new(Builder::new(), TABLES);
        s.roll_inputs_above(8 * 24);
        add_states(&mut s);
        differs_and_finish(&mut s, 64);
        let script = s.into_builder().into_script();
        let mut stack: Vec<i64> = Vec::new();
        // the claimed value sits below the two operands; the sum lands on top of it
        for w in claimed.iter().chain(a.iter()).chain(b.iter()) {
            stack.extend(nib(*w));
        }
        let out = sim::run_nums(&script, stack).unwrap();
        assert_eq!(out, vec![i64::from(lie)], "lie={lie}");
    }
}
