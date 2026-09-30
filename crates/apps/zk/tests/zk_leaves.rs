//! Z1 (DEMOS_PLAN.md section 3): BitVMX terminal challenges as LN-GAP
//! disprove leaves, over the first five steps of the Groth16 verifier ELF
//! (`zkverifier-new-mul.elf` on the repo's sample input, from `emulator
//! execute --trace --debug`: addi, jal, addi, sw, sw).
//!
//! - the native step hash reproduces the emulator's;
//! - `zk_trace_hash` agrees with its mirror on honest steps and on
//!   corrupted ones (the claimed hash, the write record, the prior hash);
//! - the execution leaves (addi, jal, sw): an honest step does not fire;
//!   each corrupted write field (address, value, pc, micro) fires; a leaf
//!   of the wrong instruction class never fires (BitVMX's opcode
//!   assertions); and a read record inconsistent with its opcode (a wrong
//!   register address) does not fire either, with the write corrupted
//!   too: the gap the inversion leaves, recorded here;
//! - peak stack under 1,000 for every leaf and case;
//! - on regtest, with the challenger's key in front as in every disprove
//!   leaf: honest steps are not disprovable, and a corrupted hash and a
//!   corrupted addi result are disproved and confirmed.

use std::sync::Arc;

use bitcoin::key::Keypair;
use bitcoin::opcodes::all::OP_CHECKSIGVERIFY;
use bitcoin::script::Builder;
use bitcoin::{Amount, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::{xonly, Seed};
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{disprove_witness, pair_key};
use lngap_pos::ttt::{Layout, PosLeaf};
use lngap_zk::*;

const GAME: u16 = 1;
/// The depth of the parked pair (the leaves need a prior head).
const D: u32 = 2;

/// Step 0's hash, then each step's trace line: read 1 (address, value),
/// read 2 (address, value), pc, micro, opcode, write (address, value,
/// pc, micro), memory witness, hash.
const H0: &str = "99d44d377bc5936d8cb7f5df90713d84c7587739";
#[rustfmt::skip]
const TRACE: [(u32, u32, u32, u32, u32, u8, u32, u32, u32, u32, u8, u8, &str); 5] = [
    (0xf0000000, 0x00000000, 0x00000000, 0x00000000, 0x8005d260, 0, 0x00000513, 0xf0000028, 0x00000000, 0x8005d264, 0, 0x08, "09229b16d156a5a4eb05e8eea147fbcbe69be904"),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x8005d264, 0, 0xbe8a30ef, 0xf0000004, 0x8005d268, 0x8000064c, 0, 0x28, "6ecf50a650b21964959fb7f005abc2e920c1403f"),
    (0xf0000008, 0xe0800000, 0x00000000, 0x00000000, 0x8000064c, 0, 0x81010113, 0xf0000008, 0xe07ff810, 0x80000650, 0, 0x08, "838e56fe3ff63566e703ec6ec789c62bb6cda9ef"),
    (0xf0000008, 0xe07ff810, 0xf0000004, 0x8005d268, 0x80000650, 0, 0x7e112623, 0xe07ffffc, 0x8005d268, 0x80000654, 0, 0x01, "265207ada14da925e9c2bf599ac63a2d9474f3f6"),
    (0xf0000008, 0xe07ff810, 0xf0000020, 0x00000000, 0x80000654, 0, 0x7e812423, 0xe07ffff8, 0x00000000, 0x80000658, 0, 0x01, "4cc77b4f5483f36a05877df2798ec756ec296c18"),
];

fn h20(s: &str) -> [u8; 20] {
    hex::decode(s).unwrap().try_into().unwrap()
}

/// The five steps as final-step records.
fn trace() -> Vec<FinalStep> {
    let mut prev = h20(H0);
    TRACE
        .iter()
        .map(|&(r1a, r1v, r2a, r2v, pc, micro, opcode, wa, wv, wpc, wm, mw, h)| {
            let s = FinalStep {
                prev_hash: prev,
                read: Read { mem_witness: mw, read_1_addr: r1a, read_1_value: r1v, read_2_addr: r2a, read_2_value: r2v, pc, micro, opcode },
                write: Step { write_addr: wa, write_value: wv, pc: wpc, micro: wm },
                hash: h20(h),
                witness: 0,
            };
            prev = s.hash;
            s
        })
        .collect()
}

fn heads(s: &FinalStep) -> ([u8; 48], [u8; 48]) {
    (s.prior_head(GAME, D - 1, mover_at(D - 1)), s.new_head(GAME, D, mover_at(D)))
}

fn reveal(sk: &WotsSecret, p: &[u8; 48], n: &[u8; 48]) -> Vec<Vec<u8>> {
    disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap())
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

/// Run a leaf in the simulator: (fired, peak stack).
fn run(leaf: &PosLeaf, sk: &WotsSecret, s: &FinalStep) -> (bool, usize) {
    let (p, n) = heads(s);
    match lngap_script32::sim::run_peak(leaf.script.as_script(), reveal(sk, &p, &n)) {
        Ok((st, peak)) => {
            assert_eq!(st.len(), 1, "{}: cleanstack", leaf.name);
            (truthy(&st[0]), peak)
        }
        Err(_) => (false, 0),
    }
}

/// The write-record corruptions: address, value, pc, micro.
fn corruptions(s: &FinalStep) -> Vec<(&'static str, FinalStep)> {
    let w = s.write;
    vec![
        ("write address", FinalStep { write: Step { write_addr: w.write_addr ^ 4, ..w }, ..*s }),
        ("write value", FinalStep { write: Step { write_value: w.write_value ^ 0x100, ..w }, ..*s }),
        ("next pc", FinalStep { write: Step { pc: w.pc ^ 8, ..w }, ..*s }),
        ("micro", FinalStep { write: Step { micro: w.micro ^ 1, ..w }, ..*s }),
    ]
}

#[test]
fn step_hash_reproduces_the_emulator() {
    for (i, s) in trace().iter().enumerate() {
        assert_eq!(step_hash(&s.prev_hash, &s.write), s.hash, "step {}", i + 1);
    }
}

#[test]
fn trace_hash_leaf_agrees_with_its_mirror() {
    let sk = pair_key([7; 32]);
    let leaf = trace_hash_leaf(&Layout::at(D, GAME, mover_at(D)), &sk.public());
    println!("{}: {} B of script ({} B BitVMX's challenge)", leaf.name, leaf.script.len(), trace_hash_script().len());
    let mut peak = 0;
    for s in trace() {
        let mut cases = vec![(s, false)];
        let mut bad = s;
        bad.hash[19] ^= 1;
        cases.push((bad, true));
        cases.extend(corruptions(&s).into_iter().map(|(_, c)| (c, true)));
        let mut bp = s;
        bp.prev_hash[0] ^= 0x80;
        cases.push((bp, true));
        for (c, fires) in cases {
            let (p, n) = heads(&c);
            assert_eq!((leaf.fires)(&p, &n), fires, "mirror");
            let (ran, pk) = run(&leaf, &sk, &c);
            assert_eq!(ran, fires, "script vs mirror");
            peak = peak.max(pk);
        }
    }
    println!("peak stack: {peak}");
    assert!(peak <= 1000);
}

/// The execution leaf for step `i`'s instruction class. Its mirror, for
/// these cases (the step's honest read record): the committed write is
/// not the emulator's.
fn exec_leaf_for(sk: &WotsSecret, i: usize) -> PosLeaf {
    let s = trace()[i];
    let ins = riscv_decode::decode(s.read.opcode).unwrap();
    let honest = s.write;
    let fires = Arc::new(move |p: &[u8; 48], n: &[u8; 48]| FinalStep::parse(p, n).write != honest);
    exec_leaf(&Layout::at(D, GAME, mover_at(D)), &sk.public(), &ins, s.read.micro, fires)
}

#[test]
fn exec_leaves() {
    let sk = pair_key([8; 32]);
    let steps = trace();
    // steps 1 (addi), 2 (jal), 4 (sw)
    let leaves: Vec<(usize, PosLeaf)> = [0, 1, 3].iter().map(|&i| (i, exec_leaf_for(&sk, i))).collect();
    let mut peak = 0;
    for (i, leaf) in &leaves {
        let s = steps[*i];
        println!("{}: {} B of script", leaf.name, leaf.script.len());
        let (ran, pk) = run(leaf, &sk, &s);
        assert!(!ran, "{}: fired on the honest step {}", leaf.name, i + 1);
        peak = peak.max(pk);
        for (what, c) in corruptions(&s) {
            let (p, n) = heads(&c);
            assert!((leaf.fires)(&p, &n));
            let (ran, pk) = run(leaf, &sk, &c);
            assert!(ran, "{}: did not fire on a corrupted {what} at step {}", leaf.name, i + 1);
            peak = peak.max(pk);
        }
        // a leaf of another class never fires on this step, honest or not
        for (j, other) in &leaves {
            if j == i {
                continue;
            }
            for (_, c) in corruptions(&s) {
                assert!(!run(other, &sk, &c).0, "{} fired on step {} ({})", other.name, i + 1, leaf.name);
            }
        }
        // the gap: a read record inconsistent with the opcode (read 1 from
        // the wrong register) is caught by BitVMX's assertion, which in the
        // inverted leaf means no fire, even with the write corrupted
        let mut bad = corruptions(&s)[1].1;
        if s.read.read_1_addr != 0 {
            bad.read.read_1_addr ^= 4;
            assert!(!run(leaf, &sk, &bad).0, "{}: fired on an inconsistent read record", leaf.name);
        }
    }
    println!("peak stack: {peak}");
    assert!(peak <= 1000);
}

#[test]
fn leaves_on_regtest() {
    let rt = Regtest::start().unwrap();
    let sk = pair_key([9; 32]);
    let challenger: Keypair = Seed::from_label("zk challenger").keypair("pay");
    let l = Layout::at(D, GAME, mover_at(D));
    let steps = trace();

    let spend = |pl: &PosLeaf, s: &FinalStep| -> Transaction {
        // the challenger's key in front, as refuted_tree does for every leaf
        let mut bytes = Builder::new().push_x_only_key(&xonly(&challenger)).push_opcode(OP_CHECKSIGVERIFY).into_script().into_bytes();
        bytes.extend_from_slice(pl.script.as_bytes());
        let script = ScriptBuf::from_bytes(bytes);
        let name = format!("disprove_{}", pl.name);
        let tree = TapTree::new(vec![Leaf::new(name.clone(), script.clone(), Timelock::NONE)]).unwrap();
        let control = tree.control_block(&name).unwrap();
        let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
        let sig = sign_tapscript(&challenger, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
        let (p, n) = heads(s);
        let mut w = reveal(&sk, &p, &n);
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &script, &control);
        tx
    };

    let th = trace_hash_leaf(&l, &sk.public());
    let ex = exec_leaf_for(&sk, 0);
    for (leaf, honest, cheat) in [
        (&th, steps[2], FinalStep { hash: [0x5a; 20], ..steps[2] }),
        (&ex, steps[0], corruptions(&steps[0])[1].1),
    ] {
        let err = rt.test_accept(&spend(leaf, &honest)).expect_err("an honest step must not be disprovable");
        println!("{}: honest step rejected ({err})", leaf.name);
        let tx = spend(leaf, &cheat);
        rt.test_accept(&tx).expect("a corrupted step is disprovable");
        let (txid, height) = rt.send_and_confirm(&tx).unwrap();
        println!("{}: disproved, {txid} confirmed at {height}: {} vB, leaf {} B", leaf.name, tx.vsize(), leaf.script.len() + 35);
    }
}
