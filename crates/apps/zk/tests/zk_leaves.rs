//! Z1 (DEMOS_PLAN.md section 3, D59): the last step of a disputed BitVMX
//! execution is proved by the prover, over the first steps of the Groth16
//! verifier ELF (`zkverifier-new-mul.elf` on the repo's sample input, from
//! `emulator execute --trace --debug`: addi, jal, addi, sw, sw).
//!
//! - the native step hash reproduces the emulator's;
//! - the proof leaves (addi, jal, sw): an honest step proves; no
//!   corruption does, whether of the write (address, value, pc, micro),
//!   the claimed hash, the prior hash, a read the instruction uses (its
//!   register address or its value: the read record inconsistent with the
//!   opcode that the disprove orientation could not catch), or the
//!   opcode; and no class's leaf proves another class's step;
//! - peak stack under 1,000;
//! - on regtest, the final step's output as D59 (amended) shapes it (the
//!   claimant's disproves after delta, the prover's proof after delta +
//!   delta', the claimant's timeout after delta + 2 delta'): an honest step
//!   is proved, not in the claimant's window; a cheated one cannot be, and
//!   the claimant takes it by timeout, not before delta + 2 delta'.

use std::sync::Arc;

use bitcoin::key::Keypair;
use bitcoin::script::Builder;
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::{xonly, Seed};
use lngap_btc::regtest::Regtest;
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::rebut::{disprove_witness, pair_key};
use lngap_pos::ttt::{Layout, PosLeaf};
use lngap_zk::*;

const GAME: u16 = 1;
/// The depth of the parked pair (the proof reads a prior head).
const D: u32 = 2;
const DELTA: u16 = 2;
const DELTA_PRIME: u16 = 3;
/// D59 amended: the proof after the claimant's disprove window, the
/// timeout after the prover's.
const PROVE: u16 = DELTA + DELTA_PRIME;
const TIMEOUT: u16 = DELTA + 2 * DELTA_PRIME;

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
                agreed_step: 0,
                ..Default::default()
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

/// Run a leaf in the simulator: (spendable, peak stack).
fn run(leaf: &PosLeaf, sk: &WotsSecret, s: &FinalStep) -> (bool, usize) {
    let (p, n) = heads(s);
    let mut w = s.extra_witness();
    w.extend(reveal(sk, &p, &n));
    match lngap_script32::sim::run_peak(leaf.script.as_script(), w) {
        Ok((st, peak)) => {
            assert_eq!(st.len(), 1, "{}: cleanstack", leaf.name);
            (truthy(&st[0]), peak)
        }
        Err(_) => (false, 0),
    }
}

/// Every corruption of step `s` that makes it wrong. The reads are
/// corrupted only when the instruction uses them (jal reads nothing).
fn corruptions(s: &FinalStep) -> Vec<(&'static str, FinalStep)> {
    let (w, r) = (s.write, s.read);
    let mut v = vec![
        ("write address", FinalStep { write: Step { write_addr: w.write_addr ^ 4, ..w }, ..*s }),
        ("write value", FinalStep { write: Step { write_value: w.write_value ^ 0x100, ..w }, ..*s }),
        ("next pc", FinalStep { write: Step { pc: w.pc ^ 8, ..w }, ..*s }),
        ("micro", FinalStep { write: Step { micro: w.micro ^ 1, ..w }, ..*s }),
        ("claimed hash", FinalStep { hash: [0x5a; 20], ..*s }),
        ("prior hash", FinalStep { prev_hash: [0xa5; 20], ..*s }),
        ("opcode's rd", FinalStep { read: Read { opcode: r.opcode ^ (1 << 7), ..r }, ..*s }),
    ];
    if r.read_1_addr != 0 {
        v.push(("read 1 register", FinalStep { read: Read { read_1_addr: r.read_1_addr ^ 4, ..r }, ..*s }));
        v.push(("read 1 value", FinalStep { read: Read { read_1_value: r.read_1_value ^ 0x10, ..r }, ..*s }));
    }
    v
}

#[test]
fn step_hash_reproduces_the_emulator() {
    for (i, s) in trace().iter().enumerate() {
        assert_eq!(step_hash(&s.prev_hash, &s.write), s.hash, "step {}", i + 1);
    }
}

/// The proof leaf for step `i`'s instruction class. Its mirror, for these
/// cases: the pair is exactly the emulator's step `i`.
fn prove_leaf_for(sk: &WotsSecret, i: usize) -> PosLeaf {
    let s = trace()[i];
    let ins = riscv_decode::decode(s.read.opcode).unwrap();
    let sh = heads(&s);
    let holds = Arc::new(move |p: &[u8; 48], n: &[u8; 48]| (*p, *n) == sh);
    prove_leaf(&Layout::at(D, GAME, mover_at(D)), &sk.public(), &ins, s.read.micro, holds)
}

#[test]
fn proofs() {
    let sk = pair_key([8; 32]);
    let steps = trace();
    // steps 1 (addi), 2 (jal), 4 (sw)
    let leaves: Vec<(usize, PosLeaf)> = [0, 1, 3].iter().map(|&i| (i, prove_leaf_for(&sk, i))).collect();
    let mut peak = 0;
    for (i, leaf) in &leaves {
        let s = steps[*i];
        let (ok, pk) = run(leaf, &sk, &s);
        println!("{}: {} B of script, peak stack {pk}", leaf.name, leaf.script.len());
        assert!(ok, "{}: the honest step {} does not prove", leaf.name, i + 1);
        peak = peak.max(pk);
        for (what, c) in corruptions(&s) {
            let (p, n) = heads(&c);
            assert!(!(leaf.fires)(&p, &n));
            assert!(!run(leaf, &sk, &c).0, "{}: proved step {} with a corrupted {what}", leaf.name, i + 1);
        }
        for (j, other) in &leaves {
            if j != i {
                assert!(!run(other, &sk, &s).0, "{} proved step {} ({})", other.name, i + 1, leaf.name);
            }
        }
    }
    assert!(peak <= 1000, "peak stack {peak}");
}

#[test]
fn final_step_on_regtest() {
    let rt = Regtest::start().unwrap();
    let sk = pair_key([9; 32]);
    let prover: Keypair = Seed::from_label("zk prover").keypair("pay");
    let claimant: Keypair = Seed::from_label("zk claimant").keypair("pay");
    let step = trace()[0];
    let pl = prove_leaf_for(&sk, 0);

    // the final step's rebuttal output, as D59 shapes it
    let prove = {
        let mut b = Builder::new().csv(PROVE).checksigverify(&xonly(&prover)).into_script().into_bytes();
        b.extend_from_slice(pl.script.as_bytes());
        ScriptBuf::from_bytes(b)
    };
    let timeout = Builder::new().csv(TIMEOUT).checksig(&xonly(&claimant)).into_script();
    let pname = pl.name.clone();
    let tree = TapTree::new(vec![Leaf::new(pname.clone(), prove.clone(), Timelock::csv(PROVE)), Leaf::new("timeout", timeout.clone(), Timelock::csv(TIMEOUT))]).unwrap();

    let spend = |op: OutPoint, prev: &TxOut, name: &str, script: &ScriptBuf, lock: Timelock, key: &Keypair, parked: Option<&FinalStep>| -> Transaction {
        let mut tx = build_spend(op, &lock, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
        let sig = sign_tapscript(key, &tx, 0, std::slice::from_ref(prev), script).unwrap();
        let mut w = match parked {
            Some(s) => {
                let (p, n) = heads(s);
                let mut w = s.extra_witness();
                w.extend(reveal(&sk, &p, &n));
                w
            }
            None => vec![],
        };
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, script, &tree.control_block(name).unwrap());
        tx
    };

    // an honest step: proved after delta + delta' (the claimant's disprove
    // window first), not before
    let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
    let tx = spend(op, &prev, &pname, &prove, Timelock::csv(PROVE), &prover, Some(&step));
    rt.mine(u64::from(DELTA)).unwrap();
    println!("honest proof in the claimant's window (after delta): {}", rt.test_accept(&tx).expect_err("CSV"));
    rt.mine(u64::from(DELTA_PRIME)).unwrap();
    rt.test_accept(&tx).expect("an honest step proves");
    let (txid, h) = rt.send_and_confirm(&tx).unwrap();
    println!("{}: proved, {txid} confirmed at {h}: {} vB, leaf {} B", pl.name, tx.vsize(), prove.len());

    // a cheated step (read 1's value inconsistent with the write): no
    // proof; the claimant's timeout after delta + 2 delta', not before
    let cheat = corruptions(&step).into_iter().find(|(w, _)| *w == "read 1 value").unwrap().1;
    let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
    rt.mine(u64::from(PROVE)).unwrap();
    let tx = spend(op, &prev, &pname, &prove, Timelock::csv(PROVE), &prover, Some(&cheat));
    println!("cheated proof: {}", rt.test_accept(&tx).expect_err("a cheated step must not prove"));
    let to = spend(op, &prev, "timeout", &timeout, Timelock::csv(TIMEOUT), &claimant, None);
    println!("timeout before delta + 2 delta': {}", rt.test_accept(&to).expect_err("CSV"));
    rt.mine(u64::from(DELTA_PRIME)).unwrap();
    let (txid, h) = rt.send_and_confirm(&to).unwrap();
    println!("timeout: the claimant takes it, {txid} confirmed at {h}: {} vB", to.vsize());
}
