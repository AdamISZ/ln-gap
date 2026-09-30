//! Z1 (DEMOS_PLAN.md section 3): BitVMX's trace-hash challenge as an
//! LN-GAP disprove leaf.
//!
//! - the native mirror reproduces the BitVMX emulator's step hashes, on
//!   the first five steps of the Groth16 verifier ELF (`zkverifier-new-
//!   mul.elf` on the repo's sample input, `emulator execute --trace
//!   --debug`);
//! - in the Script simulator the leaf agrees with the mirror on honest
//!   steps and on corrupted ones (a wrong claimed hash, a wrong step
//!   record, a wrong prior hash), and its peak stack is under 1,000;
//! - on regtest, with the challenger's key in front as in every disprove
//!   leaf: the node rejects a spend over an honest step and accepts, then
//!   confirms, one over a corrupted hash.

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
use lngap_pos::ttt::Layout;
use lngap_zk::*;

const GAME: u16 = 1;
/// The depth of the parked pair (the leaf needs a prior head).
const D: u32 = 2;

/// Step 0's hash, then (write address, write value, pc, micro, hash) for
/// steps 1..=5, from the emulator's trace.
const H0: &str = "99d44d377bc5936d8cb7f5df90713d84c7587739";
const STEPS: [(u32, u32, u32, u8, &str); 5] = [
    (0xf0000028, 0x00000000, 0x8005d264, 0, "09229b16d156a5a4eb05e8eea147fbcbe69be904"),
    (0xf0000004, 0x8005d268, 0x8000064c, 0, "6ecf50a650b21964959fb7f005abc2e920c1403f"),
    (0xf0000008, 0xe07ff810, 0x80000650, 0, "838e56fe3ff63566e703ec6ec789c62bb6cda9ef"),
    (0xe07ffffc, 0x8005d268, 0x80000654, 0, "265207ada14da925e9c2bf599ac63a2d9474f3f6"),
    (0xe07ffff8, 0x00000000, 0x80000658, 0, "4cc77b4f5483f36a05877df2798ec756ec296c18"),
];

fn h20(s: &str) -> [u8; 20] {
    hex::decode(s).unwrap().try_into().unwrap()
}

/// (prev hash, step, recorded hash) for each emulator step.
fn trace() -> Vec<([u8; 20], Step, [u8; 20])> {
    let mut prev = h20(H0);
    STEPS
        .iter()
        .map(|&(a, v, pc, m, h)| {
            let t = (prev, Step { write_addr: a, write_value: v, pc, micro: m }, h20(h));
            prev = t.2;
            t
        })
        .collect()
}

fn heads(prev: &[u8; 20], step: &Step, hash: &[u8; 20]) -> ([u8; 48], [u8; 48]) {
    (prior_head(GAME, D - 1, mover_at(D - 1), prev), step_head(GAME, D, mover_at(D), step, hash))
}

/// The pair reveal for (prior, new) under `sk`.
fn reveal(sk: &WotsSecret, p: &[u8; 48], n: &[u8; 48]) -> Vec<Vec<u8>> {
    disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap())
}

/// Honest steps, then three corruptions of each: the claimed hash, the
/// step record, the prior hash. (prior, new, should fire)
fn cases() -> Vec<([u8; 48], [u8; 48], bool)> {
    let mut v = vec![];
    for (prev, step, hash) in trace() {
        let (p, n) = heads(&prev, &step, &hash);
        v.push((p, n, false));
        let mut bad = hash;
        bad[19] ^= 1;
        let (p, n) = heads(&prev, &step, &bad);
        v.push((p, n, true));
        let (p, n) = heads(&prev, &Step { write_value: step.write_value ^ 0x100, ..step }, &hash);
        v.push((p, n, true));
        let mut bp = prev;
        bp[0] ^= 0x80;
        let (p, n) = heads(&bp, &step, &hash);
        v.push((p, n, true));
    }
    v
}

#[test]
fn mirror_reproduces_the_emulator() {
    for (i, (prev, step, hash)) in trace().into_iter().enumerate() {
        assert_eq!(step_hash(&prev, &step), hash, "step {}", i + 1);
    }
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

#[test]
fn leaf_agrees_with_the_mirror() {
    let sk = pair_key([7; 32]);
    let l = Layout::at(D, GAME, mover_at(D));
    let leaf = trace_hash_leaf(&l, &sk.public());
    println!("{}: {} B of script ({} B BitVMX's challenge)", leaf.name, leaf.script.len(), challenge_script().len());
    let mut peak = 0;
    for (p, n, fires) in cases() {
        assert_eq!((leaf.fires)(&p, &n), fires, "mirror");
        let ran = match lngap_script32::sim::run_peak(leaf.script.as_script(), reveal(&sk, &p, &n)) {
            Ok((st, pk)) => {
                peak = peak.max(pk);
                assert_eq!(st.len(), 1, "cleanstack");
                truthy(&st[0])
            }
            Err(e) => {
                assert!(!fires, "the leaf failed where it should fire: {e}");
                false
            }
        };
        assert_eq!(ran, fires, "script vs mirror");
    }
    println!("peak stack (main + alt) over all cases: {peak}");
    assert!(peak <= 1000, "peak stack {peak} exceeds consensus's 1,000");
}

#[test]
fn leaf_on_regtest() {
    let rt = Regtest::start().unwrap();
    let sk = pair_key([9; 32]);
    let l = Layout::at(D, GAME, mover_at(D));
    let pl = trace_hash_leaf(&l, &sk.public());
    // the challenger's key in front, as refuted_tree does for every leaf
    let challenger: Keypair = Seed::from_label("zk challenger").keypair("pay");
    let mut bytes = Builder::new().push_x_only_key(&xonly(&challenger)).push_opcode(OP_CHECKSIGVERIFY).into_script().into_bytes();
    bytes.extend_from_slice(pl.script.as_bytes());
    let script = ScriptBuf::from_bytes(bytes);
    let name = format!("disprove_{}", pl.name);
    let tree = TapTree::new(vec![Leaf::new(name.clone(), script.clone(), Timelock::NONE)]).unwrap();
    let control = tree.control_block(&name).unwrap();
    let pay_to = tree.script_pubkey();

    let spend = |p: &[u8; 48], n: &[u8; 48]| -> Transaction {
        let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: pay_to.clone() }]);
        let sig = sign_tapscript(&challenger, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
        let mut w = reveal(&sk, p, n);
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &script, &control);
        tx
    };

    let (prev, step, hash) = trace()[2];
    let (p, n) = heads(&prev, &step, &hash);
    let honest = spend(&p, &n);
    let err = rt.test_accept(&honest).expect_err("an honest step must not be disprovable");
    println!("honest step 3: rejected ({err})");

    let mut bad = hash;
    bad[0] ^= 0x10;
    let (p, n) = heads(&prev, &step, &bad);
    let cheat = spend(&p, &n);
    rt.test_accept(&cheat).expect("a corrupted hash is disprovable");
    let (txid, height) = rt.send_and_confirm(&cheat).unwrap();
    println!(
        "disprove over a corrupted step-3 hash: {txid} confirmed at {height}: {} vB, {} WU; leaf {} B, witness {} items",
        cheat.vsize(),
        cheat.weight().to_wu(),
        script.len(),
        cheat.input[0].witness.len()
    );
}
