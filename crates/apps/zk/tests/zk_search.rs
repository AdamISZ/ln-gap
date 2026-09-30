//! Z2 (DEMOS_PLAN.md section 3, D59): disputes over BitVMX's hello-world
//! (returns 0 iff its input is 0x11111111), searched to one step by
//! BitVMX's n-ary search between two in-process parties, then resolved on
//! regtest through the final step's output: the prover's `zk_prove_<class>`
//! after delta, the claimant's timeout after delta + delta'.
//!
//! - A: an honest prover with the valid input, and a verifier that
//!   challenges anyway: the search ends at a correct step, and the prover
//!   proves it;
//! - B: the valid input, but the prover reports a fake write at one step
//!   (so its claimed last hash is wrong; the verifier challenges a wrong
//!   hash even on a valid input): the search finds that step, the prover
//!   cannot prove it, and the claimant takes the output by timeout;
//! - C: an invalid input, the prover claiming success anyway: the search
//!   ends at the halt, which does not return 0; no proof, timeout.

use std::path::PathBuf;
use std::sync::Arc;

use bitcoin::key::Keypair;
use bitcoin::Amount;
use bitvmx_cpu_definitions::trace::{TraceStep, TraceWrite};
use emulator::decision::challenge::{prover_execute, ForceCondition};
use emulator::executor::utils::{FailConfiguration, FailExecute};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{disprove_witness, pair_key};
use lngap_pos::ttt::{Layout, PosLeaf};
use lngap_zk::chain::FinalOutput;
use lngap_zk::dispute::{search, Behaviour, Searched};
use lngap_zk::*;

const GAME: u16 = 1;
const D: u32 = 2;
const DELTA: u16 = 2;
const DELTA_PRIME: u16 = 3;
const VALID: [u8; 4] = [0x11; 4];
const INVALID: [u8; 4] = [0x11, 0x11, 0x11, 0x00];
/// The step whose write the cheating prover fakes (scenario B).
const FAKE_STEP: u64 = 40;

fn pdf() -> String {
    format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("lngap-zk-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn run(name: &str, input: &[u8], prover: Behaviour, force: ForceCondition) -> Searched {
    let dir = scratch(name);
    let s = search(&pdf(), input, &dir, &prover, &Behaviour::default(), force).unwrap().expect("the verifier challenges");
    let _ = std::fs::remove_dir_all(&dir);
    println!(
        "{name}: prover claims {:?}; {} rounds; disputed step {} ({}); prev {}, claimed {}",
        s.claim.0,
        s.rounds.len(),
        s.step,
        riscv_decode::decode(s.final_step.read.opcode).map(|i| format!("{i:?}")).unwrap_or_else(|_| "?".into()),
        hex::encode(s.final_step.prev_hash),
        hex::encode(s.final_step.hash)
    );
    s
}

/// The honest record of `step`, with its write value altered.
fn fake_trace(step: u64) -> bitvmx_cpu_definitions::trace::TraceRWStep {
    let dir = scratch("honest-trace");
    let d = format!("{}/", dir.display());
    prover_execute(&pdf(), VALID.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(&pdf()).unwrap();
    let mut t = pd.get_trace_step(&d, &d, VALID.to_vec(), step, None).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let w = t.trace_step.get_write();
    t.trace_step = TraceStep::new(TraceWrite::new(w.address, w.value ^ 0x100), t.trace_step.get_pc().clone());
    t
}

fn heads(s: &FinalStep) -> ([u8; 48], [u8; 48]) {
    (s.prior_head(GAME, D - 1, mover_at(D - 1)), s.new_head(GAME, D, mover_at(D)))
}

fn prove_leaf_for(sk: &WotsSecret, s: &FinalStep) -> Option<PosLeaf> {
    let ins = riscv_decode::decode(s.read.opcode).ok()?;
    Some(prove_leaf(&Layout::at(D, GAME, mover_at(D)), &sk.public(), &ins, s.read.micro, Arc::new(|_, _| true)))
}

/// Does the step prove, in the Script simulator?
fn proves(sk: &WotsSecret, s: &FinalStep) -> bool {
    let Some(leaf) = prove_leaf_for(sk, s) else { return false };
    let (p, n) = heads(s);
    let w = disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap());
    matches!(lngap_script32::sim::run(leaf.script.as_script(), w), Ok(st) if st.len() == 1 && st[0] == [1])
}

#[test]
fn searches() {
    let sk = pair_key([3; 32]);

    let a = run("A", &VALID, Behaviour::default(), ForceCondition::ValidInputStepAndHash);
    assert!(proves(&sk, &a.final_step), "A: an honest step must prove");
    assert_eq!(step_hash(&a.final_step.prev_hash, &a.final_step.write), a.final_step.hash);

    let fake = fake_trace(FAKE_STEP);
    let b_fail = FailConfiguration { fail_execute: Some(FailExecute { step: FAKE_STEP, fake_trace: fake.clone() }), ..Default::default() };
    let b = run("B", &VALID, Behaviour { fail: Some(b_fail) }, ForceCondition::ValidInputWrongStepOrHash);
    assert_eq!(b.trace.trace_step.get_write().value, fake.trace_step.get_write().value, "B: the search finds the faked step");
    assert!(!proves(&sk, &b.final_step), "B: a faked step must not prove");

    let c = run("C", &INVALID, Behaviour::default(), ForceCondition::No);
    assert!(!proves(&sk, &c.final_step), "C: the failing halt must not prove");
}

#[test]
fn resolved_on_regtest() {
    let rt = Regtest::start().unwrap();
    let sk = pair_key([4; 32]);
    let prover: Keypair = Seed::from_label("zk prover").keypair("pay");
    let claimant: Keypair = Seed::from_label("zk claimant").keypair("pay");

    let fake = fake_trace(FAKE_STEP);
    let cases = [
        ("A", run("rA", &VALID, Behaviour::default(), ForceCondition::ValidInputStepAndHash), true),
        ("B", run("rB", &VALID, Behaviour { fail: Some(FailConfiguration { fail_execute: Some(FailExecute { step: FAKE_STEP, fake_trace: fake }), ..Default::default() }) }, ForceCondition::ValidInputWrongStepOrHash), false),
        ("C", run("rC", &INVALID, Behaviour::default(), ForceCondition::No), false),
    ];
    for (name, s, honest) in cases {
        // the final step's output: the proof of this step's class, the timeout
        let pl = prove_leaf_for(&sk, &s.final_step).expect("a decodable opcode");
        let out = FinalOutput::new(&pl, &prover, &claimant, DELTA, DELTA_PRIME).unwrap();
        let (op, prev) = rt.fund(&out.tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
        rt.mine(u64::from(DELTA)).unwrap();
        let (p, n) = heads(&s.final_step);
        let proof = out.prove_tx(op, &prev, out.pay_back(Amount::from_sat(900_000)), &prover, &sk, &p, &n).unwrap();
        if honest {
            let (txid, h) = rt.send_and_confirm(&proof).unwrap();
            println!("{name}: the prover proves step {} ({}): {txid} at {h}, {} vB", s.step, pl.name, proof.vsize());
        } else {
            let err = rt.test_accept(&proof).expect_err("no proof of a wrong step");
            println!("{name}: no proof of step {} ({}): {err}", s.step, pl.name);
            let to = out.timeout_tx(op, &prev, out.pay_back(Amount::from_sat(900_000)), &claimant).unwrap();
            rt.test_accept(&to).expect_err("the timeout waits for delta + delta'");
            rt.mine(u64::from(DELTA_PRIME)).unwrap();
            let (txid, h) = rt.send_and_confirm(&to).unwrap();
            println!("{name}: the claimant's timeout: {txid} at {h}");
        }
    }
}

/// The Groth16 verifier (BitVMX's ELF, its public inputs set to the RISC0
/// parameters of the proof: DEMOS_PLAN.md, 2026-09-30), on a genuine proof.
/// Opt-in: set ZK_GROTH16_DIR to a directory holding `groth16.yaml`, the
/// ELF it names, and `input.hex`; about 479M steps per execution, about
/// 5.5 minutes per dispute in release on an M-series Mac.
#[test]
#[ignore]
fn groth16() {
    let Ok(dir) = std::env::var("ZK_GROTH16_DIR") else { panic!("set ZK_GROTH16_DIR") };
    let pdf = format!("{dir}/groth16.yaml");
    let input = hex::decode(std::fs::read_to_string(format!("{dir}/input.hex")).unwrap().trim()).unwrap();
    let sk = pair_key([5; 32]);
    let t0 = std::time::Instant::now();
    let go = |name: &str, input: &[u8], prover: Behaviour, force: ForceCondition| -> Searched {
        // the checkpoints: about 930 MB per dispute, removed after it
        let dir = scratch(name);
        let s = search(&pdf, input, &dir, &prover, &Behaviour::default(), force).unwrap().expect("the verifier challenges");
        let _ = std::fs::remove_dir_all(&dir);
        let ins = riscv_decode::decode(s.final_step.read.opcode).map(|i| format!("{i:?}")).unwrap_or_else(|_| "?".into());
        println!("{name}: prover claims {:?}; {} rounds; disputed step {} ({ins}); {:.0?} so far", s.claim.0, s.rounds.len(), s.step, t0.elapsed());
        s
    };
    // an honest prover of a valid proof, challenged anyway: it proves
    let a = go("g16-A", &input, Behaviour::default(), ForceCondition::ValidInputStepAndHash);
    assert!(proves(&sk, &a.final_step), "an honest step must prove");
    // a tampered proof, the prover claiming acceptance: the halt fails
    let mut bad = input.clone();
    bad[4 + 32 + 5] ^= 1;
    let c = go("g16-C", &bad, Behaviour::default(), ForceCondition::No);
    assert!(!proves(&sk, &c.final_step), "the rejecting halt must not prove");
}
