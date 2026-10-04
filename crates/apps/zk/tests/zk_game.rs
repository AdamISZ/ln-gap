//! D60's final move: the prove leaf over the state and the record (two
//! digest checks, then BitVMX's verification script and the step hash),
//! on every step of hello-world. An honest step proves with its class's
//! leaf; corruptions don't; the peak stack stays under 1,000.

use std::collections::BTreeMap;

use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::instruction_mapping::{generate_verification_script, get_key_from_instruction_and_micro, requires_witness};
use emulator::decision::challenge::prover_execute;
use emulator::loader::program_definition::ProgramDefinition;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::rebut::{disprove_witness, pair_key};
use lngap_pos::ttt::Layout;
use lngap_zk::dispute::final_step;
use lngap_zk::game::*;
use lngap_zk::{FinalStep, BASE_REGISTER_ADDRESS};

const GAME: u16 = 1;
/// The final depth (any depth >= 2 has the same layout).
const D: u32 = 7;
const INPUT: [u8; 4] = [0x11; 4];

fn pdf() -> String {
    format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR"))
}

/// Every step of hello-world as a final step.
fn all_steps() -> Vec<FinalStep> {
    let dir = std::env::temp_dir().join(format!("lngap-zk-game-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let d = format!("{}/", dir.display());
    let (_, last, hash) = prover_execute(&pdf(), INPUT.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(&pdf()).unwrap();
    let (_, trace) = pd.execute_helper(&d, &d, INPUT.to_vec(), Some((0..=last).collect()), None, false).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    trace.windows(2).map(|w| final_step(&w[1].0, &w[0].1, &w[1].1, last, &hash).unwrap()).collect()
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

fn run(script: &ScriptBuf, sk: &WotsSecret, state: &State, record: &Record) -> (bool, usize) {
    let (p, n) = final_heads(GAME, D, state, record);
    let mut w = final_witness(state, record);
    w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
    match lngap_script32::sim::run_peak(script.as_script(), w) {
        Ok((st, peak)) => (st.len() == 1 && truthy(&st[0]), peak),
        Err(_) => (false, 0),
    }
}

#[test]
fn prove_leaf_d60_on_hello_world() {
    let sk = pair_key([31; 32]);
    let l = Layout::at(D, GAME, mover_at(D));
    let steps = all_steps();
    let mut leaves: BTreeMap<String, ScriptBuf> = BTreeMap::new();
    let mut peaks: BTreeMap<String, (usize, usize, usize)> = BTreeMap::new();
    for f in &steps {
        let ins = riscv_decode::decode(f.read.opcode).unwrap();
        let key = get_key_from_instruction_and_micro(&ins, f.read.micro);
        let script = leaves
            .entry(key.clone())
            .or_insert_with(|| {
                let exec = generate_verification_script(&ins, f.read.micro, BASE_REGISTER_ADDRESS, requires_witness(&ins));
                prove_script_d60(&l, &sk.public(), &key, &ScriptBuf::from_bytes(exec.into_bytes()), requires_witness(&ins))
            })
            .clone();
        let (state, _claim, record) = blocks(f);
        let (ok, peak) = run(&script, &sk, &state, &record);
        assert!(ok, "step {} ({key}) must prove", f.agreed_step + 1);
        let e = peaks.entry(key.clone()).or_insert((0, 0, script.len()));
        e.0 += 1;
        e.1 = e.1.max(peak);
        // corruptions: none proves. The opcode: its rd bit, or for stores
        // and branches (no rd; bit 7 is the immediate, which only S1's
        // opcode check sees) its rs1 bit; at micro-step 0 only (later
        // micro-steps work from the intermediate registers the earlier
        // ones wrote, and BitVMX's script doesn't read the fields again)
        // and not for ecall, which has no register fields
        let op_bit = if matches!(record.read.opcode & 0x7f, 0x23 | 0x63) { 1 << 15 } else { 1 << 7 };
        let bad = [
            ("hi", State { hi: [0x5a; 20], ..state }, record),
            ("lo", State { lo: [0xa5; 20], ..state }, record),
            ("write value", state, Record { write: lngap_zk::Step { write_value: record.write.write_value ^ 0x100, ..record.write }, ..record }),
            ("next pc", state, Record { write: lngap_zk::Step { pc: record.write.pc ^ 8, ..record.write }, ..record }),
            ("opcode", state, Record { read: lngap_zk::Read { opcode: record.read.opcode ^ op_bit, ..record.read }, ..record }),
        ];
        for (what, s2, r2) in bad {
            if what == "opcode" && (f.read.micro != 0 || f.read.opcode & 0x7f == 0x73) {
                continue;
            }
            assert!(!run(&script, &sk, &s2, &r2).0, "step {} ({key}): a corrupted {what} must not prove", f.agreed_step + 1);
        }
    }
    let max = peaks.values().map(|v| v.1).max().unwrap();
    println!("{} steps, {} classes; peak max {max}", steps.len(), peaks.len());
    for (k, (count, peak, size)) in &peaks {
        println!("  {k:<28} {count:>5} steps  peak {peak:>4}  leaf {:>4} KB", size / 1000);
    }
    assert!(max <= 1000, "over the stack limit");
}

/// Probe: can a prover "prove" a real instruction's step with the nop
/// class's leaf, claiming the step wrote nothing? (BitVMX's op_nop drops
/// the opcode without checking it.)
#[test]
fn probe_nop_leaf_on_real_steps() {
    let sk = pair_key([33; 32]);
    let l = Layout::at(D, GAME, mover_at(D));
    let nop = riscv_decode::decode(0x00000013).unwrap(); // addi x0, x0, 0
    let exec = generate_verification_script(&nop, 0, BASE_REGISTER_ADDRESS, false);
    let script = prove_script_d60(&l, &sk.public(), "nop", &ScriptBuf::from_bytes(exec.into_bytes()), false);
    let steps = all_steps();
    let nop_mw =
        steps.iter().find(|f| get_key_from_instruction_and_micro(&riscv_decode::decode(f.read.opcode).unwrap(), f.read.micro) == "nop").map(|f| f.read.mem_witness).unwrap();
    let mut proved = BTreeMap::<String, usize>::new();
    let mut tried = 0;
    for f in steps.iter().filter(|f| f.read.micro == 0) {
        let ins = riscv_decode::decode(f.read.opcode).unwrap();
        let key = get_key_from_instruction_and_micro(&ins, 0);
        if key == "nop" {
            continue;
        }
        tried += 1;
        let (state, _, record) = blocks(f);
        // the nop's write: nothing written, pc + 4, micro 0; the memory
        // witness nop expects (none)
        let w = lngap_zk::Step { write_addr: 0, write_value: 0, pc: f.read.pc.wrapping_add(4), micro: 0 };
        let r = Record { write: w, read: lngap_zk::Read { mem_witness: nop_mw, ..record.read }, ..record };
        let s = State { hi: lngap_zk::step_hash(&state.lo, &w), ..state };
        if run(&script, &sk, &s, &r).0 {
            *proved.entry(key).or_default() += 1;
        }
    }
    println!("nop leaf proved {} of {tried} real non-nop steps: {proved:?}", proved.values().sum::<usize>());
}

/// Probe: does each class's leaf bind the opcode's fixed fields (opcode
/// bits 0..7, funct3 12..15, funct7 25 and 30)? Flip each in an honest
/// step and run the step's own class leaf: if it still proves, the leaf
/// doesn't check that bit.
#[test]
fn probe_class_binding() {
    let sk = pair_key([35; 32]);
    let l = Layout::at(D, GAME, mover_at(D));
    let mut leaves: BTreeMap<String, ScriptBuf> = BTreeMap::new();
    let mut unbound: BTreeMap<String, std::collections::BTreeSet<u32>> = BTreeMap::new();
    let mut seen: std::collections::BTreeSet<(String, u32)> = Default::default();
    for f in all_steps() {
        let ins = riscv_decode::decode(f.read.opcode).unwrap();
        let key = get_key_from_instruction_and_micro(&ins, f.read.micro);
        let script = leaves
            .entry(key.clone())
            .or_insert_with(|| {
                let exec = generate_verification_script(&ins, f.read.micro, BASE_REGISTER_ADDRESS, requires_witness(&ins));
                prove_script_d60(&l, &sk.public(), &key, &ScriptBuf::from_bytes(exec.into_bytes()), requires_witness(&ins))
            })
            .clone();
        let (state, _, record) = blocks(&f);
        for bit in [0u32, 1, 2, 3, 4, 5, 6, 12, 13, 14, 25, 30] {
            if !seen.insert((key.clone(), bit)) {
                continue;
            }
            let r = Record { read: lngap_zk::Read { opcode: record.read.opcode ^ (1 << bit), ..record.read }, ..record };
            if run(&script, &sk, &state, &r).0 {
                unbound.entry(key.clone()).or_default().insert(bit);
            }
        }
    }
    println!("classes: {}", leaves.len());
    for (k, bits) in &unbound {
        println!("  {k:<12} proves with opcode bit(s) flipped: {bits:?}");
    }
}

/// The D60 prove leaf on regtest, behind the prover's key: an honest step
/// of each of three classes is proved; a nop "proof" of a real step is
/// rejected (the guard).
#[test]
fn prove_leaf_d60_on_regtest() {
    use bitcoin::key::Keypair;
    use bitcoin::script::Builder;
    use bitcoin::{Amount, TxOut};
    use lngap_btc::keys::{xonly, Seed};
    use lngap_btc::regtest::Regtest;
    use lngap_btc::script::BuilderExt;
    use lngap_btc::sighash::sign_tapscript;
    use lngap_btc::taptree::{Leaf, TapTree};
    use lngap_btc::tx::{build_spend, Timelock};
    use lngap_btc::witness::tapscript_witness;

    let rt = Regtest::start().unwrap();
    let sk = pair_key([37; 32]);
    let prover: Keypair = Seed::from_label("d60 prover").keypair("pay");
    let l = Layout::at(D, GAME, mover_at(D));
    let steps = all_steps();
    let spend = |key: &str, ins: &riscv_decode::Instruction, micro: u8, state: &State, record: &Record| {
        let exec = generate_verification_script(ins, micro, BASE_REGISTER_ADDRESS, requires_witness(ins));
        let mut b = Builder::new().checksigverify(&xonly(&prover)).into_script().into_bytes();
        b.extend_from_slice(prove_script_d60(&l, &sk.public(), key, &ScriptBuf::from_bytes(exec.into_bytes()), requires_witness(ins)).as_bytes());
        let script = ScriptBuf::from_bytes(b);
        let tree = TapTree::new(vec![Leaf::new("prove", script.clone(), Timelock::NONE)]).unwrap();
        let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
        let sig = sign_tapscript(&prover, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
        let (p, n) = final_heads(GAME, D, state, record);
        let mut w = final_witness(state, record);
        w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &script, &tree.control_block("prove").unwrap());
        tx
    };
    for want in ["lw_0", "sb_2", "ecall"] {
        let f = steps.iter().find(|f| get_key_from_instruction_and_micro(&riscv_decode::decode(f.read.opcode).unwrap(), f.read.micro) == want).unwrap();
        let ins = riscv_decode::decode(f.read.opcode).unwrap();
        let (state, _, record) = blocks(f);
        let tx = spend(want, &ins, f.read.micro, &state, &record);
        let (txid, h) = rt.send_and_confirm(&tx).unwrap();
        println!("{want}: step {} proved, {txid} at {h}: {} vB", f.agreed_step + 1, tx.vsize());
    }
    // a nop "proof" of a real addi step: no write, pc + 4
    let f = steps.iter().find(|f| get_key_from_instruction_and_micro(&riscv_decode::decode(f.read.opcode).unwrap(), f.read.micro) == "addi").unwrap();
    let nop_f = steps.iter().find(|f| get_key_from_instruction_and_micro(&riscv_decode::decode(f.read.opcode).unwrap(), f.read.micro) == "nop").unwrap();
    let (state, _, record) = blocks(f);
    let w = lngap_zk::Step { write_addr: 0, write_value: 0, pc: f.read.pc.wrapping_add(4), micro: 0 };
    let r = Record { write: w, read: lngap_zk::Read { mem_witness: nop_f.read.mem_witness, ..record.read }, ..record };
    let s = State { hi: lngap_zk::step_hash(&state.lo, &w), ..state };
    let nop = riscv_decode::decode(0x00000013).unwrap();
    let err = rt.test_accept(&spend("nop", &nop, 0, &s, &r)).expect_err("the guard refuses");
    println!("nop proof of a real addi rejected ({err})");
}
