//! S1 (ZK_SOUNDNESS_PLAN.md): the claimant's disproves at the final step
//! that need only the parked pair and the program's constants, over
//! hello-world's real steps (the emulator's full trace records).
//!
//! - no S1 leaf fires on any honest step;
//! - each corruption fires its leaf, and script and mirror agree on every
//!   case: step 1's pc not the entry point (EntryPoint); a pc read that is
//!   not the previous step's written pc, with the claimant's witness of
//!   that step (ProgramCounter), and the same witness does not fire on the
//!   honest step, while a witness that does not hash to the agreed hash
//!   cannot fire at all; an opcode that is not the program's (Opcode, only
//!   the chunk covering the pc); a misaligned write or pc
//!   (AddressesSections);
//! - peak stack under 1,000 throughout.

use bitvmx_cpu_definitions::trace::TraceRWStep;
use emulator::decision::challenge::prover_execute;
use emulator::loader::program_definition::ProgramDefinition;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{disprove_witness, pair_key};
use lngap_pos::ttt::{Layout, PosLeaf};
use lngap_zk::challenges::*;
use lngap_zk::dispute::final_step;
use lngap_zk::*;

const GAME: u16 = 1;
const D: u32 = 2;
const INPUT: [u8; 4] = [0x11; 4];

fn pdf() -> String {
    format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR"))
}

/// The emulator's records and hashes for `steps` of hello-world on INPUT.
fn records(steps: Vec<u64>) -> Vec<(TraceRWStep, String)> {
    let dir = std::env::temp_dir().join(format!("lngap-zk-s1-{}-{}", std::process::id(), steps[0]));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let d = format!("{}/", dir.display());
    prover_execute(&pdf(), INPUT.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(&pdf()).unwrap();
    let (_, trace) = pd.execute_helper(&d, &d, INPUT.to_vec(), Some(steps), None, false).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    trace
}

/// Step `s` as a final step, with the ProgramCounter witness (the hash
/// after step s-2 and step s-1's write): s >= 3.
fn step(s: u64) -> (FinalStep, [u8; 20], Step) {
    let r = records(vec![s - 2, s - 1, s]);
    let h = |x: &str| -> [u8; 20] { hex::decode(x).unwrap().try_into().unwrap() };
    let f = final_step(&r[2].0, &r[1].1, &r[2].1).unwrap();
    let w = r[1].0.trace_step.get_write();
    let pc = r[1].0.trace_step.get_pc();
    let prev = Step { write_addr: w.address, write_value: w.value, pc: pc.get_address(), micro: pc.get_micro() };
    assert_eq!(f.agreed_step as u64, s - 1);
    (f, h(&r[0].1), prev)
}

fn heads(f: &FinalStep) -> ([u8; 48], [u8; 48]) {
    (f.prior_head(GAME, D - 1, mover_at(D - 1)), f.new_head(GAME, D, mover_at(D)))
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

/// Run a leaf: (fired, peak). `extra` goes below the pair reveal.
fn run(leaf: &PosLeaf, sk: &WotsSecret, f: &FinalStep, extra: Vec<Vec<u8>>) -> (bool, usize) {
    let (p, n) = heads(f);
    let mut w = extra;
    w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
    match lngap_script32::sim::run_peak(leaf.script.as_script(), w) {
        Ok((st, peak)) => {
            assert_eq!(st.len(), 1, "{}: cleanstack", leaf.name);
            (truthy(&st[0]), peak)
        }
        Err(_) => (false, 0),
    }
}

#[test]
fn s1_disproves() {
    let sk = pair_key([2; 32]);
    let info = ProgramInfo::load(&pdf()).unwrap();
    let l = Layout::at(D, GAME, mover_at(D));
    let entry = entry_point_leaf(&l, &sk.public(), &info);
    let pcl = program_counter_leaf(&l, &sk.public());
    let addr = addresses_leaf(&l, &sk.public(), &info);
    let ops = opcode_leaves(&l, &sk.public(), &info);
    println!("entry {} B, pc {} B, addresses {} B, opcode {} leaves (chunk 0: {} B); entry point {:#x}", entry.script.len(), pcl.script.len(), addr.script.len(), ops.len(), ops[0].script.len(), info.entry);
    let mut peak = 0;
    let mut check = |leaf: &PosLeaf, f: &FinalStep, extra: Vec<Vec<u8>>, mirror: bool, what: &str| {
        let (fired, pk) = run(leaf, &sk, f, extra);
        assert_eq!(fired, mirror, "{}: script {fired} vs mirror {mirror} ({what})", leaf.name);
        peak = peak.max(pk);
    };

    // step 1 against the entry point (its record from steps 0..=1)
    let r = records(vec![0, 1]);
    let f1 = final_step(&r[1].0, &r[0].1, &r[1].1).unwrap();
    assert_eq!(f1.agreed_step, 0);
    check(&entry, &f1, vec![], false, "honest step 1");
    let bad = FinalStep { read: Read { pc: f1.read.pc + 4, ..f1.read }, ..f1 };
    let (p, n) = heads(&bad);
    assert!((entry.fires)(&p, &n));
    check(&entry, &bad, vec![], true, "step 1 at the wrong pc");

    for s in [3u64, 10, 40, 200, 700, 1499] {
        let (f, pp, prev) = step(s);
        let (p, n) = heads(&f);
        // honest: nothing fires
        check(&entry, &f, vec![], false, "honest");
        check(&addr, &f, vec![], (addr.fires)(&p, &n), "honest");
        assert!(!(addr.fires)(&p, &n), "step {s}: addresses mirror on an honest step");
        check(&pcl, &f, program_counter_witness(&pp, &prev), false, "honest");
        let k = chunk_for(&info, f.read.pc).expect("the pc is in the code");
        check(&ops[k], &f, vec![], false, "honest");

        // a pc read that is not the previous step's written pc
        let bad = FinalStep { read: Read { pc: f.read.pc ^ 8, ..f.read }, ..f };
        assert!(program_counter_fires(&bad, &pp, &prev));
        check(&pcl, &bad, program_counter_witness(&pp, &prev), true, "pc not the previous write");
        // a witness that does not hash to the agreed hash cannot fire
        let mut wrong = pp;
        wrong[0] ^= 1;
        check(&pcl, &bad, program_counter_witness(&wrong, &prev), false, "a forged witness");

        // an opcode that is not the program's: only the covering chunk fires
        let bad = FinalStep { read: Read { opcode: f.read.opcode ^ (1 << 20), ..f.read }, ..f };
        for (j, op) in ops.iter().enumerate().filter(|(j, _)| *j == k || *j + 1 == k || *j == k + 1) {
            let (p, n) = heads(&bad);
            check(op, &bad, vec![], (op.fires)(&p, &n), "wrong opcode");
            assert_eq!((op.fires)(&p, &n), j == k);
        }

        // a misaligned write, a misaligned pc
        for (what, bad) in [
            ("misaligned write", FinalStep { write: Step { write_addr: f.write.write_addr + 1, ..f.write }, ..f }),
            ("misaligned pc", FinalStep { read: Read { pc: f.read.pc + 2, ..f.read }, ..f }),
        ] {
            let (p, n) = heads(&bad);
            assert!((addr.fires)(&p, &n), "{what}");
            check(&addr, &bad, vec![], true, what);
        }
    }
    println!("peak stack: {peak}");
    assert!(peak <= 1000);
}

/// The Groth16 verifier's constants: its entry point and code chunks, on
/// its first steps (records from the emulator's trace, as in zk_leaves.rs).
/// Opt-in: ZK_GROTH16_DIR as for zk_search's groth16 test.
#[test]
#[ignore]
fn s1_groth16_constants() {
    let Ok(dir) = std::env::var("ZK_GROTH16_DIR") else { panic!("set ZK_GROTH16_DIR") };
    let sk = pair_key([3; 32]);
    let info = ProgramInfo::load(&format!("{dir}/groth16.yaml")).unwrap();
    let l = Layout::at(D, GAME, mover_at(D));
    let ops = opcode_leaves(&l, &sk.public(), &info);
    println!("Groth16 verifier: entry {:#x}, {} code chunks", info.entry, ops.len());
    // (pc, opcode) of the ELF's steps 1..=5
    let steps = [(0x8005d260u32, 0x00000513u32), (0x8005d264, 0xbe8a30ef), (0x8000064c, 0x81010113), (0x80000650, 0x7e112623), (0x80000654, 0x7e812423)];
    assert_eq!(info.entry, steps[0].0, "step 1 is at the entry point");
    for (i, &(pc, opcode)) in steps.iter().enumerate() {
        let f = FinalStep { read: Read { pc, opcode, ..Default::default() }, agreed_step: i as u32, ..Default::default() };
        let k = chunk_for(&info, pc).unwrap();
        let (fired, _) = run(&ops[k], &sk, &f, vec![]);
        assert!(!fired, "step {}: the program's own opcode fires chunk {k}", i + 1);
        let bad = FinalStep { read: Read { opcode: opcode ^ 0x80, ..f.read }, ..f };
        assert!(run(&ops[k], &sk, &bad, vec![]).0, "step {}: a wrong opcode must fire chunk {k}", i + 1);
        let other = if k == 0 { 1 } else { k - 1 };
        assert!(!run(&ops[other], &sk, &bad, vec![]).0, "step {}: chunk {other} must not fire", i + 1);
    }
}

/// The largest S1 leaf, ProgramCounter, on regtest behind the challenger's
/// key: the node accepts the disprove of a wrong pc with the claimant's
/// witness, and rejects it on the honest step.
#[test]
fn s1_program_counter_on_regtest() {
    use bitcoin::key::Keypair;
    use bitcoin::script::Builder;
    use bitcoin::{Amount, ScriptBuf, TxOut};
    use lngap_btc::keys::{xonly, Seed};
    use lngap_btc::regtest::Regtest;
    use lngap_btc::script::BuilderExt;
    use lngap_btc::sighash::sign_tapscript;
    use lngap_btc::taptree::{Leaf, TapTree};
    use lngap_btc::tx::{build_spend, Timelock};
    use lngap_btc::witness::tapscript_witness;

    let rt = Regtest::start().unwrap();
    let sk = pair_key([4; 32]);
    let challenger: Keypair = Seed::from_label("s1 challenger").keypair("pay");
    let l = Layout::at(D, GAME, mover_at(D));
    let pl = program_counter_leaf(&l, &sk.public());
    let mut b = Builder::new().checksigverify(&xonly(&challenger)).into_script().into_bytes();
    b.extend_from_slice(pl.script.as_bytes());
    let script = ScriptBuf::from_bytes(b);
    let tree = TapTree::new(vec![Leaf::new(pl.name.clone(), script.clone(), Timelock::NONE)]).unwrap();
    let (f, pp, prev) = step(40);
    let spend = |f: &FinalStep| {
        let (op, prevout) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
        let sig = sign_tapscript(&challenger, &tx, 0, std::slice::from_ref(&prevout), &script).unwrap();
        let (p, n) = heads(f);
        let mut w = program_counter_witness(&pp, &prev);
        w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &script, &tree.control_block(&pl.name).unwrap());
        tx
    };
    let err = rt.test_accept(&spend(&f)).expect_err("the honest step is not disprovable");
    let bad = FinalStep { read: Read { pc: f.read.pc ^ 8, ..f.read }, ..f };
    let tx = spend(&bad);
    let (txid, h) = rt.send_and_confirm(&tx).unwrap();
    println!("zk_program_counter: honest rejected ({err}); wrong pc disproved: {txid} at {h}, {} vB", tx.vsize());
}

/// BitVMX's own chunking (Program::get_code_chunks, rev 299009c6) places
/// chunk i at start + i * CHUNK_SIZE bytes although it holds CHUNK_SIZE
/// words: on the Groth16 verifier, the chunk it assigns to the pc of step
/// 3 (addi at 0x8000064c) holds a different word there, so BitVMX's Opcode
/// challenge would fire on an honest step. Ours holds the opcode. Opt-in:
/// ZK_GROTH16_DIR.
#[test]
#[ignore]
fn bitvmx_chunk_addressing_bug() {
    use bitvmx_cpu_definitions::constants::CHUNK_SIZE;
    use emulator::loader::program_definition::ProgramDefinition;
    let Ok(dir) = std::env::var("ZK_GROTH16_DIR") else { panic!("set ZK_GROTH16_DIR") };
    let pdf = format!("{dir}/groth16.yaml");
    let p = ProgramDefinition::from_config(&pdf).unwrap().load_program().unwrap();
    let (pc, opcode) = (0x8000064cu32, 0x81010113u32);
    let word_at = |cs: &[bitvmx_cpu_definitions::memory::Chunk]| {
        let c = cs.iter().find(|c| c.base_addr <= pc && pc <= c.base_addr + c.data.len() as u32 * 4 - 1).unwrap();
        c.data[((pc - c.base_addr) / 4) as usize]
    };
    let theirs = word_at(&p.get_code_chunks(CHUNK_SIZE));
    let ours = word_at(&ProgramInfo::load(&pdf).unwrap().code_chunks);
    println!("word at {pc:#x}: BitVMX's chunks {theirs:#010x}, ours {ours:#010x}, the executed opcode {opcode:#010x}");
    assert_eq!(ours, opcode);
    assert_ne!(theirs, opcode);
}
