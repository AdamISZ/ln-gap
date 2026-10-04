//! Z3 step 4: the claimant's final-depth disproves at D60's layout
//! (final_d60.rs). On hello-world: no leaf fires on honest steps; a
//! malformation aimed at each leaf fires it; Script == mirror for every
//! leaf on every case; peak under 1,000; a sample spends on regtest.

use emulator::decision::challenge::prover_execute;
use emulator::loader::program_definition::ProgramDefinition;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::rebut::{disprove_witness, pair_key};
use lngap_pos::ttt::Layout;
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::final_step;
use lngap_zk::final_d60::*;
use lngap_zk::game::*;
use lngap_zk::FinalStep;

const GAME: u16 = 1;
const D: u32 = 23;
const INPUT: [u8; 4] = [0x11; 4];

fn pdf() -> String {
    format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn all_steps() -> Vec<FinalStep> {
    let dir = std::env::temp_dir().join(format!("lngap-zk-final-{}", std::process::id()));
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

struct Case {
    what: String,
    state: State,
    record: Record,
    claim: Claim,
    wit: Vec<u8>,
}

fn run(leaf: &FinalLeaf, sk: &WotsSecret, c: &Case) -> (bool, usize) {
    let (p, n) = final_heads(GAME, D, &c.state, &c.record);
    let wit = if leaf.wit > 0 { c.wit.clone() } else { vec![] };
    let mut w = final_leaf_witness(&leaf.blocks, &c.state, &c.record, &c.claim, &wit);
    w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
    match lngap_script32::sim::run_peak(leaf.script.as_script(), w) {
        Ok((st, peak)) => (st.len() == 1 && truthy(&st[0]), peak),
        Err(_) => (false, 0),
    }
}

fn honest_case(steps: &[FinalStep], i: usize) -> Case {
    let (state, claim, record) = blocks(&steps[i]);
    // the program counter witness: the hash after step i-1 and step i's
    // write (steps[i] is step i + 1)
    let wit = if i >= 1 { program_counter_wit(&steps[i - 1].prev_hash, &steps[i - 1].write) } else { vec![0; 33] };
    Case { what: format!("step {} honest", i + 1), state, record, claim, wit }
}

/// The malformations: each aimed at one leaf.
fn malformed(steps: &[FinalStep], info: &ProgramInfo, i: usize) -> Vec<(String, Case)> {
    let h = honest_case(steps, i);
    let mut v = vec![];
    let mut push = |aim: &str, f: &dyn Fn(&mut Case)| {
        let mut c = Case { what: format!("step {}: {aim}", i + 1), state: h.state, record: h.record, claim: h.claim, wit: h.wit.clone() };
        f(&mut c);
        c.state.claim = c.claim.digest();
        v.push((aim.to_string(), c));
    };
    push("zk_record_step", &|c| c.record.step += 1);
    push("zk_opcode", &|c| c.record.read.opcode ^= 1 << 20);
    push("zk_addresses_sections", &|c| c.record.read.read_1_addr = c.record.read.read_1_addr.wrapping_add(2));
    push("zk_future_read_1", &|c| c.record.last_step_1 = u64::from(c.record.step) + 5);
    push("zk_halt_hash", &|c| {
        c.claim.last_step = u64::from(c.record.step) + 1;
        c.claim.last_hash = [0x77; 20];
    });
    // (at the real last step, an ecall exit with 0, that claim is honest)
    let exit = h.record.read.opcode == 0x73 && h.record.read.read_1_value == 93 && h.record.read.read_2_value == 0;
    if !exit {
        push("zk_halt_exit", &|c| c.claim.last_step = u64::from(c.record.step) + 1);
    }
    if i >= 1 {
        push("zk_program_counter", &|c| c.record.read.pc = c.record.read.pc.wrapping_add(4));
    }
    if i == 0 {
        push("zk_entry_point", &|c| c.record.read.pc = c.record.read.pc.wrapping_add(4));
    }
    // a never-written read in initialised data with the wrong value, and
    // one in uninitialised memory with a nonzero value
    let c0 = &info.data_chunks[0];
    let (a, val) = (c0.base_addr, c0.data[0]);
    push("zk_initialized", &move |c| {
        c.record.read.read_1_addr = a;
        c.record.read.read_1_value = val ^ 1;
        c.record.last_step_1 = NEVER_WRITTEN;
    });
    let ua = info.uninitialized.ranges[0].0;
    push("zk_uninitialized_1", &move |c| {
        c.record.read.read_1_addr = ua;
        c.record.read.read_1_value = 5;
        c.record.last_step_1 = NEVER_WRITTEN;
    });
    v
}

#[test]
fn final_leaves_match_mirrors() {
    let sk = pair_key([71; 32]);
    let info = ProgramInfo::load(&pdf()).unwrap();
    let l = Layout::at(D, GAME, mover_at(D));
    let leaves = final_leaves(&l, &sk.public(), &info);
    let steps = all_steps();
    let mut peak = 0;
    let (mut fired, mut held) = (0usize, 0usize);
    let sample: Vec<usize> = (0..steps.len()).step_by(37).chain([0, 1, 2, steps.len() - 1]).collect();
    for &i in &sample {
        let mut cases = vec![(String::new(), honest_case(&steps, i))];
        cases.extend(malformed(&steps, &info, i));
        for (aim, c) in &cases {
            for leaf in &leaves {
                let mirror = fires(&leaf.name, &info, &c.state, &c.record, &c.claim, &c.wit);
                let (f, pk) = run(leaf, &sk, c);
                assert_eq!(f, mirror, "{}: {} script vs mirror", c.what, leaf.name);
                peak = peak.max(pk);
                if f {
                    fired += 1
                } else {
                    held += 1
                }
                if aim.is_empty() {
                    // honest: only the halt leaves at the real last step may
                    // look at it, and they hold there too
                    assert!(!f, "{}: {} fired on an honest step", c.what, leaf.name);
                }
            }
            if !aim.is_empty() {
                assert!(leaves.iter().any(|lf| lf.name.starts_with(aim.as_str()) && run(lf, &sk, c).0), "{}: no {aim} leaf fired", c.what);
            }
        }
    }
    let sizes: Vec<String> =
        leaves.iter().filter(|l| !l.name.starts_with("zk_opcode_") && !l.name.starts_with("zk_initialized_")).map(|l| format!("{} {} KB", l.name, l.script.len() / 1000)).collect();
    println!("{} leaves; {} steps sampled; {fired} fired, {held} held; peak {peak}", leaves.len(), sample.len());
    println!("{}", sizes.join(", "));
    assert!(peak <= 1000, "over the stack limit");
}

/// Each leaf's peak, and the heaviest on regtest: an aimed malformation
/// disproved, the honest step not.
#[test]
fn final_leaves_peaks_and_regtest() {
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

    let sk = pair_key([73; 32]);
    let info = ProgramInfo::load(&pdf()).unwrap();
    let l = Layout::at(D, GAME, mover_at(D));
    let leaves = final_leaves(&l, &sk.public(), &info);
    let steps = all_steps();
    let i = 40;
    let mut cases: Vec<(String, Case)> = vec![(String::new(), honest_case(&steps, i))];
    cases.extend(malformed(&steps, &info, i));
    let mut peaks: std::collections::BTreeMap<String, usize> = Default::default();
    for (_, c) in &cases {
        for lf in &leaves {
            let key = if lf.name.starts_with("zk_opcode_") {
                "zk_opcode_*".to_string()
            } else if lf.name.starts_with("zk_initialized_") {
                "zk_initialized_*".to_string()
            } else {
                lf.name.clone()
            };
            let pk = run(lf, &sk, c).1;
            let e = peaks.entry(key).or_default();
            *e = (*e).max(pk);
        }
    }
    println!("peaks: {peaks:?}");

    let rt = Regtest::start().unwrap();
    let claimant: Keypair = Seed::from_label("final claimant").keypair("pay");
    for aim in ["zk_program_counter", "zk_halt_exit", "zk_record_step"] {
        let lf = leaves.iter().find(|x| x.name == aim).unwrap();
        let (_, bad) = cases.iter().find(|(a, _)| a == aim).unwrap();
        let (_, good) = &cases[0];
        let spend = |c: &Case| {
            let mut b = Builder::new().checksigverify(&xonly(&claimant)).into_script().into_bytes();
            b.extend_from_slice(lf.script.as_bytes());
            let script = ScriptBuf::from_bytes(b);
            let tree = TapTree::new(vec![Leaf::new("d", script.clone(), Timelock::NONE)]).unwrap();
            let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
            let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
            let sig = sign_tapscript(&claimant, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
            let (p, n) = final_heads(GAME, D, &c.state, &c.record);
            let wit = if lf.wit > 0 { c.wit.clone() } else { vec![] };
            let mut w = final_leaf_witness(&lf.blocks, &c.state, &c.record, &c.claim, &wit);
            w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
            w.push(sig.as_ref().to_vec());
            tx.input[0].witness = tapscript_witness(&w, &script, &tree.control_block("d").unwrap());
            tx
        };
        let err = rt.test_accept(&spend(good)).expect_err("the honest step holds");
        let tx = spend(bad);
        let (txid, h) = rt.send_and_confirm(&tx).unwrap();
        println!("{aim}: {txid} at {h}, {} vB; honest rejected ({err})", tx.vsize());
    }
}
