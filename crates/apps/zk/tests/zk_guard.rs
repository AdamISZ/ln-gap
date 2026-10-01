//! The class guard (guard.rs): Script == the native mirror over random and
//! targeted opcodes for every class; every instruction of the Groth16
//! verifier's code passes its own class's guard (opt-in, ZK_GROTH16_DIR).

use bitcoin_script_riscv::riscv::instruction_mapping::generate_sample_instructions;
use bitcoin_script_riscv::riscv::instruction_mapping::get_key_from_instruction_and_micro;
use lngap_zk::guard::*;
use rand::{Rng, SeedableRng};

fn nibbles(op: u32, micro: u8) -> Vec<Vec<u8>> {
    let mut v: Vec<u8> = (0..8).map(|i| ((op >> (28 - 4 * i)) & 15) as u8).collect();
    v.push(micro);
    v.into_iter().map(|x| if x == 0 { vec![] } else { vec![x] }).collect()
}

fn script_holds(s: &bitcoin::ScriptBuf, op: u32, micro: u8) -> bool {
    let mut script = s.clone();
    script.push_opcode(bitcoin::opcodes::all::OP_PUSHNUM_1);
    matches!(lngap_script32::sim::run_peak(script.as_script(), nibbles(op, micro)), Ok((st, _)) if st == vec![vec![1u8]])
}

#[test]
fn guard_script_matches_mirror() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(41);
    let mut keys: Vec<String> = generate_sample_instructions().iter().map(|(i, m)| get_key_from_instruction_and_micro(i, *m)).collect();
    keys.sort();
    keys.dedup();
    // hello-world's code words at every micro-step
    let info = lngap_zk::challenges::ProgramInfo::load(&format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR"))).unwrap();
    let samples: Vec<(u32, u8)> = info.code_chunks.iter().flat_map(|c| c.data.iter().copied()).flat_map(|op| (0..8u8).map(move |m| (op, m))).collect();
    let (mut yes, mut no) = (0, 0);
    for key in &keys {
        let s = class_guard_script(key);
        let mut cases: Vec<(u32, u8)> = (0..60).map(|_| (rng.gen::<u32>(), rng.gen_range(0..8))).collect();
        cases.extend((0..60).map(|_| samples[rng.gen_range(0..samples.len())]));
        // every sample this class's guard should admit
        cases.extend(samples.iter().copied().filter(|&(op, m)| key_of(op, m).as_deref() == Some(key.as_str())).take(20));
        cases.extend([(0x0000_0073, 0), (0x0010_0073, 0), (0x0000_0073, 1), (0x0000_00f3, 0), (0x0000_0013, 0), (0x0000_0093, 0)]);
        for (op, micro) in cases {
            let want = guard_holds(key, op, micro);
            assert_eq!(script_holds(&s, op, micro), want, "{key}: opcode {op:#010x} micro {micro}");
            if want {
                yes += 1
            } else {
                no += 1
            }
        }
    }
    println!("{} classes; {yes} held, {no} refused", keys.len());
    assert!(yes > keys.len());
}

/// Every word of the Groth16 verifier's code, at each of its micro-steps,
/// passes its own class's guard (natively).
#[test]
#[ignore]
fn guard_complete_on_groth16() {
    let Ok(dir) = std::env::var("ZK_GROTH16_DIR") else { panic!("set ZK_GROTH16_DIR") };
    let info = lngap_zk::challenges::ProgramInfo::load(&format!("{dir}/groth16.yaml")).unwrap();
    let (mut words, mut checked) = (0, 0);
    let mut keys = std::collections::BTreeSet::new();
    for op in info.code_chunks.iter().flat_map(|c| c.data.iter().copied()) {
        words += 1;
        for micro in 0..8u8 {
            if let Some(k) = key_of(op, micro) {
                assert!(guard_holds(&k, op, micro), "{op:#010x} micro {micro} ({k})");
                keys.insert(k);
                checked += 1;
            }
        }
    }
    println!("{words} code words, {checked} (opcode, micro) pairs, {} classes: all pass their guard", keys.len());
}
