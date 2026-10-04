//! Measurement (ZK_Z3_PLAN.md, step 1): the final depth's leaf set, which
//! every channel update re-signs while the contract is live. One prove
//! leaf per BitVMX instruction class (D59), plus the S1 and S2 claimant
//! disproves (their count depends on the program's chunks). How many
//! leaves, how many bytes, how long to build?
//!
//! hello-world always; the Groth16 verifier with ZK_GROTH16_DIR.

use std::sync::Arc;
use std::time::Instant;

use bitcoin_script_riscv::riscv::instruction_mapping::generate_sample_instructions;
use lngap_pos::instance::mover_at;
use lngap_pos::rebut::pair_key;
use lngap_pos::ttt::Layout;
use lngap_zk::challenges::*;
use lngap_zk::prove_leaf;

const GAME: u16 = 1;
const D: u32 = 2;

fn measure(name: &str, yaml: &str) {
    let sk = pair_key([21; 32]);
    let info = ProgramInfo::load(yaml).unwrap();
    let l = Layout::at(D, GAME, mover_at(D));
    let t = Instant::now();
    let classes = generate_sample_instructions();
    let prove: Vec<_> = classes.iter().map(|(ins, micro)| prove_leaf(&l, &sk.public(), ins, *micro, Arc::new(|_, _| false))).collect();
    let t_prove = t.elapsed();
    let t = Instant::now();
    let s1 = s1_leaves(&l, &sk.public(), &info);
    let s2 = s2_leaves(&l, &sk.public(), &info);
    let t_s = t.elapsed();
    let bytes = |v: &[lngap_pos::ttt::PosLeaf]| v.iter().map(|x| x.script.len()).sum::<usize>();
    let mut names: Vec<_> = prove.iter().map(|p| p.name.clone()).collect();
    names.sort();
    names.dedup();
    println!(
        "{name}: prove {} leaves ({} distinct), {:.1} MB, {t_prove:.2?}; S1 {} leaves {:.1} MB, S2 {} leaves {:.1} MB, {t_s:.2?}; largest {} KB",
        prove.len(),
        names.len(),
        bytes(&prove) as f64 / 1e6,
        s1.len(),
        bytes(&s1) as f64 / 1e6,
        s2.len(),
        bytes(&s2) as f64 / 1e6,
        prove.iter().chain(&s1).chain(&s2).map(|x| x.script.len()).max().unwrap() / 1000
    );
}

#[test]
fn final_leaves_hello() {
    measure("hello-world", &format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR")));
}

#[test]
#[ignore]
fn final_leaves_groth16() {
    let Ok(dir) = std::env::var("ZK_GROTH16_DIR") else { panic!("set ZK_GROTH16_DIR") };
    measure("groth16", &format!("{dir}/groth16.yaml"));
}
