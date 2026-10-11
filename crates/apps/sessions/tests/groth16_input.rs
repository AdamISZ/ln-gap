//! Opt-in: BitVMX's Groth16 verifier ELF, as shipped (no patch), run on a
//! Groth16 receipt of OUR guest made with RISC Zero 3.0.6 (r0/). Needs
//! `G16_OURS_DIR` holding `groth16.yaml` (naming the unpatched ELF) and
//! `input.hex` (the receipt encoded by Fairgate's `proof-as-input`). A
//! few minutes in release.

use std::time::Instant;

use emulator::decision::challenge::prover_execute;

#[test]
#[ignore]
fn the_verifier_accepts_our_receipt() {
    let Ok(dir) = std::env::var("G16_OURS_DIR") else { panic!("set G16_OURS_DIR") };
    let input = hex::decode(std::fs::read_to_string(format!("{dir}/input.hex")).unwrap().trim()).unwrap();
    let work = std::env::temp_dir().join(format!("lngap-g16ours-{}", std::process::id()));
    std::fs::create_dir_all(&work).unwrap();
    let w = format!("{}/", work.display());
    let t = Instant::now();
    let (result, last_step, last_hash) = prover_execute(&format!("{dir}/groth16.yaml"), input.clone(), &w, &w, true, None, false).unwrap();
    let _ = std::fs::remove_dir_all(&work);
    println!("G16 ours: {:?} after {last_step} steps ({:.0?}), last hash {last_hash}", result, t.elapsed());
    assert!(format!("{result:?}").starts_with("Halt(0,"), "the verifier must accept: {result:?}");
}
