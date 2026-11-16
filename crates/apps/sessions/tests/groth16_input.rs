//! Opt-in: BitVMX's Groth16 verifier ELF, as the disputes run it (the
//! shipped ELF with RISC Zero 3.1's key and constants written in,
//! `lngap_zk::groth16::verifier_elf`), run on the Groth16 receipt of OUR
//! guest made with RISC Zero 3.1.0 (r0/, tests/data): it accepts the
//! receipt and refuses it with b changed, deciding as
//! `lngap_zk::groth16::verify_input` does. A few minutes per run in release.

use std::time::Instant;

use emulator::decision::challenge::prover_execute;
use lngap_zk::groth16;

/// Runs the verifier on `input`: its result, as the emulator prints it.
fn run(dir: &std::path::Path, input: &[u8]) -> String {
    let w = format!("{}/", dir.display());
    let t = Instant::now();
    let (result, last_step, _) = prover_execute(&format!("{w}groth16.yaml"), input.to_vec(), &w, &w, true, None, false).unwrap();
    println!("G16 ours: {result:?} after {last_step} steps ({:.0?})", t.elapsed());
    format!("{result:?}")
}

#[test]
#[ignore]
fn the_verifier_accepts_our_receipt() {
    let input = hex::decode(include_str!("data/withdraw-9-42-deployment.hex").trim()).unwrap();
    let dir = std::env::temp_dir().join(format!("lngap-g16ours-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("zkverifier.elf"), groth16::verifier_elf(&groth16::shipped_verifier_elf().unwrap()).unwrap()).unwrap();
    std::fs::write(dir.join("groth16.yaml"), format!("elf: zkverifier.elf\nnary_search: 8\nmax_steps: 536870912\ninput_section_name: .input\njump_list: true\ninputs:\n  - size: {}\n    owner: prover\n", input.len())).unwrap();
    assert!(groth16::verify_input(&input).is_ok());
    let accepted = run(&dir, &input);
    let mut tampered = input.clone();
    tampered[164] ^= 3; // b, the journal's first word
    assert!(groth16::verify_input(&tampered).is_err());
    let refused = run(&dir, &tampered);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(accepted.starts_with("Halt(0,"), "the verifier must accept: {accepted}");
    assert!(!refused.starts_with("Halt(0,"), "the verifier must refuse b changed: {refused}");
}
