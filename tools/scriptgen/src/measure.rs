//! Size measurements of BitVM gadgets we may use.
use bitvm::signatures::winternitz::{
    generate_public_key, BinarysearchVerifier, BruteforceVerifier, ListpickVerifier, Parameters, VoidConverter, Winternitz,
};

pub fn winternitz_sizes() {
    let ps = Parameters::new_by_bit_length(256, 4);
    let sk: Vec<u8> = (0..20u8).collect();
    let pk = generate_public_key(&ps, &sk);
    let msg: Vec<u8> = (0..32u8).map(|i| i.wrapping_mul(77)).collect();
    let lp = Winternitz::<ListpickVerifier, VoidConverter>::new();
    let bf = Winternitz::<BruteforceVerifier, VoidConverter>::new();
    let bs = Winternitz::<BinarysearchVerifier, VoidConverter>::new();
    let wit = lp.sign(&ps, &sk, &msg);
    let wit_bytes: usize = wit.iter().map(|e| e.len()).sum();
    println!(
        "winternitz 256-bit/4-bit digits ({} digits incl. checksum): witness {} elements, {} bytes",
        ps.total_digit_len(),
        wit.len(),
        wit_bytes
    );
    println!("  listpick verify script: {} bytes", lp.checksig_verify(&ps, &pk).compile().len());
    println!("  bruteforce verify script: {} bytes", bf.checksig_verify(&ps, &pk).compile().len());
    println!("  binarysearch verify script: {} bytes", bs.checksig_verify(&ps, &pk).compile().len());
}

pub fn sha256_stack_size() {
    use bitcoin_script_stack::stack::StackTracker;
    let mut st = StackTracker::new();
    let s = bitvm::hash::sha256_u4_stack::sha256_stack(&mut st, 32, false, true);
    println!("sha256_stack(32, no add table, full xor): {} bytes", s.compile().len());
}
