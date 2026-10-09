//! The withdrawal statement, PLACEHOLDER: it commits the claimed `(b, c)`
//! as the journal (two little-endian words) and checks nothing. The
//! statement proper (a return note of `b` with memo `c` in a final state)
//! replaces it; this guest exists to set up and test the proving pipeline,
//! STARK here and the Groth16 wrap on x86 Linux.

use risc0_zkvm::guest::env;

fn main() {
    let (b, c): (u32, u32) = env::read();
    let mut journal = [0u8; 8];
    journal[..4].copy_from_slice(&b.to_le_bytes());
    journal[4..].copy_from_slice(&c.to_le_bytes());
    env::commit_slice(&journal);
}
