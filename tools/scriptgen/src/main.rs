//! Dump BitVM's Script hash gadgets (MIT, github.com/BitVM/BitVM) as hex
//! files, and print their sizes.
//! SHA-256 conventions (bitvm/src/hash/sha256.rs): input = `n` single-byte
//! script numbers, last byte pushed first; output = 32 single-byte elements.
mod compress;
use bitvm::hash::sha256::sha256;
use std::path::PathBuf;

fn main() {
    let out = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../crates/contract/scripts");
    std::fs::create_dir_all(&out).unwrap();
    for n in [32usize, 64, 80] {
        let s = sha256(n).compile();
        let path = out.join(format!("sha256_{n}.bin"));
        std::fs::write(&path, s.as_bytes()).unwrap();
        println!("sha256({n}) byte-wise: {} bytes", s.len());
    }
    for n in [32u32, 64, 80] {
        let s = bitvm::hash::sha256_u4::sha256(n).compile();
        let path = out.join(format!("sha256_u4_{n}.bin"));
        std::fs::write(&path, s.as_bytes()).unwrap();
        println!("sha256_u4({n}) nibble-wise: {} bytes", s.len());
    }
    for n in [32usize, 64, 80] {
        let s = bitvm::hash::blake3::blake3_compute_script(n).compile();
        println!("blake3({n}): {} bytes", s.len());
    }
    for add in [false, true] {
        match compress::self_test(add) {
            Ok((len, stack)) => {
                println!("sha256_compress_u4(add_table={add}): OK, {len} bytes, max stack {stack}");
                let s = compress::sha256_compress_u4(add).compile();
                std::fs::write(out.join(format!("sha256_compress_u4{}.bin", if add { "_addtable" } else { "" })), s.as_bytes()).unwrap();
            }
            Err(e) => println!("sha256_compress_u4(add_table={add}): {e}"),
        }
    }
}
