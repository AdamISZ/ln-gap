//! Write the built guest's program binary to a file and print its image
//! id: `export-guest <out>`.

use std::fmt::Write;

use lngap_r0_methods::{WITHDRAW_ELF, WITHDRAW_ID};

fn main() {
    let out = std::env::args().nth(1).expect("usage: export-guest <out>");
    std::fs::write(&out, WITHDRAW_ELF).expect("writing the binary");
    let id = WITHDRAW_ID.iter().flat_map(|w| w.to_le_bytes()).fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    });
    println!("{out}: {} bytes, image id {id}", WITHDRAW_ELF.len());
}
