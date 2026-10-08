//! The withdrawal statement, MOCKED: a BitVMX program (`guest/`, built to
//! `programs/withdraw.elf`) that accepts its input `(b, c)` iff `c` is the
//! session's identifier and `(b, c)` is in a table of returns. The harness
//! patches the session's identifier and the toy L2's returns into the ELF,
//! standing in for "a return of `b` with memo `c` is in a final state".

use std::path::Path;

use anyhow::{ensure, Context, Result};

/// The program as built (an empty table).
pub const ELF: &[u8] = include_bytes!("../programs/withdraw.elf");

/// The table's marker ("LGAP", "RRET" as little-endian words).
const MARKER: [u8; 8] = [0x4C, 0x47, 0x41, 0x50, 0x52, 0x52, 0x45, 0x54];

/// At most this many returns in the table.
pub const MAX_RETURNS: usize = 16;

/// BitVMX's bound on the program's steps (binary search: 8 rounds).
pub const MAX_STEPS: u64 = 256;

/// The ELF with the session's identifier and the returns patched in.
pub fn patched(session: u32, returns: &[(u32, u32)]) -> Result<Vec<u8>> {
    ensure!(returns.len() <= MAX_RETURNS, "at most {MAX_RETURNS} returns");
    let at = ELF.windows(8).position(|w| w == MARKER).context("the table's marker")?;
    let mut elf = ELF.to_vec();
    let mut words = vec![session, returns.len() as u32];
    for (b, c) in returns {
        words.extend([*b, *c]);
    }
    for (i, w) in words.iter().enumerate() {
        let o = at + 8 + 4 * i;
        elf[o..o + 4].copy_from_slice(&w.to_le_bytes());
    }
    Ok(elf)
}

/// The program's input: `b` and `c`, little-endian words.
pub fn input(b: u32, c: u32) -> Vec<u8> {
    [b.to_le_bytes(), c.to_le_bytes()].concat()
}

/// Write the patched ELF and its BitVMX definition (binary search) under
/// `dir`; returns the definition's path.
pub fn write_program(dir: &Path, session: u32, returns: &[(u32, u32)]) -> Result<String> {
    std::fs::create_dir_all(dir)?;
    std::fs::write(dir.join("withdraw.elf"), patched(session, returns)?)?;
    let yaml = dir.join("withdraw.yaml");
    std::fs::write(
        &yaml,
        format!("elf: withdraw.elf\nnary_search: 2\nmax_steps: {MAX_STEPS}\ninput_section_name: .input\ninputs:\n  - size: 8\n    owner: prover\n"),
    )?;
    Ok(yaml.display().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_table_is_patched_at_its_marker() {
        let e = patched(7, &[(5, 7), (9, 7)]).unwrap();
        let at = e.windows(8).position(|w| w == MARKER).unwrap();
        let w = |i: usize| u32::from_le_bytes(e[at + 8 + 4 * i..at + 12 + 4 * i].try_into().unwrap());
        assert_eq!((w(0), w(1), w(2), w(3), w(4), w(5)), (7, 2, 5, 7, 9, 7));
        assert_eq!(e.len(), ELF.len());
    }
}
