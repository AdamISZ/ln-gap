//! S1 of ZK_SOUNDNESS_PLAN.md: the claimant's disproves at the final step
//! that need nothing beyond the parked pair and the program's own
//! constants. Each is BitVMX's verifier challenge script, unchanged (they
//! end in an inequality or a verify of one: already the disprove
//! orientation), behind our pair readout:
//!
//! - `zk_entry_point`: at step 1, the pc read is not the program's entry;
//! - `zk_program_counter`: the pc read is not the pc the previous step
//!   wrote. The claimant supplies the hash two steps back and the previous
//!   step's write record as witness nibbles; the script range-checks them
//!   and checks that they hash to the agreed previous hash;
//! - `zk_opcode_<k>`: the opcode is not the program's instruction at the
//!   pc, one leaf per code chunk of BitVMX's `CHUNK_SIZE` words;
//! - `zk_addresses_sections`: a read, the write or the pc is outside the
//!   section its memory witness allows, or misaligned.

use std::sync::Arc;

use anyhow::{anyhow, Result};
use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::challenges::{addresses_sections_challenge, entry_point_challenge, opcode_challenge, program_counter_challenge};
use bitcoin_script_stack::stack::StackTracker;
use bitvmx_cpu_definitions::constants::CHUNK_SIZE;
use bitvmx_cpu_definitions::memory::{Chunk, SectionDefinition};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_lamport::winternitz::WotsPublic;
use lngap_pos::ttt::{Layout, PosLeaf};

use crate::*;

/// The program's constants the challenges bake in.
#[derive(Clone, Debug)]
pub struct ProgramInfo {
    pub entry: u32,
    pub code_chunks: Vec<Chunk>,
    pub read_write: SectionDefinition,
    pub read_only: SectionDefinition,
    pub registers: SectionDefinition,
    pub code: SectionDefinition,
}

impl ProgramInfo {
    /// From a BitVMX program definition (its ELF).
    pub fn load(pdf: &str) -> Result<ProgramInfo> {
        let p = ProgramDefinition::from_config(pdf)?.load_program().map_err(|e| anyhow!("{e}"))?;
        Ok(ProgramInfo {
            entry: p.pc.get_address(),
            code_chunks: chunks(&p.sections, |s| s.is_code),
            read_write: p.read_write_sections.clone(),
            read_only: p.read_only_sections.clone(),
            registers: p.register_sections.clone(),
            code: p.code_sections.clone(),
        })
    }
}

/// A program's sections as chunks of `CHUNK_SIZE` words, each at its true
/// byte address. BitVMX's `Program::get_chunks` (rev 299009c6) places
/// chunk `i` at `start + i * CHUNK_SIZE`, counting words as bytes, so every
/// chunk after a section's first claims an address range that does not
/// hold its words; this is the corrected form.
pub fn chunks(sections: &[emulator::loader::program::Section], filter: impl Fn(&emulator::loader::program::Section) -> bool) -> Vec<Chunk> {
    sections
        .iter()
        .filter(|s| filter(s))
        .flat_map(|s| {
            s.data.chunks(CHUNK_SIZE as usize).enumerate().map(move |(i, words)| Chunk {
                base_addr: s.start + i as u32 * CHUNK_SIZE * 4,
                data: words.iter().map(|w| u32::from_be(*w)).collect(),
            })
        })
        .collect()
}

fn tracked(f: impl FnOnce(&mut StackTracker)) -> ScriptBuf {
    let mut st = StackTracker::new();
    f(&mut st);
    st.get_script()
}

fn digs(it: impl Iterator<Item = usize>) -> impl Iterator<Item = Src> {
    it.map(Src::Dig)
}

fn offsets(l: &Layout) -> (usize, usize) {
    (l.prior.expect("the final step's leaves read a prior head: depth >= 2"), l.new)
}

fn opcode_digits(p: usize, n: usize) -> impl Iterator<Item = Src> {
    let (hi, lo) = (p + 8 + 2 * P_OPHI, n + 8 + 2 * N_OPLO);
    digs((hi..hi + 4).chain(lo..lo + 4))
}

// ----- EntryPoint -----

/// Native mirror: the disputed step is step 1 and its pc (with micro-step
/// 0) is not the entry point.
pub fn entry_point_fires(f: &FinalStep, entry: u32) -> bool {
    f.agreed_step == 0 && (f.read.pc != entry || f.read.micro != 0)
}

pub fn entry_point_leaf(l: &Layout, key: &WotsPublic, info: &ProgramInfo) -> PosLeaf {
    let (p, n) = offsets(l);
    let mut src: Vec<Src> = digs(word_digits(p, P_PC)).chain(digs(byte_digits(p, P_MICRO))).collect();
    // the agreed step as 16 nibbles: the head holds its low 32 bits
    src.extend(std::iter::repeat(Src::Konst(0)).take(8));
    src.extend(digs(word_digits(n, N_AGREED)));
    let entry = info.entry;
    PosLeaf {
        name: "zk_entry_point".into(),
        script: leaf_script_src(l, key, &src, &tracked(|st| entry_point_challenge(st, entry))),
        fires: Arc::new(move |p, n| entry_point_fires(&FinalStep::parse(p, n), entry)),
    }
}

// ----- ProgramCounter -----

/// The claimant's witness for `zk_program_counter`: the hash after step
/// i-2 and step i-1's write record, as nibbles (first deepest); they go
/// below the pair reveal in the witness.
pub fn program_counter_witness(prev_prev_hash: &[u8; 20], prev_write: &Step) -> Vec<Vec<u8>> {
    let mut bytes = prev_prev_hash.to_vec();
    bytes.extend_from_slice(&prev_write.to_bytes());
    bytes.iter().flat_map(|b| [b >> 4, b & 15]).map(|v| if v == 0 { vec![] } else { vec![v] }).collect()
}

/// Native mirror, given the claimant's witness: the witness hashes to the
/// agreed previous hash, and the pc (with micro-step) it wrote is not the
/// pc read.
pub fn program_counter_fires(f: &FinalStep, prev_prev_hash: &[u8; 20], prev_write: &Step) -> bool {
    step_hash(prev_prev_hash, prev_write) == f.prev_hash && (prev_write.pc, prev_write.micro) != (f.read.pc, f.read.micro)
}

pub fn program_counter_leaf(l: &Layout, key: &WotsPublic) -> PosLeaf {
    let (p, _) = offsets(l);
    let src: Vec<Src> = digs(word_digits(p, P_PC)).chain(digs(byte_digits(p, P_MICRO))).chain(digs(p + 8 + 2 * P_PREV..p + 8 + 2 * P_PREV + 40)).collect();
    PosLeaf {
        name: "zk_program_counter".into(),
        script: leaf_script_src(l, key, &src, &tracked(program_counter_challenge)),
        // needs the claimant's witness: see program_counter_fires
        fires: Arc::new(|_, _| false),
    }
}

// ----- Opcode -----

/// Native mirror for chunk `c`: the pc falls in it and its word there is
/// not the opcode.
pub fn opcode_fires(f: &FinalStep, c: &Chunk) -> bool {
    let pc = f.read.pc;
    pc >= c.base_addr && ((pc - c.base_addr) / 4) < c.data.len() as u32 && pc % 4 == 0 && c.data[((pc - c.base_addr) / 4) as usize] != f.read.opcode
}

pub fn opcode_leaves(l: &Layout, key: &WotsPublic, info: &ProgramInfo) -> Vec<PosLeaf> {
    let (p, n) = offsets(l);
    let src: Vec<Src> = digs(word_digits(p, P_PC)).chain(opcode_digits(p, n)).collect();
    info.code_chunks
        .iter()
        .enumerate()
        .map(|(k, c)| {
            let chunk = c.clone();
            let mirror = c.clone();
            PosLeaf {
                name: format!("zk_opcode_{k}"),
                script: leaf_script_src(l, key, &src, &tracked(|st| opcode_challenge(st, &chunk))),
                fires: Arc::new(move |p, n| opcode_fires(&FinalStep::parse(p, n), &mirror)),
            }
        })
        .collect()
}

// ----- AddressesSections -----

fn in_sections(a: u32, s: &SectionDefinition) -> bool {
    s.ranges.iter().any(|&(start, end)| start <= a && a <= end.saturating_sub(3))
}

/// Native mirror of BitVMX's `addresses_sections_challenge`: some read or
/// the write is outside the sections its memory witness names, or
/// misaligned, or the pc is outside the code or misaligned.
pub fn addresses_fire(f: &FinalStep, info: &ProgramInfo) -> bool {
    let w = f.read.mem_witness;
    let (r1, r2, wr) = (w >> 4, (w >> 2) & 3, w & 3);
    // BitVMX's MemoryAccessType: 0 register, 1 memory, 2 unused (see
    // bitvmx_cpu_definitions::memory::memory_access_type)
    use bitvmx_cpu_definitions::memory::memory_access_type::{MEMORY, REGISTER};
    let bad_read = |t: u8, a: u32| (t == MEMORY && !in_sections(a, &info.read_write) && !in_sections(a, &info.read_only)) || (t == REGISTER && !in_sections(a, &info.registers)) || a % 4 != 0;
    let bad_write = |t: u8, a: u32| (t == MEMORY && !in_sections(a, &info.read_write)) || (t == REGISTER && !in_sections(a, &info.registers)) || a % 4 != 0;
    let bad_pc = |a: u32| !in_sections(a, &info.code) || a % 4 != 0;
    bad_read(r1, f.read.read_1_addr) || bad_read(r2, f.read.read_2_addr) || bad_write(wr, f.write.write_addr) || bad_pc(f.read.pc)
}

pub fn addresses_leaf(l: &Layout, key: &WotsPublic, info: &ProgramInfo) -> PosLeaf {
    let (p, n) = offsets(l);
    let src: Vec<Src> = digs(word_digits(p, P_R1A))
        .chain(digs(word_digits(p, P_R2A)))
        .chain(digs(word_digits(n, N_WADDR)))
        .chain(digs(byte_digits(p, P_MEMW)))
        .chain(digs(word_digits(p, P_PC)))
        .collect();
    let i = info.clone();
    let mirror = info.clone();
    PosLeaf {
        name: "zk_addresses_sections".into(),
        script: leaf_script_src(l, key, &src, &tracked(|st| addresses_sections_challenge(st, &i.read_write, &i.read_only, &i.registers, &i.code))),
        fires: Arc::new(move |p, n| addresses_fire(&FinalStep::parse(p, n), &mirror)),
    }
}

/// All of S1's leaves for a program.
pub fn s1_leaves(l: &Layout, key: &WotsPublic, info: &ProgramInfo) -> Vec<PosLeaf> {
    let mut v = vec![entry_point_leaf(l, key, info), program_counter_leaf(l, key), addresses_leaf(l, key, info)];
    v.extend(opcode_leaves(l, key, info));
    v
}

/// The chunk index covering `pc`, if any (for picking the Opcode leaf).
pub fn chunk_for(info: &ProgramInfo, pc: u32) -> Option<usize> {
    info.code_chunks.iter().position(|c| pc >= c.base_addr && ((pc - c.base_addr) / 4) < c.data.len() as u32)
}
