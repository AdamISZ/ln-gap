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
//!
//! S2: the challenges that read the final step's extra data (the claimed
//! hash, the reads' last-write steps, the prover's claim), each checking
//! the new head's digest first (`leaf_with_extra`). One leaf per read
//! (`_1`, `_2`) where BitVMX takes an unsigned read selector:
//!
//! - `zk_future_read_<r>`: read r's last write is after the agreed step;
//! - `zk_initialized_<k>_<r>`: read r was never written and its value is
//!   not the program's initialised data (per data chunk);
//! - `zk_uninitialized_<r>`: read r was never written, its address is
//!   uninitialised memory, and its value is not zero;
//! - `zk_halt`: the disputed step is the claimed last step, and it is not a
//!   success halt (ecall exit with 0) or its hash is not the claimed final
//!   hash.

use std::sync::Arc;

use anyhow::{anyhow, Result};
use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::challenges::{addresses_sections_challenge, entry_point_challenge, future_read_challenge, halt_challenge, initialized_challenge, opcode_challenge, program_counter_challenge, uninitialized_challenge};
use bitcoin_script_stack::stack::StackTracker;
use bitvmx_cpu_definitions::constants::CHUNK_SIZE;
use bitvmx_cpu_definitions::memory::{Chunk, SectionDefinition};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_pos::ttt::{Layout, PosLeaf};

use crate::OpensFile;
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
    pub data_chunks: Vec<Chunk>,
    pub uninitialized: SectionDefinition,
    /// The input section's first address and the input's words (D61).
    pub input_base: u32,
    pub input_words: usize,
}

impl ProgramInfo {
    /// From a BitVMX program definition (its ELF).
    pub fn load(pdf: &str) -> Result<ProgramInfo> {
        let pd = ProgramDefinition::from_config(pdf)?;
        let p = pd.load_program().map_err(|e| anyhow!("{e}"))?;
        // The registers are initialised by the loader (the stack pointer is
        // not zero), but BitVMX's get_uninitialized_ranges (rev 299009c6)
        // lists their section as uninitialised, so its UninitializedData
        // challenge fires on an honest first read of the stack pointer. Here
        // the register section is initialised data, holding the loader's
        // values, and is not among the uninitialised ranges.
        let regs = p.sections.iter().find(|s| s.registers).ok_or_else(|| anyhow!("no register section"))?;
        let (rstart, rend) = (regs.start, regs.start + regs.size - 1);
        let mut data_chunks = chunks(&p.sections, |s| s.initialized && !s.is_code);
        data_chunks.push(Chunk { base_addr: rstart, data: (0..regs.size / 4).map(|i| p.registers.get(i)).collect() });
        let mut uninitialized = p.get_uninitialized_ranges(&pd);
        let input_base = p.find_section_by_name(&pd.input_section_name).ok_or_else(|| anyhow!("no input section"))?.start;
        let input_words = pd.inputs.iter().map(|i| i.size as usize).sum::<usize>().div_ceil(4);
        uninitialized.ranges.retain(|&(a, b)| b < rstart || a > rend);
        Ok(ProgramInfo {
            entry: p.pc.get_address(),
            code_chunks: chunks(&p.sections, |s| s.is_code),
            read_write: p.read_write_sections.clone(),
            read_only: p.read_only_sections.clone(),
            registers: p.register_sections.clone(),
            code: p.code_sections.clone(),
            data_chunks,
            uninitialized,
            input_base,
            input_words,
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

pub fn entry_point_leaf(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> PosLeaf {
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

pub fn program_counter_leaf(l: &Layout, key: &impl OpensFile) -> PosLeaf {
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

pub fn opcode_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<PosLeaf> {
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

pub fn addresses_leaf(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> PosLeaf {
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
pub fn s1_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<PosLeaf> {
    let mut v = vec![entry_point_leaf(l, key, info), program_counter_leaf(l, key), addresses_leaf(l, key, info)];
    v.extend(opcode_leaves(l, key, info));
    v
}

// ----- S2: the leaves that read the extra data -----

fn step16(from_head: impl Iterator<Item = Src>) -> Vec<Src> {
    std::iter::repeat(Src::Konst(0)).take(8).chain(from_head).collect()
}

fn agreed16(n: usize) -> Vec<Src> {
    step16(digs(word_digits(n, N_AGREED)))
}

fn x_word64(off: usize) -> Vec<Src> {
    x_nibbles(off, 8).collect()
}

/// The two reads as BitVMX's challenges take them: address, value, last
/// write step (16 nibbles), for read 1 then read 2.
fn reads_src(p: usize) -> Vec<Src> {
    let mut v: Vec<Src> = digs(word_digits(p, P_R1A)).chain(digs(word_digits(p, P_R1V))).collect();
    v.extend(x_word64(X_LS1));
    v.extend(digs(word_digits(p, P_R2A)).chain(digs(word_digits(p, P_R2V))));
    v.extend(x_word64(X_LS2));
    v
}

/// The selected read: (address, value, last write step).
fn read_sel(f: &FinalStep, r: u8) -> (u32, u32, u64) {
    if r == 1 {
        (f.read.read_1_addr, f.read.read_1_value, f.last_step_1)
    } else {
        (f.read.read_2_addr, f.read.read_2_value, f.last_step_2)
    }
}

/// Never written (BitVMX's LAST_STEP_INIT).
pub const NEVER: u64 = u64::MAX;

/// Native mirror (needs the extra data).
pub fn future_read_fires(f: &FinalStep, r: u8) -> bool {
    let (_, _, ls) = read_sel(f, r);
    ls != NEVER && u64::from(f.agreed_step) < ls
}

pub fn future_read_leaf(l: &Layout, key: &impl OpensFile, r: u8) -> PosLeaf {
    let (_, n) = offsets(l);
    let mut src = agreed16(n);
    src.extend(x_word64(X_LS1));
    src.extend(x_word64(X_LS2));
    src.push(Src::Konst(i64::from(r)));
    PosLeaf { name: format!("zk_future_read_{r}"), script: leaf_with_extra(l, key, &[(src, tracked(future_read_challenge))]), fires: Arc::new(|_, _| false) }
}

/// Native mirror: read r never written, its address in chunk `c`, its
/// value not the chunk's word there.
pub fn initialized_fires(f: &FinalStep, r: u8, c: &Chunk) -> bool {
    let (a, v, ls) = read_sel(f, r);
    ls == NEVER && a >= c.base_addr && a % 4 == 0 && ((a - c.base_addr) / 4) < c.data.len() as u32 && c.data[((a - c.base_addr) / 4) as usize] != v
}

pub fn initialized_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<PosLeaf> {
    let (p, _) = offsets(l);
    let mut v = vec![];
    for (k, c) in info.data_chunks.iter().enumerate() {
        for r in [1u8, 2] {
            let mut src = reads_src(p);
            src.push(Src::Konst(i64::from(r)));
            let chunk = c.clone();
            v.push(PosLeaf { name: format!("zk_initialized_{k}_{r}"), script: leaf_with_extra(l, key, &[(src, tracked(|st| initialized_challenge(st, &chunk)))]), fires: Arc::new(|_, _| false) });
        }
    }
    v
}

/// Native mirror: read r never written, its address uninitialised, its
/// value not zero.
pub fn uninitialized_fires(f: &FinalStep, r: u8, info: &ProgramInfo) -> bool {
    let (a, v, ls) = read_sel(f, r);
    ls == NEVER && in_sections(a, &info.uninitialized) && v != 0
}

pub fn uninitialized_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<PosLeaf> {
    let (p, _) = offsets(l);
    [1u8, 2]
        .into_iter()
        .map(|r| {
            let mut src = reads_src(p);
            src.push(Src::Konst(i64::from(r)));
            let sections = info.uninitialized.clone();
            PosLeaf { name: format!("zk_uninitialized_{r}"), script: leaf_with_extra(l, key, &[(src, tracked(|st| uninitialized_challenge(st, &sections)))]), fires: Arc::new(|_, _| false) }
        })
        .collect()
}

/// Native mirror: the disputed step is the claimed last step, and it is
/// not an ecall exit (93) with code 0, or its hash is not the claimed final
/// hash.
pub fn halt_fires(f: &FinalStep) -> bool {
    u64::from(f.agreed_step) + 1 == f.claim_last_step && (f.read.read_1_value != 93 || f.read.read_2_value != 0 || f.read.opcode != 0x73 || f.hash != f.claim_last_hash)
}

pub fn halt_leaf(l: &Layout, key: &impl OpensFile) -> PosLeaf {
    let (p, n) = offsets(l);
    let mut src = x_word64(X_CLS);
    src.extend(agreed16(n));
    src.extend(digs(word_digits(p, P_R1V)));
    src.extend(digs(word_digits(p, P_R2V)));
    src.extend(opcode_digits(p, n));
    src.extend(x_nibbles(X_HASH, 20));
    src.extend(x_nibbles(X_CLH, 20));
    PosLeaf { name: "zk_halt".into(), script: leaf_with_extra(l, key, &[(src, tracked(halt_challenge))]), fires: Arc::new(|_, _| false) }
}

/// All of S2's leaves for a program.
pub fn s2_leaves(l: &Layout, key: &impl OpensFile, info: &ProgramInfo) -> Vec<PosLeaf> {
    let mut v = vec![future_read_leaf(l, key, 1), future_read_leaf(l, key, 2), halt_leaf(l, key)];
    v.extend(uninitialized_leaves(l, key, info));
    v.extend(initialized_leaves(l, key, info));
    v
}

/// The chunk index covering `pc`, if any (for picking the Opcode leaf).
pub fn chunk_for(info: &ProgramInfo, pc: u32) -> Option<usize> {
    info.code_chunks.iter().position(|c| pc >= c.base_addr && ((pc - c.base_addr) / 4) < c.data.len() as u32)
}
