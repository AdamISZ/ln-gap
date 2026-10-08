//! The withdrawal statement, MOCKED (V25_POC_PLAN.md, Phase 6).
//!
//! The real statement checks that a return of `b` with memo `c` to the
//! hub is in a final L2 state (the sequencer's signature, a Merkle
//! path). Here the final state's returns are a table in the program
//! itself, patched in by the harness: the program accepts (returns 0) iff
//! its input `c` is the session's identifier and `(b, c)` is in the
//! table. The game, the dispute graph and the payout around it are what
//! the PoC exercises.
//!
//! Input (8 bytes, little-endian words): `b`, `c`.

#![no_std]
#![no_main]

use core::ptr::read_volatile;

const INPUT: *const u32 = 0xAA00_0000 as *const u32;

/// The table: a marker the harness finds in the ELF, the session's
/// identifier, a count, then up to 16 `(b, c)` pairs.
#[no_mangle]
#[used]
#[link_section = ".rodata.returns"]
pub static RETURNS: [u32; 36] = {
    let mut t = [0u32; 36];
    t[0] = 0x5041_474C; // "LGAP"
    t[1] = 0x5445_5252; // "RRET"
    t
};

core::arch::global_asm!(
    ".section .text._start",
    ".globl _start",
    "_start:",
    "  li sp, 0xE07FFFF0",
    "  call main",
    "  li a7, 93",
    "  ecall",
    ".section .stack, \"aw\", @nobits",
    "  .space 0x800000",
    // reserved as in BitVMX's entrypoint: 0x1000 + one word as stdout
    ".section .bss.reserved, \"aw\", @nobits",
    "  .space 4100",
    ".section .input, \"aw\", @nobits",
    "  .skip 0x2000",
);

#[no_mangle]
pub extern "C" fn main() -> u32 {
    // volatile reads: the table is patched after compiling
    let t = RETURNS.as_ptr();
    let (b, c) = unsafe { (read_volatile(INPUT), read_volatile(INPUT.add(1))) };
    if c != unsafe { read_volatile(t.add(2)) } {
        return 2;
    }
    let n = unsafe { read_volatile(t.add(3)) }.min(16) as usize;
    for i in 0..n {
        let (tb, tc) = unsafe { (read_volatile(t.add(4 + 2 * i)), read_volatile(t.add(5 + 2 * i))) };
        if tb == b && tc == c {
            return 0;
        }
    }
    1
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
