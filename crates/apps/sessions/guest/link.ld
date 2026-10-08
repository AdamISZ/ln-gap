/* BitVMX's memory map (as in BitVMX-CPU's docker-riscv32/linker/link.ld),
   one segment per section so the file doesn't span the address gaps */
ENTRY(_start)
PHDRS { text PT_LOAD; data PT_LOAD; rodata PT_LOAD; bss PT_LOAD; input PT_LOAD; stack PT_LOAD; }
SECTIONS
{
    .text 0x80000000 : ALIGN(4) { KEEP(*(.text._start)) *(.text .text.*) . = ALIGN(4); } :text
    .data 0x90000000 : ALIGN(4) { *(.data .data.*) *(.sdata .sdata.*) LONG(0xDEADBEEF) . = ALIGN(4); } :data
    .rodata 0xB0000000 : ALIGN(4) { KEEP(*(.rodata.returns)) *(.rodata .rodata.*) *(.srodata .srodata.*) . = ALIGN(4); } :rodata
    .bss 0xA0000000 (NOLOAD) : ALIGN(4) { KEEP(*(.bss.reserved)) *(.bss .bss.*) *(.sbss .sbss.*) . = ALIGN(4); } :bss
    .input 0xAA000000 (NOLOAD) : ALIGN(4) { KEEP(*(.input)) . = ALIGN(4); } :input
    .stack 0xE0000000 (NOLOAD) : ALIGN(4) { KEEP(*(.stack)) . = ALIGN(4); } :stack
    /DISCARD/ : { *(.eh_frame) *(.comment) *(.riscv.attributes) }
}
