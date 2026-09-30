# Programs for the zk harness

`hello-world.elf`, `hello-world.yaml` and `hello-world.c` are copied
unchanged from FairgateLabs/bitvmx-docker-riscv32 (MIT), as vendored in
BitVMX-CPU at rev 299009c6 (`docker-riscv32/riscv32/build/`, `src/`).
The program returns 0 iff its 4-byte input is 0x11111111.

The Groth16 verifier ELF is not vendored: it is built from
FairgateLabs/bitvmx-zk-verifier, which is GPL-3.0. See
docs/planning/DEMOS_PLAN.md (2026-09-30) for how to obtain it and pair
it with a valid proof.
