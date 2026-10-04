# Programs for the zk harness

`hello-world.elf`, `hello-world.yaml` and `hello-world.c` are copied
unchanged from FairgateLabs/bitvmx-docker-riscv32 (MIT), as vendored in
BitVMX-CPU at rev 299009c6 (`docker-riscv32/riscv32/build/`, `src/`).
The program returns 0 iff its 4-byte input is 0x11111111.

The Groth16 verifier ELF is not vendored: it is built from
FairgateLabs/bitvmx-zk-verifier, which is GPL-3.0. See
../GROTH16.md: `../scripts/groth16-setup.sh` copies it out of your Cargo
checkout of BitVMX-CPU, patches it to a sample proof's parameters and
encodes the proof as its input.
