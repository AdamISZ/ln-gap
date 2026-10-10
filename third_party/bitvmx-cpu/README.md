# BitVMX-CPU, patched

The workspace builds BitVMX-CPU (FairgateLabs, Apache-2.0) from
`upstream/bitvmx-cpu/BitVMX-CPU`: the upstream commit 299009c with these
patches applied (see `[patch]` in the workspace `Cargo.toml`). Create the
tree with `tools/setup-bitvmx-cpu.sh`.

- 0001-0003: fixes found by LN-GAP's tests (code and initialized-data
  chunks placed at word offsets as if bytes; the register section treated
  as uninitialized), with tests that fail on 299009c.
- 0004: the authenticated jump list (S. D. Lerner, "Latest innovations in
  BitVMX", June 2024), opt-in by `jump_list: true` in a program definition
  (JUMPLIST_PLAN.md, J4). The linear hash chain is unchanged by default.
- 0005: fault injection of a wrong long-jump hash (`fail_jump`), for tests.
