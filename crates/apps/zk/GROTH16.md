# Running the Groth16 dispute yourself

The default zero-knowledge examples dispute a small RISC-V program
(`programs/hello-world.elf`) and need nothing beyond the repository. The
headline example, a dispute over **BitVMX's Groth16 verifier** checking a
real RISC Zero proof (478,727,216 steps, searched in 29 rounds on the venue,
one step proved on regtest), needs three things the repository can't ship.
The script `scripts/groth16-setup.sh` assembles them on your machine.

    crates/apps/zk/scripts/groth16-setup.sh ~/groth16

It takes about a minute (plus a first-time build of a small Rust tool), and
needs `git`, `python3`, a Rust toolchain and network access.

Then:

    # the narrated dispute (about 5½ minutes)
    cargo run --release -p lngap-zk --bin lngap-zk-demo -- groth16 ~/groth16 honest
    cargo run --release -p lngap-zk --bin lngap-zk-demo -- groth16 ~/groth16 tampered

    # the search played as a game through the dispute graph, the final step proved on regtest
    ZK_GROTH16_DIR=~/groth16 cargo test --release -p lngap-zk --test zk_graph groth16_on_regtest -- --ignored --nocapture

The other opt-in tests read the same directory: `zk_search groth16`,
`zk_challenges s1_groth16_constants`, `zk_final_leaves final_leaves_groth16`
and `zk_guard guard_complete_on_groth16`. Run any of them with
`ZK_GROTH16_DIR=… … -- --ignored`. `zk_graph`, `zk_search` and
`zk_challenges` also need `bitcoind`, as the demo does.

## What the script does, and why

**1. The verifier program.** The program being disputed is BitVMX's Groth16
verifier compiled for RISC-V (`zkverifier-new-mul.elf`, built from
FairgateLabs/bitvmx-zk-verifier). It is **GPL-3.0**, so this repository
doesn't include it. It doesn't have to: BitVMX-CPU's repository carries a
built copy (`docker-riscv32/verifier/build/`), and Cargo has already
downloaded BitVMX-CPU as a dependency of `lngap-zk`. The script copies it
out of your Cargo checkout and checks its hash.

**2. A proof to verify.** Fairgate's `rust-bitvmx-zk-proof` (Apache-2.0)
includes a sample Groth16 proof (`snark-seal.json`) of a toy guest program:
it commits `1` if its input is below 100, `0` otherwise, and the sample
proves a `1`. The guest doesn't matter for the dispute: a trivial guest and
a huge computation give the same proof size and the same verifier
execution. The script clones that repository at a pinned commit and builds
its `verifier` tool, whose `proof-as-input` command encodes the proof as the
verifier program's 168-byte input: the journal length, the image ID, the
three compressed proof points, the journal. The result is checked
byte-for-byte against the input that ran the paper's dispute.

**3. A parameter patch.** The ELF was built for RISC Zero v3's parameters,
but the sample proof was made under older ones, so as shipped the verifier
rejects it. The script overwrites the three affected constants in the
ELF's public-input table (file offset 716804): the control root (two
16-byte halves, at +0 and +32) and the BN254 control ID (32 bytes, at +128).
The patched ELF is checked against a known hash. A proof made under v3's
parameters would need no patch, but generating one needs RISC Zero's
x86 tooling.

**4. Program definitions.** BitVMX's tools describe a program with a small
YAML file naming the ELF, the search arity and the input. The script writes
two: `groth16.yaml` (8-ary search, used by the narrated demo and most tests)
and `groth16-binary.yaml` (binary search, used by the game played through
the dispute graph).

The patched ELF is still GPL-3.0. Keep the directory to yourself; don't
commit it here.

## What you should see

The narrated demo runs BitVMX's search between a prover who claims the
verifier accepts the proof and a challenger who disputes it, narrowing 478
million steps to one, then resolves that step on regtest: with `honest` the
prover proves the halting `ecall`, and with `tampered` (one byte of the
proof flipped, acceptance still claimed) the prover can't, and the
challenger's timeout pays it. The `zk_graph` test plays the same search
as a 119-depth contract, with every move sealed by the venue, and ends with
the claim (about 220 vB), the rebuttal (about 24 kvB) and the proof of the
final step (about 58.5 kvB) on regtest. On-chain cost doesn't depend on the
program's length.
