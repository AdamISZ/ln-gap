# Proving the sessions guest and wrapping it in Groth16

The sessions PoC disputes one program on Bitcoin: BitVMX's Groth16
verifier. To feed it a real proof of *our* withdrawal guest, the guest's
RISC Zero receipt must be wrapped in Groth16. Every step of that runs on
a Mac except the last, RISC Zero's Groth16 prover, which is a Docker
image for **x86_64 only** (gnark plus the proving key). This directory is
the RISC Zero side: the guest (`methods/guest`), a host tool `lngap-r0`
(`host/`) and these scripts.

Everything is pinned to **RISC Zero 3.0.6**. The BitVMX verifier ELF
bakes in RISC Zero 3.0's control root (`a54dc85a…1f56`) and BN254
control id (`c07a6514…4404`), so receipts made with any 3.0 release
verify with it unpatched (the older sample proof needed a patch; see
`crates/apps/zk/GROTH16.md`).

## On the Linux machine

**You need:** x86_64 Linux; Rust (`rustup`); Docker Engine usable by
your user (`docker info` works without sudo); git and curl; about 15 GB
of free disk; 16 GB of RAM or more is safest for the Groth16 step (the
setup script warns below that). GNU `time` (`apt install time`) is
optional: with it, the logs record peak memory.

1. Get the branch (after it has been pushed):

       git clone <the repo> ln-gap && cd ln-gap
       git checkout v25-seal
       cd crates/apps/sessions/r0

2. Set up (user-level, no sudo; about 10 minutes, mostly the image pull
   and the build):

       scripts/linux-setup.sh

   It checks the machine, installs RISC Zero's `rzup` (its installer
   adds `~/.risc0/bin` to your shell profile), then through it the guest
   toolchain, `r0vm` 3.0.6 and `cargo-risczero` 3.0.6, pulls
   `risczero/risc0-groth16-prover:v2025-04-03.1`, and builds `lngap-r0`.

3. Self-test the whole pipeline (prove, wrap, verify):

       scripts/linux-selftest.sh

   It ends with `selftest: OK`-style output from `lngap-r0 verify` and
   writes `selftest.log`. **Send that log back**: it records the
   machine, the times and (with GNU `time`) the peak memory of each step.

## Wrapping a receipt made on the Mac

On the Mac (see below), `lngap-r0 prove <b> <c> succinct.bin` writes a
succinct receipt (about 220 KB). Then:

    # Mac -> Linux
    scp succinct.bin linux:ln-gap/crates/apps/sessions/r0/receipts/

    # on Linux
    scripts/wrap.sh receipts/succinct.bin receipts/groth16.bin

    # Linux -> Mac
    scp linux:ln-gap/crates/apps/sessions/r0/receipts/groth16.bin .

`wrap.sh` also writes `receipts/groth16.log`. The Groth16 receipt is a
few hundred bytes of seal plus the journal; `lngap-r0 show groth16.bin`
prints the image id, journal and seal.

Both sides must run the same guest: the receipt is verified against the
guest's image id, which changes with any change to the guest or to the
toolchain. Pull the branch on both machines before proving.

## On the Mac

Proving on the Mac works through `r0vm` (RISC Zero's prebuilt prover;
the host tool uses RISC Zero's client API, so nothing of RISC Zero's
needs compiling here, and Xcode's Metal compiler is not needed):

    curl -L https://risczero.com/install | bash      # rzup
    rzup install rust
    rzup install r0vm 3.0.6
    rzup install cargo-risczero 3.0.6
    cd crates/apps/sessions/r0 && cargo build --release
    ./target/release/lngap-r0 prove 9 42 succinct.bin   # ~7 s

`RISC0_DEV_MODE=1` makes fake receipts (instant, not proofs; `show`
labels them) for working on the guest.

## What the tool does

    lngap-r0 prove <b> <c> <out>   a succinct (STARK) receipt of the guest on (b, c)
    lngap-r0 wrap <in> <out>       the Groth16 receipt of a succinct receipt
    lngap-r0 verify <in>           verify against the guest's image id
    lngap-r0 show <in>             kind, image id, journal, seal
    lngap-r0 selftest              prove (9, 42), wrap, verify

The guest is a PLACEHOLDER for now: it commits `(b, c)` as its journal
and checks nothing. The withdrawal statement (a return note of `b` with
memo `c` in a final state) replaces it; the pipeline stays the same.

## If something goes wrong

- `docker returned failure exit code`: run the image by hand to see why,
  `docker run --rm risczero/risc0-groth16-prover:v2025-04-03.1`; out of
  memory is the usual cause (check `dmesg` for the OOM killer). Exit
  code 137 is the kernel's kill: on the Mac, under Colima's default VM
  (2 CPUs, 1.9 GB, the amd64 image emulated), the wrap died this way
  after 26 s. A larger VM (`colima start --memory 24 --cpu 8 --arch
  x86_64`, say) might do it there, slowly; x86 Linux is the plain route.
- `r0vm` version errors: the host tool and `r0vm` must both be 3.0.x;
  `rzup show` lists what's installed, `rzup default r0vm 3.0.6` selects.
- `image id mismatch` on verify: the two machines built different
  guests; check out the same commit on both and rebuild.
