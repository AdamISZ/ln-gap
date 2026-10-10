#!/usr/bin/env bash
# A wallet's claim, proved on x86 Linux:
#   scripts/linux-claim.sh <withdraw-input.json> [out.hex]
# The JSON is what `lichen withdraw-input <memo>` prints: the return note,
# its path and the sequencer's signed root. Proves the canonical guest on
# it (STARK), wraps the proof in Groth16, and writes the BitVMX verifier's
# 172-byte input as hex: give it to `lichen dispute ... --input <out.hex>`.
set -euo pipefail
cd "$(dirname "$0")/.."
json="$(realpath "$1")"; out="${2:-claim.hex}"
export PATH="$HOME/.risc0/bin:$HOME/.cargo/bin:$PATH"
export RISC0_WORK_DIR=${RISC0_WORK_DIR:-$HOME/r0work}
mkdir -p "$RISC0_WORK_DIR"
cargo build --release -p lngap-r0
./target/release/lngap-r0 claim "$json" "$out"
cat "$out"; echo
