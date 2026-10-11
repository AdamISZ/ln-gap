#!/usr/bin/env bash
# The whole withdrawal pipeline on x86 Linux, in one go:
#   scripts/linux-withdraw.sh [b] [c]       (default: b = 9, memo c = 42)
# 1. builds the guest reproducibly (scripts/build-guest.sh) into
#    guests/withdraw.bin, and rebuilds the host tool around it;
# 2. builds the toy L2 with Alice's return of b (memo c), checks the
#    statement natively and proves it (STARK);
# 3. wraps the proof in Groth16;
# 4. encodes it as the BitVMX verifier's input.
# Writes withdraw.log. Bring back guests/withdraw.bin (USB stick) and the
# log's last lines (the image id, the binary's SHA-256 and the input hex).
set -euo pipefail
cd "$(dirname "$0")/.."
b="${1:-9}"; c="${2:-42}"
export PATH="$HOME/.risc0/bin:$HOME/.cargo/bin:$PATH"
export RUST_LOG=${RUST_LOG:-info}
export RISC0_WORK_DIR=${RISC0_WORK_DIR:-$HOME/r0work}
mkdir -p "$RISC0_WORK_DIR" receipts
timed() { if [ -x /usr/bin/time ]; then /usr/bin/time -v "$@"; else "$@"; fi; }
{
    echo "== $(date -u) on $(uname -srm), $(nproc) cores, $(awk '/MemTotal/ {printf "%d GB", $2/1024/1024}' /proc/meminfo); commit $(git rev-parse --short HEAD)"
    scripts/build-guest.sh
    cargo build --release -p lngap-r0
    timed ./target/release/lngap-r0 withdraw-demo "$b" "$c" receipts/withdraw-succinct.bin
    timed ./target/release/lngap-r0 wrap receipts/withdraw-succinct.bin receipts/withdraw-groth16.bin
    ./target/release/lngap-r0 bitvmx-input receipts/withdraw-groth16.bin receipts/withdraw-input.hex
    echo
    echo "== to bring back"
    echo "guest binary: $(sha256sum guests/withdraw.bin)"
    ./target/release/lngap-r0 show receipts/withdraw-groth16.bin | grep -E 'image id|journal'
    echo "input: $(cat receipts/withdraw-input.hex)"
} 2>&1 | tee withdraw.log
