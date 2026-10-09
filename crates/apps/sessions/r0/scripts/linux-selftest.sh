#!/usr/bin/env bash
# The whole pipeline on this machine: prove the guest on (9, 42), wrap the
# proof in Groth16, verify it. Writes selftest.log (send it back) and
# receipts/selftest-groth16.bin.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.risc0/bin:$HOME/.cargo/bin:$PATH"
export RUST_LOG=${RUST_LOG:-info}
# peak memory via GNU time, if installed (Debian/Ubuntu: apt install time)
timed() { if [ -x /usr/bin/time ]; then /usr/bin/time -v "$@"; else "$@"; fi; }
mkdir -p receipts
{
    echo "== $(date -u) on $(uname -srm), $(nproc) cores, $(awk '/MemTotal/ {printf "%d GB", $2/1024/1024}' /proc/meminfo)"
    r0vm --version
    timed ./target/release/lngap-r0 prove 9 42 receipts/selftest-succinct.bin
    timed ./target/release/lngap-r0 wrap receipts/selftest-succinct.bin receipts/selftest-groth16.bin
    ./target/release/lngap-r0 verify receipts/selftest-groth16.bin
} 2>&1 | tee selftest.log
echo
echo "selftest.log written; the Groth16 receipt is receipts/selftest-groth16.bin"
