#!/usr/bin/env bash
# Wrap a succinct receipt (made on the Mac with `lngap-r0 prove`) in
# Groth16:   scripts/wrap.sh <succinct.bin> <groth16.bin>
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: $0 <succinct.bin> <groth16.bin>" >&2; exit 2; }
cd "$(dirname "$0")/.."
export PATH="$HOME/.risc0/bin:$HOME/.cargo/bin:$PATH"
export RUST_LOG=${RUST_LOG:-info}
# peak memory via GNU time, if installed (Debian/Ubuntu: apt install time)
timed() { if [ -x /usr/bin/time ]; then /usr/bin/time -v "$@"; else "$@"; fi; }
in=$(realpath "$1"); out=$(realpath -m "$2")
timed ./target/release/lngap-r0 wrap "$in" "$out" 2>&1 | tee "${out%.bin}.log"
