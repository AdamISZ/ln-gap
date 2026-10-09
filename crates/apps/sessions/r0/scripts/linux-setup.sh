#!/usr/bin/env bash
# Set up an x86_64 Linux machine to prove the sessions guest and wrap
# proofs in Groth16 (RISC Zero 3.0.6). See ../WRAP_ON_LINUX.md.
#
# Installs (user-level, no sudo): RISC Zero's rzup and, through it, the
# guest toolchain, r0vm 3.0.6 and cargo-risczero 3.0.6; pulls RISC Zero's
# Groth16 prover image; builds the host tool. Needs: Rust (rustup), Docker
# usable by this user, git, curl.
set -euo pipefail
cd "$(dirname "$0")/.."

R0_VERSION=3.0.6
IMAGE=risczero/risc0-groth16-prover:v2025-04-03.1

say() { printf '\n== %s\n' "$*"; }
die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }

say "checks"
[ "$(uname -s)" = Linux ] || die "this script is for Linux"
[ "$(uname -m)" = x86_64 ] || die "the Groth16 prover image is x86_64 only (this is $(uname -m))"
command -v cargo >/dev/null || die "no cargo: install Rust first, https://rustup.rs (then open a new shell)"
command -v docker >/dev/null || die "no docker: install Docker Engine, https://docs.docker.com/engine/install/"
docker info >/dev/null 2>&1 || die "docker is installed but this user can't reach the daemon (add yourself to the 'docker' group and log in again, or start the daemon)"
mem_gb=$(awk '/MemTotal/ {printf "%d", $2/1024/1024}' /proc/meminfo)
echo "memory: ${mem_gb} GB"
[ "$mem_gb" -ge 16 ] || echo "WARNING: under 16 GB; the Groth16 step may run out of memory"
df -h . | tail -1 | awk '{print "free disk here: " $4 " (the prover image and build need ~15 GB)"}'

say "rzup"
# the current rzup lives in ~/.risc0/bin; an older one elsewhere on PATH
# (e.g. ~/.cargo/bin/rzup) has a different command syntax, so use this one
# an rzup older than 0.5 (e.g. 0.2.x from an earlier install) has a
# different command syntax: reinstall over it
rzup_ok() {
    v=$("$HOME/.risc0/bin/rzup" --version 2>/dev/null | awk '{print $2}') || return 1
    [ "$(printf '%s\n0.5.0\n' "$v" | sort -V | head -1)" = 0.5.0 ]
}
if ! rzup_ok; then
    echo "installing the current rzup (RISC Zero's installer; it adds ~/.risc0/bin to your shell profile)"
    curl -sSfL https://risczero.com/install | bash
    rzup_ok || die "rzup is still older than 0.5 after reinstalling"
fi
export PATH="$HOME/.risc0/bin:$HOME/.cargo/bin:$PATH"
rzup() { "$HOME/.risc0/bin/rzup" "$@"; }
rzup --version
if other=$(which -a rzup 2>/dev/null | grep -v "^$HOME/.risc0/bin/rzup$" | head -1) && [ -n "$other" ]; then
    echo "note: another rzup at $other (older; ignored here, you may want to remove it)"
fi

say "RISC Zero components ($R0_VERSION)"
rzup install rust || true
rzup install r0vm "$R0_VERSION" || rzup default r0vm "$R0_VERSION"
rzup install cargo-risczero "$R0_VERSION" || rzup default cargo-risczero "$R0_VERSION"
rzup show
r0vm --version

say "the Groth16 prover image"
docker pull "$IMAGE"

say "building the host tool"
cargo build --release
ls -la target/release/lngap-r0

say "done"
echo "next: scripts/linux-selftest.sh"
