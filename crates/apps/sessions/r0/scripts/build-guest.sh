#!/usr/bin/env bash
# The canonical, reproducible build of the guest: inside RISC Zero's
# pinned builder image (x86 Docker), so the binary and its image id are
# the same on every machine. Writes guests/withdraw.bin and prints its
# image id and hash; commit the binary, and compare the image id with
# another machine's build of the same commit.
set -euo pipefail
cd "$(dirname "$0")/.."

die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
[ "$(uname -m)" = x86_64 ] || die "RISC Zero's guest builder image is x86_64 only"
docker info >/dev/null 2>&1 || die "docker is not usable by this user"
# the build must be of committed sources only
if [ -n "$(git status --porcelain -- methods/guest)" ]; then
    die "uncommitted changes under methods/guest: commit or stash them first"
fi
export PATH="$HOME/.risc0/bin:$HOME/.cargo/bin:$PATH"
# Docker reads the build files RISC Zero writes to a temporary directory;
# a snap-installed Docker can't see /tmp, so keep it under $HOME
export TMPDIR="${TMPDIR_GUEST:-$HOME/r0work/tmp}"
mkdir -p "$TMPDIR"
# export the build's output as a tar unpacked as this user (see shim/docker)
LNGAP_REAL_DOCKER="$(command -v docker)"
export LNGAP_REAL_DOCKER
export PATH="$PWD/scripts/shim:$PATH"

echo "== building the guest at $(git rev-parse --short HEAD) in RISC Zero's builder image"
LNGAP_GUEST_DOCKER=1 cargo run --release -p lngap-r0-methods --bin export-guest -- guests/withdraw.bin
sha256sum guests/withdraw.bin
echo
echo "now: bring guests/withdraw.bin back (it is to be committed), and note the image id above"
