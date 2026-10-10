#!/bin/sh
# Create upstream/bitvmx-cpu/BitVMX-CPU: BitVMX-CPU at 299009c with the
# patches in third_party/bitvmx-cpu applied (the workspace builds it from
# there). Idempotent: an existing tree with the patches is left alone.
set -e
cd "$(dirname "$0")/.."
DIR=upstream/bitvmx-cpu/BitVMX-CPU
BASE=299009c65e635327025ee13ffe1e1f1671bd0615
if [ ! -d "$DIR/.git" ]; then
  mkdir -p upstream/bitvmx-cpu
  git clone https://github.com/FairgateLabs/BitVMX-CPU.git "$DIR"
fi
cd "$DIR"
want=$(ls ../../../third_party/bitvmx-cpu/*.patch | wc -l | tr -d ' ')
have=$(git rev-list --count "$BASE"..HEAD 2>/dev/null || echo 0)
if [ "$have" = "$want" ]; then
  echo "BitVMX-CPU: $BASE with $have patches, as wanted"
  exit 0
fi
git checkout -q -B lngap "$BASE"
git -c user.name=lngap -c user.email=lngap@localhost am -q ../../../third_party/bitvmx-cpu/*.patch
echo "BitVMX-CPU: $BASE with $want patches applied"
