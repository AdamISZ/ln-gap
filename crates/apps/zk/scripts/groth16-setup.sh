#!/usr/bin/env bash
# Assemble the directory that the Groth16 runs of lngap-zk read
# (ZK_GROTH16_DIR): BitVMX's Groth16 verifier ELF, patched to the RISC Zero
# parameters of a sample proof, the proof encoded as the verifier's input,
# and the two program definitions. See ../GROTH16.md for what each step is
# and why.
#
#     crates/apps/zk/scripts/groth16-setup.sh [OUT_DIR]      (default: ./groth16)
#
# Needs: git, python3, a Rust toolchain, network access (GitHub, crates.io).
# Nothing GPL is downloaded or distributed by this repository: the verifier
# ELF is copied from your own Cargo checkout of BitVMX-CPU, and patched
# locally.

set -euo pipefail

OUT="${1:-groth16}"
REPO_ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"

# BitVMX-CPU, as pinned by crates/apps/zk/Cargo.toml (rev 299009c6…)
BITVMX_SHORT_REV="299009c"
ELF_REL="docker-riscv32/verifier/build/zkverifier-new-mul.elf"
ELF_SHA256="2b96e192300ab938b918a860b5bdf5f72a066e0e4688fdf7efc32228d6915598"
PATCHED_SHA256="f2cab152d95006e8adfee6c0587cd367c38b4f79f0261426b1dfb08f3e88e1a8"

# FairgateLabs/rust-bitvmx-zk-proof (Apache-2.0): the sample proof and the tool
# that encodes it
ZKP_REPO="https://github.com/FairgateLabs/rust-bitvmx-zk-proof"
ZKP_COMMIT="4d0d149c7dc50d4e54e468c945a8afb4c9fc2ad2"

# The input this produces; it ran the dispute in the paper
INPUT_EXPECTED="010000006362fbd71058c3a524356bceda7543ed7bd2fad51f3a943403d5434a31606b548e4deda855b2c0b5db4ce319fd8acc893a7090e55486fcb06a0c641e3b59fd9868132cb254d3b6521bf49d7f76663cf0670b9237f48974fa6e6e4c77bcb2d826753e071aa80b8b2446721a221d65afc50de871abe632e7008c57dd9c3c80520d131e780aa59b066ce310ff2d357e1765e3dbc2f05e6481d8b880956d8b06a90301000000"

say() { printf '\n==> %s\n' "$*"; }
sha256() { python3 -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"; }

mkdir -p "$OUT"
OUT="$(cd "$OUT" && pwd)"
WORK="$OUT/.work"
mkdir -p "$WORK"

say "1/6  fetching the workspace's git dependencies (BitVMX-CPU among them)"
(cd "$REPO_ROOT" && cargo fetch --quiet)

say "2/6  locating the verifier ELF in your Cargo checkout of BitVMX-CPU"
ELF=""
for d in "$CARGO_HOME"/git/checkouts/bitvmx-cpu-*/"$BITVMX_SHORT_REV"*; do
    if [ -f "$d/$ELF_REL" ]; then ELF="$d/$ELF_REL"; break; fi
done
[ -n "$ELF" ] || { echo "not found: $CARGO_HOME/git/checkouts/bitvmx-cpu-*/$BITVMX_SHORT_REV*/$ELF_REL" >&2; exit 1; }
[ "$(sha256 "$ELF")" = "$ELF_SHA256" ] || { echo "unexpected ELF (hash mismatch): $ELF" >&2; exit 1; }
echo "    $ELF"

say "3/6  fetching the sample proof and building its encoder (a few minutes the first time)"
if [ ! -d "$WORK/zkp/.git" ]; then
    git clone --quiet "$ZKP_REPO" "$WORK/zkp"
fi
git -C "$WORK/zkp" fetch --quiet origin "$ZKP_COMMIT" 2>/dev/null || true
git -C "$WORK/zkp" checkout --quiet "$ZKP_COMMIT"
(cd "$WORK/zkp" && cargo build --quiet --release -p verifier)
VERIFIER="$WORK/zkp/target/release/verifier"

say "4/6  encoding the proof as the verifier program's input"
python3 - "$WORK/zkp" "$WORK" <<'EOF'
import json, struct, sys
zkp, work = sys.argv[1], sys.argv[2]
# the image id: eight u32 words, little-endian
words = json.load(open(f"{zkp}/image_id.json"))
open(f"{work}/image_id.hex", "w").write(b"".join(struct.pack("<I", w) for w in words).hex())
# the Groth16 seal, wrapped as the encoder expects; the guest's journal is 1
seal = json.load(open(f"{zkp}/snark-seal.json"))
json.dump({"type": "ProveResult", "data": {"seal": seal, "journal": [1, 0, 0, 0], "status": "ok"}}, open(f"{work}/proof.json", "w"))
EOF
"$VERIFIER" proof-as-input -i "$WORK/image_id.hex" -p "$WORK/proof.json" | sed -e 's/^input: //' > "$OUT/input.hex"
[ "$(tr -d '[:space:]' < "$OUT/input.hex")" = "$INPUT_EXPECTED" ] || { echo "the encoded input differs from the expected one" >&2; exit 1; }

say "5/6  patching the ELF's public inputs to the proof's RISC Zero parameters"
cp "$ELF" "$OUT/zkverifier.elf"
chmod u+w "$OUT/zkverifier.elf"
python3 - "$OUT/zkverifier.elf" <<'EOF'
import sys
p = sys.argv[1]
b = bytearray(open(p, "rb").read())
base = 716804   # the verifier's public-input table
patch = {
    0:   "a516a057c9fbf5629106300934d48e0e",                                   # control root, first half
    32:  "775d4230e41e503347cad96fcbde7e2e",                                   # control root, second half
    128: "51b54a62f2aa599aef768744c95de8c7d89bf716e11b1179f05d6cf0bcfeb60e",   # BN254 control id
}
for off, h in patch.items():
    v = bytes.fromhex(h)
    b[base + off:base + off + len(v)] = v
open(p, "wb").write(b)
EOF
[ "$(sha256 "$OUT/zkverifier.elf")" = "$PATCHED_SHA256" ] || { echo "the patched ELF's hash is unexpected" >&2; exit 1; }

say "6/6  writing the program definitions"
for n in 8 2; do
    f="$OUT/groth16.yaml"; [ "$n" = 2 ] && f="$OUT/groth16-binary.yaml"
    cat > "$f" <<EOF
elf: zkverifier.elf
nary_search: $n
max_steps: 536870912
input_section_name: .input
inputs:
  - size: 168
    owner: prover
EOF
done

cat <<EOF

Done: $OUT
  zkverifier.elf        the patched verifier (GPL-3.0: keep it to yourself, don't commit it)
  input.hex             the sample proof, encoded
  groth16.yaml          8-ary search (the narrated demo, most tests)
  groth16-binary.yaml   binary search (the game played through the dispute graph)

Try:
  cargo run --release -p lngap-zk --bin lngap-zk-demo -- groth16 $OUT honest
  ZK_GROTH16_DIR=$OUT cargo test --release -p lngap-zk --test zk_graph groth16_on_regtest -- --ignored --nocapture
EOF
