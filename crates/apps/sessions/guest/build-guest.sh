#!/bin/sh
# Build the statement program and copy the ELF beside the harness.
# Needs: rustup target add riscv32im-unknown-none-elf
set -e
cd "$(dirname "$0")"
cargo build --release
cp target/riscv32im-unknown-none-elf/release/lngap-sessions-guest ../programs/withdraw.elf
echo "programs/withdraw.elf: $(wc -c < ../programs/withdraw.elf) bytes"
