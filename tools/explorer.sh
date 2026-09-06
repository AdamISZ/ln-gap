#!/usr/bin/env bash
# Open a kept LN-GAP regtest chain in a browser explorer.
#
#   cargo run -p lngap-harness --bin scenarios -- --keep T4
#   tools/explorer.sh regtest-data/T4-<...>        # then browse http://127.0.0.1:3002
#
# Starts bitcoind on the datadir (RPC port $RPC_PORT, default 18555, so it
# does not clash with a regtest node on 18443) and btc-rpc-explorer on
# $EXPLORER_PORT (default 3002). Ctrl-C stops both. The scenario's txids and
# their roles are in <datadir>/SCENARIO.md.
set -euo pipefail
DATADIR="${1:?usage: tools/explorer.sh <regtest-data/dir>}"
RPC_PORT="${RPC_PORT:-18555}"
EXPLORER_PORT="${EXPLORER_PORT:-3002}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CLI="$HERE/explorer/node_modules/btc-rpc-explorer/bin/cli.js"
if [ ! -f "$CLI" ]; then
  echo "installing btc-rpc-explorer (once) ..."
  (cd "$HERE/explorer" && npm install --ignore-scripts >/dev/null)
fi
DATADIR="$(cd "$DATADIR" && pwd)"
port_busy() { lsof -nP -iTCP:"$1" -sTCP:LISTEN >/dev/null 2>&1; }
if ! bitcoin-cli -regtest -datadir="$DATADIR" -rpcport="$RPC_PORT" getblockcount >/dev/null 2>&1; then
  # a node from an earlier run (other datadir) may still hold the port: pick a free one
  while port_busy "$RPC_PORT" || port_busy $((RPC_PORT + 1)); do
    echo "port $RPC_PORT is busy (another bitcoind?), trying $((RPC_PORT + 2))"
    RPC_PORT=$((RPC_PORT + 2))
  done
  bitcoind -regtest -datadir="$DATADIR" -txindex=1 -rpcport="$RPC_PORT" -port=$((RPC_PORT + 1)) -listen=0 -daemon >/dev/null
  for _ in $(seq 1 60); do
    sleep 1
    bitcoin-cli -regtest -datadir="$DATADIR" -rpcport="$RPC_PORT" getblockcount >/dev/null 2>&1 && break
  done
fi
echo "bitcoind: height $(bitcoin-cli -regtest -datadir="$DATADIR" -rpcport="$RPC_PORT" getblockcount) on rpcport $RPC_PORT"
[ -f "$DATADIR/SCENARIO.md" ] && echo "scenario report: $DATADIR/SCENARIO.md"
# stop the node we started (or found) when the explorer exits for any reason
trap 'echo; echo "stopping bitcoind on $RPC_PORT"; bitcoin-cli -regtest -datadir="$DATADIR" -rpcport="$RPC_PORT" stop >/dev/null 2>&1 || true' EXIT
while port_busy "$EXPLORER_PORT"; do
  echo "port $EXPLORER_PORT is busy (an explorer still running?), trying $((EXPLORER_PORT + 1))"
  EXPLORER_PORT=$((EXPLORER_PORT + 1))
done
echo "explorer: http://127.0.0.1:$EXPLORER_PORT  (Ctrl-C stops the explorer and this bitcoind)"
BTCEXP_HOST=127.0.0.1 BTCEXP_PORT="$EXPLORER_PORT" \
BTCEXP_BITCOIND_HOST=127.0.0.1 BTCEXP_BITCOIND_PORT="$RPC_PORT" \
BTCEXP_BITCOIND_COOKIE="$DATADIR/regtest/.cookie" \
BTCEXP_PRIVACY_MODE=true BTCEXP_NO_RATES=true BTCEXP_SLOW_DEVICE_MODE=true BTCEXP_NO_INMEMORY_RPC_CACHE=true \
node "$CLI" &
NODE=$!
trap 'kill "$NODE" 2>/dev/null' INT TERM
wait "$NODE" || true
