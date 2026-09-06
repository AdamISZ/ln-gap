# LN-GAP — Lightning Network Governed by Arbitrary Programs

Proof of concept: Lightning-style channels whose commitment transactions carry
*contract outputs* decided by arbitrary programs, enforced on-chain only under
dispute with pre-signed transactions, Lamport bit commitments and plain
Tapscript. No soft fork, no trusted party, no dispute VM.

Runs against a regtest `bitcoind`. Two demonstrations: tic-tac-toe, then a
bonded name registry.

## Layout

```
crates/
  btc/        keys, taproot trees, sighash, tx building, witness, regtest wrapper
  lamport/    one-time bit commitments, Script gadgets, per-party key store
  channel/    (M1) channel state machine, commitments, revocation, close paths
  contract/   (M2) Contract trait, contract-output taptree, pre-signed graph
  apps/       (M3, M4) tictactoe, names
  party/      (M2+) user/hub behaviour and watch loop
  harness/    (M3+) scenario runner
docs/
  SCRIPTS.md      every leaf, witness layout, sizes
  SCENARIOS.md    every scenario with expected and observed outcomes
  DECISIONS.md    design decisions taken beyond the plan, and open TODOs
```

## Running

Requires `bitcoind` (v25+) on `PATH` (or `LNGAP_BITCOIND=/path/to/bitcoind`)
and a Rust toolchain.

```
cargo test                      # unit tests + regtest-backed leaf tests
LNGAP_KEEP_DATADIR=1 cargo test # keep the regtest datadirs under ./regtest-data
```

Every leaf test spends through the real interpreter: a throwaway regtest node
is started per test, the output is funded, and the spend is checked with
`testmempoolaccept` (negative cases) or mined (positive cases).
