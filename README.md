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
  channel/    channel state machine, commitments, revocation, close paths
  contract/   Contract trait, contract-output taptree, pre-signed graph, disprove leaves,
              bisection claims (claim.rs: compression level; inner.rs: round level)
  script32/   32-bit word gadgets and a SHA-256 round / schedule step in Script, with a
              native mini-interpreter for debugging
  apps/       tictactoe, names (registry, anchor chain, bonded hub, sale),
              spv (header chain, OP_RETURN anchor, Merkle and ledger paths as a claim)
  party/      user/hub behaviour: off-chain negotiation, watch loop, statements
  harness/    scenario runner (`scenarios` binary), single- and two-channel worlds
docs/
  SCRIPTS.md      every leaf, witness layout, sizes
  SCENARIOS.md    every scenario with expected and observed outcomes
  DECISIONS.md    design decisions taken beyond the plan, and open TODOs
```

## Running

Requires `bitcoind` (v25+) on `PATH` (or `LNGAP_BITCOIND=/path/to/bitcoind`)
and a Rust toolchain.

```
cargo test                                          # everything: ~60 tests, ~1.5 min
cargo test -p lngap-harness --test p2_inner -- --nocapture   # bisection disputes with the
                                                    #   two-level search (p1_claims: flat)
cargo test -p lngap-harness --test p3_spv -- --nocapture     # SPV facts: headers, anchor,
                                                    #   Merkle and ledger paths; fork refutation
cargo run -p lngap-harness --bin scenarios          # the demo: all 18 scenarios,
                                                    #   narrative log, writes docs/SCENARIOS.md
cargo run -p lngap-harness --bin scenarios -- --keep T2   # one scenario, keep its
                                                    #   regtest datadir at ./regtest-data/T2/
```

To inspect a kept chain (pick a free RPC port if you run another regtest node):

```
bitcoind -regtest -datadir=regtest-data/T2 -txindex=1 -rpcport=18555 -listen=0 -daemon
bitcoin-cli -regtest -datadir=regtest-data/T2 -rpcport=18555 getrawtransaction <txid> 1
```

Every kept run is throwaway: `regtest-data/<scenario>/` is wiped at the start
of the next `--keep` run of that scenario (after stopping a node the explorer
script still has on it), and `SCENARIO.md` inside it always describes the
chain next to it. The same table goes into `docs/SCENARIOS.md`.

### Browsing a kept chain

```
tools/explorer.sh regtest-data/T2        # then open http://127.0.0.1:3002
```

This starts `bitcoind` on the datadir (RPC port 18555 by default, so it does
not clash with a regtest node on 18443) and
[btc-rpc-explorer](https://github.com/janoside/btc-rpc-explorer) on port 3002,
installed on first use under `tools/explorer/` (needs `node`; the install
skips native modules, which the explorer only uses for ZMQ). Paste a txid from
`SCENARIO.md`; the Scripts tab shows the witness elements (signatures, Lamport
preimages, leaf script, control block) as raw pushes. Ctrl-C stops both processes.

### Decoding a transaction

The explorer does not parse tapscript leaves. This does, and it knows the
LN-GAP gadgets:

```
cargo run -p lngap-harness --bin decode -- regtest-data/T2 <txid> [--rpcport 18555]
```

It prints the role of the transaction and of the output it spends (from the
datadir's `SCENARIO.md`), the leaf with `CSV`/`CLTV`, the 2-of-2, `bit_decode`
and `expect_bit` gadgets named, every witness element classified, and the
Lamport preimages resolved to the bits they commit to (e.g. `1101` = move 1,
state 1, code 01 for an attestation-gated payment). The node for that datadir
must be running, e.g. via `tools/explorer.sh`.

Every leaf test spends through the real interpreter: a throwaway regtest node
is started per test, the output is funded, and the spend is checked with
`testmempoolaccept` (negative cases) or mined (positive cases). Scenarios
never tell a party what to broadcast: the harness mines, delivers blocks,
relays messages, and injects the adversary's faults; every honest transaction
is a reaction of the party's own watch loop.

## What is demonstrated

| | Scenarios | On-chain path exercised |
|---|---|---|
| Channel | M1 tests, T7, c6 | funding, 10 updates, cooperative close, unilateral close with delay, penalty sweep including a contract output |
| Force-move | T2, T3, T8, T9, c2–c4 | Move chain up to depth 3, Settle after the deadline, Split after Δ / Δ+Δ' |
| Fraud proofs | T4, T5, T6, T6b, c5 | one-transaction disproofs: occupied cell, wrong board, wrong status, wrong code |
| Bonded hub | N2, N3, N6 | bond claimed with the hub's receipt; hub reclaims only by publishing the attestation |
| Sale | N4, N5, N7 | payment gated on an attestation; the buyer's leg reveals it, the seller copies it from the chain |
| Audit | N8 | omission and equivocation reported off-chain (not enforced: needs SPV in script) |
| Bisection claims | `p1_claims`, `p2_inner` tests | a 16-step SHA-256 chain disputed by bisection; two-level search ends in a one-round leaf (largest tx 12 kvB, whole dispute ~53 kvB) |
| SPV facts | `p3_spv` tests | a ledger entry anchored in a block of a valid regtest header chain, as a 128-step claim; a header that does not link or lacks proof of work, a wrong Merkle or ledger sibling are each disproved by one small leaf; a private fork is refuted by the heavier chain |

Sizes: a tic-tac-toe Move is ~2.3 KB of witness; disproofs are 0.3–2 KB;
the whole pre-signed graph from an empty board is 37 transactions per
commitment version. See `docs/SCRIPTS.md`.
