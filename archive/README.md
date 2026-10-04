# Archive

Crates from earlier iterations of the design, kept for reference. They are
still workspace members, so they build and their tests run, but nothing in
the current design depends on them except as noted.

| crate | what it was |
|---|---|
| `party` | the first party layer: claim queues and bisection disputes over Bitcoin SPV data |
| `spv` | disputes over Bitcoin SPV step kinds, on regtest data |
| `names` | a names registry settled by bilateral contracts against inclusion proofs (`chess-fc` still borrows one type from it) |
| `names-fc` | the same registry over the proof-of-work fact chain |
| `tictactoe-fc` | tic-tac-toe played on the proof-of-work fact chain |

The harness's older suites (`fc_*`, `m2`–`m4`, `p1`–`p3`) exercise these.
The current design (the proof-of-stake venue, its dispute graph and the
demos) lives under `crates/`; see the repository map in the top-level
README.
