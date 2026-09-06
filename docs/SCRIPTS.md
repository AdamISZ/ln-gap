# Leaves, witness layouts, sizes

Sizes measured on regtest by the tests (script bytes exclude the control block;
control block = 33 + 32·depth). Witness convention: elements listed here in
*consumption order* (first listed is on top of the stack).

## Primitive fragments (`lngap-btc::script`)

| Fragment | Script | Witness | Size |
|---|---|---|---|
| `two_of_two(A,B)` | `<A> OP_CHECKSIG <B> OP_CHECKSIGADD 2 OP_NUMEQUAL` | `sig_A, sig_B` | 70 B |
| `cltv(h)` | `<h> OP_CLTV OP_DROP` | — | 4–6 B |
| `csv(n)` | `<n> OP_CSV OP_DROP` | — | 3–4 B |
| `checksig(K)` | `<K> OP_CHECKSIG` | `sig_K` | 34 B |

## Lamport gadgets (`lngap-lamport::gadgets`)

| Gadget | Script | Witness | Size |
|---|---|---|---|
| `bit_decode(h0,h1)` | `OP_HASH160 OP_DUP <h1> OP_EQUAL OP_IF OP_DROP 1 OP_ELSE <h0> OP_EQUALVERIFY 0 OP_ENDIF` | `p` | 51 B, leaves bit |
| `expect_bit(h)` | `OP_HASH160 <h> OP_EQUALVERIFY` | `p` | 23 B |
| `decode_uint(pk, n)` | `0` then per bit msb-first: `OP_DUP OP_ADD OP_SWAP bit_decode OP_ADD` | `p_{n-1} … p_0` | 1 + 55·n B, leaves number |
| `expect_uint(pk, v)` | `expect_bit` × n, msb first | `p_{n-1} … p_0` | 23·n B |
| `equivocation(h0,h1)` | `OP_HASH160 <h1> OP_EQUALVERIFY OP_HASH160 <h0> OP_EQUALVERIFY` | `p1, p0` | 46 B |

Preimages are 20 bytes; a witness element per bit costs 21 bytes.

### M0 deliverable

Leaf `decode_uint(8) 100 OP_GREATERTHAN`: script 452 B; spend witness 658 B
(8 × 21 + script + 33-byte control block). Confirmed on regtest, txid
`14f36963103f84cf6dc994eb174241dda4ef18deafd126ca0cdd5ce12f828af5` (throwaway
chain; reproduce with `cargo test -p lngap-lamport -- --nocapture`).

## Channel leaves (`lngap-channel`)

Every revocable output of `X`'s commitment carries the same `revoke` leaf.

| Output | Leaf | Script | Witness (consumption order) | Timelock |
|---|---|---|---|---|
| funding | `funding` | `<U.funding> OP_CHECKSIG <H.funding> OP_CHECKSIGADD 2 OP_NUMEQUAL` | `sig_U, sig_H` | — |
| `to_local` (X's) | `revoke` | `OP_HASH160 <rev_hash_X> OP_EQUALVERIFY <Y.payment> OP_CHECKSIG` | `secret_X, sig_Y` | — |
| `to_local` (X's) | `delayed` | `<to_self_delay> OP_CSV OP_DROP <X.delayed> OP_CHECKSIG` | `sig_X` | CSV 6 |
| `to_remote` (Y's) | `claim` | `<Y.payment> OP_CHECKSIG` | `sig_Y` | — |
| contract `C_i` | `revoke` | as above | as above | — |

Commitment fee (1000 sat) comes out of the broadcaster's `to_local`. Sweeps
(penalty, claims) pay 1000 sat and go to the sweeper's payout script, a
single-leaf `<payout> OP_CHECKSIG` taproot output.

## Contract output leaves (`lngap-contract`)

`C` is the contract output on the commitment (depth 0); `C'_d` is the output
of `Move_d`. `P` is the prover at depth `d`, `Q` the challenger. All 2-of-2
fragments are `<U.payment> OP_CHECKSIG <H.payment> OP_CHECKSIGADD 2 OP_NUMEQUAL(VERIFY)`
with witness `sig_U, sig_H`.

| Output | Leaf | Script | Witness after sigs | Timelock |
|---|---|---|---|---|
| `C` | `revoke` | channel revocation leaf | `secret, sig_Q` (no sigs pair) | — |
| `C` | `settle` | `<deadline> OP_CLTV OP_DROP <tsd> OP_CSV OP_DROP 2-of-2` | — | CLTV deadline + CSV 6 (D1) |
| `C` | `move_1` | `[<tsd> OP_CSV OP_DROP if P broadcast] 2-of-2-verify, then per bit of P's move, new state, code: bit_decode OP_DROP; OP_1` | P's reveals: move, state, code (each msb first) | CSV 6 only on the broadcaster's own Move |
| `C'_d` | `disprove_<check>` | `<Q.payment> OP_CHECKSIGVERIFY <body>` — see per-contract tables | `sig_Q`, then the reveal slices the body declares, in order | — |
| `C'_d` | `move_{d+1}` | as `move_1` with Q's depth-(d+1) keys, no CSV | Q's reveals | — |
| `C'_d` | `split_X` | `<Δ[+Δ']> OP_CSV OP_DROP 2-of-2-verify expect_uint(P's code key, X) OP_1` | P's code reveal (copied from `Move_d`) | CSV Δ = 6, +Δ' = 6 if X favours P |

Values: `C` holds `V`; `C'_d` holds `V − d·fee`; Settle pays `R(s)` of `V − fee`;
`Split_X` off `C'_d` pays `dist(X)` of `V − (d+1)·fee`. Fee = 1000 sat.

### Disprove leaf bodies: the two-phase convention

A body first declares its inputs (`prior_uint`, `mv_uint`, `new_uint`,
`code_uint`), each decoded and parked on the altstack, then restores them in
declaration order (`OP_FROMALTSTACK` × n, then `<i> OP_ROLL` for i in 1..n)
and computes. At depth 1 the prior state is a constant (`push_int`) and a
leaf that reads only prior fields is dropped if it can never fire.

### Coin flip (`lngap-contract::toy`), 4-bit state, 1-bit move

| Leaf | Inputs | Body | Script (d=1 / d=2) |
|---|---|---|---|
| `not_on_turn` (user) | prior u_rev | value itself | dropped at d=1 / 94 B |
| `not_on_turn` (hub) | prior u_rev, h_rev | `OP_SWAP OP_NOT OP_BOOLOR` | — / ~150 B |
| `state_mismatch` | prior(4), move, new(4) | `TOALT IF <bitval> ELSE 0 ENDIF ADD <flag> ADD FROMALT NUMNOTEQUAL` | 338 B / ~560 B |
| `code_mismatch` | new bits ×4, code | `TOALT SWAP IF NUMNOTEQUAL NIP ELSE 2DROP NOT ENDIF FROMALT NUMNOTEQUAL` | 404 B |

Move leaf: 442 B script, witness 7 × 21 B of preimages + 2 × 64 B sigs.
Graph for M = 2: 7 pre-signed transactions per commitment version.

### Tic-tac-toe (`lngap-tictactoe`), 21-bit state, 4-bit move

| Leaf | Inputs | Check | Script (d=1 / d≥2) | Disproof witness |
|---|---|---|---|---|
| `prior_closed` | prior status | `!= 0` | dropped / 149 B | 452 B |
| `not_on_turn` | prior turn | `== other` | dropped / 94 B | 344 B |
| `cell_out_of_range` | move | `> 8` | 263 B | 578–610 B |
| `cell_occupied_i` ×9 | move, prior cell i | `mv == i && cell != 0` | 271 / 383 B | 586–772 B |
| `board_mismatch_i` ×9 | prior cell i, move, new cell i | `new != (mv == i ? mark : prior)` | 392 / 504 B | 749–935 B |
| `turn_not_flipped` | prior turn, new turn | `==` | 99 / 155 B | 381–458 B |
| `status_mismatch` | new status, new cells ×9 | 8 win lines via `OP_PICK`, full-board, expected vs claimed | 1379 B | 2030–2062 B |
| `code_mismatch` | new turn, new status, code | `status ? status−1 : !turn` vs code | 340 B | 708 B |

`move_d` leaf: 1505 B script (27 bits × ~52 B + 2-of-2); Move witness ≈ 27 × 21 + 128 + script + control block ≈ 2.3 KB.
`C'_1`: 26 leaves, 9.9 KB of script; `C'_2`: 28 leaves, 12.2 KB (control blocks 161–193 B).
Graph from the empty board (M = 9): 37 pre-signed transactions per commitment version.
