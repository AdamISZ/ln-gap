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

## Bisection claims (`lngap-contract::claim`, `::inner`, `::simple`, `lngap-script32`)

A claim is a program over `n_words ≤ 24` registers (D19): compression
steps and simple steps. The prover commits the end state in its Move with
a Winternitz signature over `4 n_words` bytes (4-bit digits; 1.4 KB witness
and 5 KB verifier for 8 words, 6 KB and 21 KB for 24). Off `C'_d` a
pre-signed chain lets the challenger bisect:

| Output | Leaf | Script | Witness after sigs | Timelock |
|---|---|---|---|---|
| `C'_d` | `dispute` | 2-of-2 | — | — |
| `D_0`, `R_r'` | `p_round_r` | 2-of-2-verify, `k−1` × Winternitz verify+drop, `OP_1` | the `k−1` state signatures | timeout leaf: Q after Δ |
| `R_r` | `q_round_r` | 2-of-2-verify, `log2 k` × `bit_decode OP_DROP`, `OP_1` | the index preimages | timeout: P after Δ |
| `R_R` | `q_round_R_check` | as `q_round_R` + `OP_NOP`: the simple-step variant, into the check chain | | |
| `S_0` / `C_0` | `p_re_cur` / `c_re_cur` | 2-of-2-verify, verify+drop the re-committed cur (+ 16 × 32-bit block words) | | timeout: Q |
| `S_0'` / `C_0'` | `p_re_next` / `c_re_next` | verify+drop the re-committed next | | timeout: Q |
| `S_1` | `p_sched` | 48 × 32-bit Winternitz verify+drop — 35.7 KB, 962 items | 48 signatures | timeout: Q |
| `S_2`, `S_3` | `p_inner_r` | 7 × Winternitz verify+drop | 7 state signatures | timeout: Q |
| `I_r` | `q_inner_r` | 3 × `bit_decode OP_DROP` | 3 preimages | timeout: P |
| `I_1` | `sched_<hash>` ×48 | `<Q> OP_CHECKSIGVERIFY`, verify the 4 inputs then `W[i]` (parked), tables, schedule step, "differs" | 5 word signatures | — |
| `I_1` | `block_<hash>` | block word `j` vs its constant, or a word of the verified re_cur | word (+ re_cur) signatures | — |
| `I_1`, `C_1` | `re_cur_mismatch_<src>`, `re_next_mismatch_<src>` | re-commitment vs the path's source (constant nibbles or a verified commitment) | 1–2 state signatures | — |
| `I_1` | `ckeep_<step>` | re_next ≠ re_cur outside `D` and the step's copy destinations | re_cur, re_next | — |
| `I_1` | `cpred_<step>` | verify block words 15..0 then re_cur (parked, restored: state deepest), predicates over the 320-nibble space | 16 words, re_cur | — |
| `I_1` | `ccopy_<step>` | copy destinations of re_next vs block nibbles | 16 words, re_next | — |
| `T` | `round_<hash>` (64 per init kind) | verify `W[r]`, `s_r`, (`init` for r = 63), `s_{r+1}`; tables; one SHA-256 round (+ feed-forward); "differs" | word and state signatures | — |
| `C_1` | `simple_<step>` | verify re_cur (parked) and re_next; per nibble `OP_PICK OP_PICK OP_EQUAL` against the expected copy; predicates; AND, NOT | re_cur, re_next | — |
| any | `timeout` | `<Δ> OP_CSV OP_DROP <X.payment> OP_CHECKSIG` | `sig_X` | CSV Δ |
| `R_R'` (flat claims) | `step_<hash>` | two Winternitz midstates, `sha256_u4` compression (368.7 KB), mismatch check | next then cur signatures | — |

Predicates in Script: `EqConst` and `EqNibbles` are one `OP_PICK … OP_EQUAL`
per nibble; `LeTarget` folds the 64 nibbles of `D` from the least
significant up as `acc' = (n < t) || (n == t && acc)`. Leaves are named by
a hash of their script and deduplicated.

### 32-bit word gadgets (`lngap-script32`)

Words are 8 nibbles, most significant deepest. Tables pushed by the leaf
(608 one-byte constants): `xor[16a+b]`, `and[16a+b]` (256 entries each,
entry 0 nearest the top) and for `s` in 1..3 `lo_s[x] = x >> s`,
`hi_s[x] = (x << (4−s)) & 15`. A lookup is `<depth> OP_ADD OP_PICK` with the
depth tracked at build time.

| Gadget | Method | Script |
|---|---|---|
| `a + b mod 2^32` | nibble adds LS-first with a carry (`OP_GREATERTHANOREQUAL`, `OP_SUB`) | 1,130 B |
| `a ^ b`, `a & b` | 8 table lookups | 1,167 / 1,159 B |
| `!a` | `15 − x` per nibble | 1,017 B |
| `rotr n`, `shr n` | nibble rotate by `n/4`, then per nibble `lo_s(x_j) + hi_s(x_{j−1})` | 1,129–1,141 B |
| SHA-256 round (`K[i]` constant, `W[i]` on the stack) | Σ1, Ch, Σ0, Maj, two adds, shift | 6,128 B |
| schedule step `W[i] = σ1(W[i−2]) + W[i−7] + σ0(W[i−15]) + W[i−16]` | | 3,252 B |
| "differs" (n nibbles) | n × (`OP_ROLL OP_ROLL OP_EQUAL OP_TOALTSTACK`), drop tables, `OP_BOOLAND` chain, `OP_NOT` | ~1 KB for n = 64 |

Every gadget is checked against its native counterpart on regtest and
exhaustively in the crate's mini-interpreter (`script32::sim`).

## Names (`lngap-names`), facts as inclusion proofs

Nothing in the names contracts is a hub statement: the hub's promise (an
anchor height and a proof shape) binds through its signature on the bond
that names it, and every fact about the registry is a bisection claim of
the phase-2b shape (D20, D22).

### `nreg:{params}` — bonded registration (hub locks the bond; depths 1–3)

| Depth | Prover | Leaf | Script |
|---|---|---|---|
| 1 | user | `move_1` (claim "not anchored") | `<h+2> OP_CLTV OP_DROP [CSV tsd] 2-of-2-verify, reveal(move 1b, state 2b, code 2b), OP_1` |
| 2 | hub | `move_2` (inclusion proof) | `2-of-2-verify, reveals, Winternitz end state (24 words: 6 KB witness, 21 KB verifier), OP_1`; `C'_2` carries the `dispute` leaf and the pre-signed dispute chain |
| 3 | user | `move_3` (heavier chain) | as `move_2` with the refutation claim's end state |
| any | `disprove_state_mismatch`, `disprove_code_mismatch` | the generic consistency checks (expected state = depth, code by depth) |
| any | `split_BondToUser` / `split_BondToHub` | CSV Δ(+Δ′) |
| `C` | `settle` | CLTV deadline: bond back to the hub |

### `anchorpay:{params}` — payment gated on an inclusion proof (depths 1–2)

| Depth | Prover | Leaf |
|---|---|---|
| 1 | the prover named in the params | `move_1` with the inclusion claim's end state |
| 2 | the other party | `move_2` with the heavier-chain claim's end state |
| | | `split_Paid` / `split_Refund`; `settle` at `h_sale`: refund |

### Anchor chain

Anchor = a fixed-layout transaction (`lngap_spv::chain::anchor_tx`): one
input spending the previous anchor's change output by key path; outputs
`OP_RETURN <69 zero bytes> <root> OP_0` and a P2TR change output; 208 bytes
with the root at byte 128, so the claim hashes it as four 64-byte blocks
and copies the root out of the third; predicates on the first chunk pin the
spent outpoint (bytes 5..41), the output count (byte 46 = 2) and output 0's
first script byte (byte 56 = `OP_RETURN`), so an anchor with a second
spendable output cannot be proven against. Users walk the chain from genesis
(`verify_anchor_chain`) before trusting a promise's tip; the auditor does the
same and recomputes the root of the published ledger as of each anchor.
