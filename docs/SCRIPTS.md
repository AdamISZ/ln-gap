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
