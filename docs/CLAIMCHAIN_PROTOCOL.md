# ClaimChain Protocol — PoC Measurement Report

Branch: `factchain-poc`

## 1. What this validates

The PoC tests whether dispute proofs for a custom PoW fact chain are
small enough to be practical in real Bitcoin transactions, with
realistic chain lengths (W >= 10, preferably W = 100), without
cheating.

The fact chain replaces Bitcoin SPV: instead of proving inclusion by
verifying Bitcoin headers, an anchor transaction, and a block Merkle
path, the root is carried directly in the fact chain's own 48-byte
header. The proof is a chain of n4bit hash compressions from a
checkpoint to the target header.

The dispute path uses bisection in plain Tapscript: the prover commits
to intermediate states, the challenger narrows to one step, and a
terminal leaf recomputes that step on-chain. No soft fork, no trusted
party.

## 2. Scenarios (N1-N8)

All 8 scenarios pass on regtest:

  cargo test -p lngap-harness --test fc_names

| scenario | what it tests | result |
|----------|--------------|--------|
| N1 | Cooperative registration | no channel tx on-chain; both bonds folded |
| N2 | Hub doesn't submit to fact chain; Alice claims after h_max+GRACE | move_1, split_1_BondToUser; Alice +40k |
| N3 | Alice falsely claims not anchored; hub proves inclusion on-chain | move_1, split_1_BondToHub |
| N4 | Cooperative sale (Alice to Bob) | no channel tx; Bob -40k, Alice +40k |
| N5 | Sale; Alice never signs transfer | nothing opens; balances unchanged |
| N6 | Sale; hub refuses to submit transfer | Bob refunded; Alice keeps name |
| N7 | Sale; hub proves inclusion in leg 1, refuses to pay Alice | Bob's leg resolves; registry shows transfer |
| N8 | Hub fabricates inclusion proof; Alice disproves by bisection | bisection disproof at terminal leaf; bond to Alice |

N8 is the key stage-2 scenario: the hub cheats by altering the claimed
end state of its inclusion proof. Alice disputes, the bisection
protocol runs through 3 level-1 rounds (k=2), narrows to the isolated
step, and disproves it at a flat terminal leaf. The full dispute
transaction chain executes on regtest:

    commitment_2, claim_to_remote, claim_to_local, move_1 (hub's proof),
    d1/dispute (Alice disputes), p_round_1, q_round_1, p_round_2,
    q_round_2, p_round_3, q_round_3_check, c_re_cur, c_re_next,
    simple_nop (disproof)

Alice's balance after N8: 128,000 sat (100k funding + 40k bond - ~12k
fees).

## 3. Dispute chain measurement

  cargo test -p lngap-harness --test fc_stage2_measure -- --nocapture

### 3.1 Scaling table

| kind    | W   | steps | rounds | script (B) | witness (B) | fee (sat) | txs | build (ms) |
|---------|-----|-------|--------|------------|-------------|-----------|-----|------------|
| n4bit   | 1   | 8     | 3      | 41,637     | 22          | 22,000    | 22  | 32         |
| SHA-256 | 1   | 4     | 2      | 204,342    | 15          | 19,803    | 15  | 165        |
| n4bit   | 10  | 128   | 7      | 55,121     | 30          | 30,000    | 30  | 53         |
| SHA-256 | 10  | 64    | 6      | 262,514    | 23          | 27,803    | 23  | 254        |
| n4bit   | 100 | 1024  | 10     | 65,234     | 36          | 36,000    | 36  | 118        |
| SHA-256 | 100 | 512   | 9      | 306,143    | 29          | 33,803    | 29  | 779        |

### 3.2 n4bit vs SHA-256 ratios (SHA-256 / n4bit)

| W   | script  | witness | fee  | tx   | build |
|-----|---------|---------|------|------|-------|
| 1   | 4.9x    | 0.7x    | 0.9x | 0.7x | 5.2x  |
| 10  | 4.8x    | 0.8x    | 0.9x | 0.8x | 4.8x  |
| 100 | 4.7x    | 0.8x    | 0.9x | 0.8x | 6.6x  |

### 3.3 Per-round Script leaf

| metric              | n4bit   | SHA-256  | ratio   |
|---------------------|---------|----------|---------|
| per-round leaf size | 1,041 B | ~12,000 B| 11.5x smaller |
| stack elements      | 61      | ~672     | 11x fewer |

### 3.4 Key findings

1. **Script size: n4bit is 4.7-4.9x smaller** across all W values. At
   W=100, n4bit uses 65 KB of script vs 306 KB for SHA-256.

2. **Build time: n4bit is 4.8-6.6x faster** because the round leaf is
   smaller and the Script construction is simpler (16-entry S-box table
   vs 608-element XOR/AND/shift tables).

3. **Both scale logarithmically.** Bisection means the transaction
   count grows as O(log W), not O(W). n4bit goes 22 -> 30 -> 36 txs
   (W=1 -> 10 -> 100); SHA-256 goes 15 -> 23 -> 29.

4. **Script grows sub-linearly.** n4bit script: 42 KB -> 55 KB -> 65 KB
   (1.57x from W=1 to W=100). The growth is dominated by the
   level-1 round transactions (which carry WOTS commitments that don't
   shrink with the hash function), not the terminal leaf.

5. **Fee and witness counts are slightly worse for n4bit** because n4bit
   has more steps (7/header vs 4/header) and thus more bisection
   rounds. In a real fee market where cost scales with script/witness
   size, n4bit would be significantly cheaper: 65 KB vs 306 KB of
   script means far less block space consumed.

6. **The per-round leaf ratio (11.5x) is higher than the total-chain
   ratio (4.9x)** because WOTS commitment overhead doesn't shrink. Each
   p_round leaf verifies k-1 WOTS commitments regardless of hash kind.
   The hash function only affects the terminal round leaf, which is one
   transaction out of the chain.

## 4. Architecture

### 4.1 Crates

| crate | role |
|-------|------|
| lngap-n4bit | 4-bit SPN sponge hash (native + Script), cryptanalysis |
| lngap-factchain | 48-byte header, miner, ChainClient, FactChainShape claim builder |
| lngap-names-fc | NRegFc + AnchorPayFc contract programs (fact-chain backed) |
| lngap-harness | FcWorld: two channels, fact-chain miner, 8 scenarios |
| lngap-contract | ClaimSpec, bisection protocol, dispute graph, inner chain |
| lngap-party | dispute watch loop, on-chain reaction, broadcast |

### 4.2 n4bit hash

- 4-bit S-box (PRESENT's, ISO/IEC 29192-2)
- ADD key mixing (mod 16) — native to Bitcoin Script's OP_ADD
- Feistel ADD mixing on nibble pairs (required for avalanche)
- ShiftRows + column rotation + cross-boundary swap permutation
- Sponge: 40-nibble state, 20-nibble rate, 20-nibble capacity
- 20 rounds per absorb, 160-bit (20-byte) digest
- 48-byte header = 1 compression (within the 55-byte single-compression
  boundary for a 10-byte-rate sponge)

### 4.3 ClaimSpec for fact-chain headers

Each 48-byte header = 96 nibbles. Using 2 words (16 nibbles) per step:
6 absorb steps + 1 padding = 7 compression steps per header. Padded to
next power of 2 for k=2 bisection.

| W   | steps (pre-pad) | steps (padded) | bisection rounds |
|-----|-----------------|----------------|-----------------|
| 1   | 7               | 8              | 3               |
| 10  | 70              | 128            | 7               |
| 100 | 700             | 1024           | 10              |

## 5. Known limitations (not blocking PoC validation)

1. **Sponge capacity**: 80-bit capacity gives 2^40 collision resistance,
   not the 2^80 target. Fix: increase state to 60+ nibbles. The
   architecture is hash-agnostic; the hash is a swappable component.

2. **Diffusion**: full diffusion takes 41 rounds but only 20 are applied.
   The permutation has trapping. Fix: improve the permutation. The
   S-box itself is optimal (PRESENT's).

3. **Symmetric bonds**: stakes are [0, BOND] — Alice risks nothing by
   claiming falsely. Fix: stakes [BOND, BOND]. State machine unchanged.

4. **Variable-length claims**: n_headers is fixed at 1 in the contract
   program. The full design would adapt to the actual confirmed height.

5. **N8 disproof at NOP step**: the current cheat (flipping the end
   state) causes the bisection to narrow to a NOP padding step, not a
   real n4bit compression. A cheat that corrupts a compression midstate
   would trigger the inner chain (re-commit -> n4bit round leaf), which
   is a stronger test. The infrastructure supports it; only the test
   setup needs adjustment.

## 6. How to reproduce

```
# All 8 scenarios
cargo test -p lngap-harness --test fc_names

# Measurement table
cargo test -p lngap-harness --test fc_stage2_measure -- --nocapture

# n4bit unit tests + cryptanalysis
cargo test -p lngap-n4bit

# SHA-256 bisection tests (backward compatibility)
cargo test -p lngap-harness --test p2_inner
cargo test -p lngap-harness --test p3_spv
```
