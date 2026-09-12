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

## 2. Scenarios (N1-N9)

All 9 scenarios pass on regtest:

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
| N9 | Hub proves inclusion on a private fork; Alice refutes with the heavier chain | no dispute is possible on either side; resolution by chain length; bond to Alice |

N8 is the key stage-2 scenario: the hub cheats by altering the claimed
end state of its inclusion proof. Alice disputes, the bisection
protocol runs through 3 level-1 rounds (k=2), narrows to the isolated
step. With flat_inner, the dispute then uses a single flat terminal leaf
that recomputes all 20 n4bit SPN rounds in one transaction — no
re-commitments, no inner rounds, no back-and-forth narrowing. The full
dispute transaction chain executes on regtest:

    commitment_2, claim_to_remote, claim_to_local, move_1 (hub's proof),
    d1/dispute (Alice disputes), p_round_1, q_round_1, p_round_2,
    q_round_2, p_round_3, q_round_3_check, c_re_cur, c_re_next,
    simple_nop (disproof)

N9 is the complementary case: the hub's inclusion proof is on a private
fork — internally valid, so Alice cannot disprove it. Her answer is the
heavier real chain: the factchain world mines the hub's entry on a fork
(hub sees it, users don't) while the real chain advances past it, then
serves the refutation data (`{req}/refute`, one more header from the same
checkpoint). On-chain: commitment_2, claim_to_remote, claim_to_local,
move_1 (hub's fork proof — Alice's party recomputes it: end state
correct, nothing to dispute), move_2 (Alice's refutation — the hub
recomputes it: correct, nothing to dispute), split_2_BondToUser after the
challenge window. The bisection never runs; the resolution is by chain
length, encoded structurally: the depth-3 claim commits to n_headers+1
headers from the same checkpoint.

## 3. Dispute chain measurement

  cargo test -p lngap-harness --test fc_stage2_measure -- --nocapture

### 3.1 Scaling table

| kind    | W   | steps | rounds | script (B) | witness (B) | fee (sat) | txs | build (ms) |
|---------|-----|-------|--------|------------|-------------|-----------|-----|------------|
| n4bit   | 1   | 8     | 3      | 24,782      | 12          | 12,000     | 12  | 20         |
| SHA-256 | 1   | 4     | 2      | 204,342     | 15          | 19,803     | 15  | 162        |
| n4bit   | 10  | 128   | 7      | 38,266      | 20          | 20,000     | 20  | 101        |
| SHA-256 | 10  | 64    | 6      | 262,514    | 23          | 27,803     | 23  | 249        |
| n4bit   | 100 | 1024  | 10     | 48,379      | 26          | 26,000     | 26  | 790        |
| SHA-256 | 100 | 512   | 9      | 306,143    | 29          | 33,803     | 29  | 766        |

### 3.2 n4bit vs SHA-256 ratios (SHA-256 / n4bit)

| W   | script  | witness | fee  | tx   | build |
|-----|---------|---------|------|------|-------|
| 1   | 8.2x    | 1.2x    | 1.7x | 1.2x | 8.1x  |
| 10  | 6.9x    | 1.1x    | 1.4x | 1.1x | 2.5x  |
| 100 | 6.3x    | 1.1x    | 1.3x | 1.1x | 1.0x  |

### 3.3 Per-round Script leaf

| metric              | n4bit   | SHA-256  | ratio   |
|---------------------|---------|----------|---------|
| per-round leaf size | 1,041 B | ~12,000 B| 11.5x smaller |
| stack elements      | 61      | ~672     | 11x fewer |

### 3.4 Key findings

1. **Script size: n4bit is 6.3-8.2x smaller** across all W values. At
   W=100, n4bit uses 48 KB of script vs 306 KB for SHA-256.

2. **Build time: n4bit is comparable or faster** — at W=1 and W=10
   it's 2.5-8x faster; at W=100 the flat terminal leaf is larger,
   evening out the build time (the 20-round leaf takes more Script to
   construct than the old 1-round leaf).

3. **Both scale logarithmically.** Bisection means the transaction
   count grows as O(log W), not O(W). n4bit goes 12 -> 20 -> 26 txs
   (W=1 -> 10 -> 100); SHA-256 goes 15 -> 23 -> 29.

4. **The flat_inner optimization eliminated 10 transactions.** By
   replacing the inner bisection (re-commit + schedule + 5 inner rounds
   + terminal = 13 txs) with one flat terminal leaf that recomputes all
   20 SPN rounds in a single transaction, n4bit drops from 36 to 26 txs
   at W=100. SHA-256 cannot do this (64 rounds x 12 KB = 768 KB in one leaf
   is a non-starter); the inner bisection is forced by SHA-256's cost. n4bit
   is cheap enough to skip it entirely.

5. **Script grows sub-linearly.** n4bit script: 25 KB -> 38 KB -> 48 KB
   (1.95x from W=1 to W=100). The growth is dominated by the
   level-1 round transactions (which carry WOTS commitments that don't
   shrink with the hash function), not the terminal leaf.

6. **Fee and witness counts are slightly better for n4bit** now that
   flat_inner removed the extra inner-round transactions. At W=100,
   n4bit uses 26 txs / 26k sat vs SHA-256's 29 txs / 34k sat. In a real
   fee market where cost scales with script/witness size, n4bit would be
   far cheaper: 48 KB vs 306 KB of script means far less block space.

6. **The per-round leaf ratio (11.5x) is higher than the total-chain
  ratio (6.3x)** because WOTS commitment overhead doesn't shrink. Each
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

5. **Heaviest-chain is structural, not an explicit on-chain check**: N9
   now runs on the fact chain: the hub's private-fork proof and Alice's
   heavier-chain refutation are both internally valid, no bisection runs,
   and the longer chain wins by timeout. But "heavier" is encoded by the
   refutation ClaimSpec's shape (n_headers+1 from the same checkpoint),
   not by an on-chain comparison of two chains. That suffices at fixed
   difficulty with n_headers = 1; the general version (variable-length
   claims, item 4, and comparing chains of different lengths) needs the
   comparison made explicit.

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
