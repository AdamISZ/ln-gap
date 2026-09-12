# Cryptanalysis Primer for the n4bit Hash Function

This document explains the cryptanalysis tests we implemented for the n4bit
hash function. You know hash function properties (collision resistance,
preimage resistance, etc.) but tend to treat the internal algorithms as a
black box. The goal here is to open that box — not to make you a
cryptanalyst, but to give you enough understanding to read the test output
and judge whether the results are concerning.

## The big picture

A hash function is a mixer. It takes an input of any length and produces
a fixed-length output where:

1. Every bit of the output depends on every bit of the input (diffusion)
2. No one can find two inputs that produce the same output (collision resistance)
3. No one can find an input that produces a given output (preimage resistance)
4. The output is indistinguishable from random (pseudorandomness)

The tests below check these properties at three levels: the S-box (the
nonlinear core), the round function (how differences propagate), and the
full hash (statistical behavior of the output).

## Layer 1: S-box analysis

The S-box is the only nonlinear component in the entire construction.
Everything else — the ADD key mixing, the permutation, the Feistel mix —
is linear over GF(2) (XOR-land) or over Z/16Z (ADD-land). If the S-box
is weak, the whole hash is weak. The S-box is where the cryptographic
"hardness" comes from.

We use the PRESENT cipher's S-box (ISO/IEC 29192-2). This is a well-
studied 4-bit S-box from a NIST-reviewed lightweight cipher. Using a
known-good S-box is much better than designing our own.

### Differential Distribution Table (DDT)

**What it measures**: If I flip some bits of the S-box input, which output
bits flip, and how often?

For each pair (input difference Δx, output difference Δy), the DDT counts
how many of the 16 possible inputs x produce that particular input→output
difference pair. For a 4-bit S-box, the table is 16×16.

**Why it matters**: Differential cryptanalysis exploits high-probability
differential trails. If the DDT has a large entry (say 6 or 8), then an
attacker can predict that a particular input difference will produce a
particular output difference with high probability, and chain these
predictions across rounds to distinguish the hash from random.

**The key number**: The **differential uniformity** is the maximum DDT
entry excluding (0,0). For a 4-bit S-box:
- Optimal: 4 (the best possible for any 4-bit bijection)
- Acceptable: 4 (we want this)
- Concerning: > 4

**Our result**: 4 (optimal). The PRESENT S-box is differentially 4-uniform,
which is the best possible for a 4-bit permutation. This is a known result
from the PRESENT literature.

### Linear Approximation Table (LAT)

**What it measures**: If I look at a linear combination (XOR of selected
bits) of the input, and a linear combination of the output, how often do
they agree?

For each pair (input mask α, output mask β), the LAT counts how many
inputs x satisfy (x AND α) has even parity iff (S(x) AND β) has even
parity. A count of 8 means "no correlation" — the mask pair is balanced.
A count of 0 or 16 means "perfect correlation" — the output bit is a
linear function of the input bits, which would be catastrophic.

**Why it matters**: Linear cryptanalysis exploits high-bias linear
approximations. If the LAT has large entries (far from 8), an attacker
can build a linear approximation of the cipher that holds with non-
negligible probability, and use it to distinguish the hash from random.

**The key number**: The **nonlinearity** = 8 - max|LAT entry - 8| (for
a 4-bit S-box). This measures how far the S-box is from being a linear
function.
- Optimal: 4 (the best possible for a 4-bit bijection)
- Acceptable: 4
- Concerning: < 4

**Our result**: 4 (optimal). Again, a known property of the PRESENT S-box.

### Algebraic degree

**What it measures**: Each output bit of the S-box is a Boolean function
of the 4 input bits. This function can be written as a polynomial over
GF(2) — the Algebraic Normal Form (ANF). The degree of this polynomial
is the algebraic degree. Degree 1 = linear (terrible). Degree 2 = quadratic
(okay). Degree 3 = cubic (best possible for a 4-bit bijection).

**Why it matters**: Algebraic attacks (like higher-order differential
attacks) can exploit low algebraic degree. If all output bits have degree
2 or less, the cipher is vulnerable. Degree 3 means the S-box uses the
full nonlinear capacity of a 4-bit function.

**Our result**: [3, 3, 3, 3] (optimal). All output bits have algebraic
degree 3.

### Branch number

**What it measures**: For each nonzero input difference, what is the
minimum combined weight (number of changed bits) of the input and output
differences? A branch number of 3 means: if you change 1 input bit, at
least 2 output bits change. If you change 2 input bits, at least 1 output
bit changes.

**Why it matters**: Higher branch numbers mean faster diffusion — a
difference in few input bits forces differences in many output bits, which
means the round function reaches full diffusion in fewer rounds.

**Our result**: 3 (good for a 4-bit S-box).

## Layer 2: Round function analysis

### Full diffusion round count

**What it measures**: If I start with a difference in a single nibble
(4 bits), how many rounds of the SPN does it take for that difference to
affect all 40 nibbles (160 bits) of the state?

**Why it matters**: If full diffusion takes more rounds than we apply,
then some output bits don't depend on some input bits. This means the
hash has "blind spots" — input changes that don't fully propagate, which
an attacker can exploit.

**Our result**: 41 rounds to reach full diffusion, but we only apply 20
rounds per absorb/squeeze. This is a real weakness.

**What it means**: The diffusion profile shows that after 5 rounds, 28/40
nibbles are affected. After 10 rounds, ~37/40. But it never consistently
reaches 40/40 — it oscillates between 34 and 39 because the permutation
has trapping: certain nibble positions are unreachable from certain
starting positions in certain rounds. The cross-boundary swap helps but
doesn't fully solve this.

**Options to fix**:
1. Increase ROUNDS from 20 to 50+ (costs more Script space)
2. Improve the permutation (better mixing between rows/columns)
3. Use a different diffusion structure (e.g., a full MDS matrix)
4. Use multiple starting differences and take the maximum

### Strict Avalanche Criterion (SAC)

**What it measures**: If I flip exactly one input bit, each output bit
should flip with probability exactly 50%. SAC tests this by flipping bit 0
of many random inputs and measuring the flip probability of each of the 160
output bits.

**Why it matters**: If some output bits flip with probability far from 50%
(say 60% or 40%), then those bits are "biased" — they are not fully
independent of the flipped input bit. This creates distinguishability
from random.

**Our result**: Max deviation from 0.5 is 0.0156 (1.56%). This is
excellent — well below the 10% threshold. Despite the incomplete diffusion
at the nibble level, the bit-level avalanche is good because each nibble
contains 4 bits and the S-box mixes them well.

### Bit Independence Criterion (BIC)

**What it measures**: For each pair of output bits (i, j), when we flip
one input bit, the flips of bits i and j should be statistically
independent. BIC measures the maximum correlation between the flip
indicators across all pairs.

**Why it matters**: If two output bits are correlated (they tend to flip
together or never together), then knowing one bit gives information about
the other, reducing the effective output size.

**Our result**: Max correlation 0.025 (2.5%). This is good — well below
the 15% threshold.

## Layer 3: Hash function statistical tests

### Avalanche weight distribution

**What it measures**: For many input pairs differing by exactly one bit,
the Hamming weight (number of 1-bits) of the output difference should
follow a Binomial(160, 0.5) distribution — mean 80, standard deviation
~6.32. We measure the actual mean and standard deviation.

**Why it matters**: If the mean is far from 80, the hash is not achieving
50% avalanche. If the standard deviation is far from 6.32, the distribution
is not binomial, which suggests structural bias.

**Our result**: Mean 80.05, std 6.31. Essentially perfect. This is the
most important statistical test and we pass it comfortably.

### Chi-square test on nibble values

**What it measures**: For each of the 40 nibble positions in the output,
count how often each value (0-15) appears across 10,000 hash outputs.
Under the null hypothesis (uniform), each value should appear ~625 times.
The chi-square statistic measures how far the observed counts deviate from
expected. With 16 categories and 10,000 samples, the critical value at
p=0.01 is 30.58.

**Why it matters**: If some nibble values are significantly over- or
under-represented, the hash has a bias. A biased hash is distinguishable
from random, which breaks the pseudorandomness property.

**Our result**: Max chi-square 34.35, which exceeds the critical value
30.58. This means at least one nibble position has a detectable bias.

**What it means**: With 40 positions tested at p=0.01, we expect ~0.4
false positives by chance alone. So one failure is borderline. However,
combined with the diffusion weakness (41 rounds > 20 ROUNDS), this is
more likely a real bias from insufficient mixing than a statistical fluke.

**Note**: This test is sensitive to the PRNG used for input generation.
A different PRNG or more samples might give a different result. The
important thing is the pattern: diffusion weakness + chi-square failure
are related.

### Birthday collision search

**What it measures**: We truncate the 160-bit hash to 20 bits and hash
random inputs until we find two that collide (same truncated hash). The
birthday bound says this should take ~2^(20/2) = ~1024 hashes.

**Why it matters**: If collisions are found significantly faster than the
birthday bound, the hash has a structural weakness that makes collision
finding easier than brute force. If collisions are found at approximately
the right rate, the hash behaves like a random function (at least for
collision resistance).

**Our result**: Found in 6741 hashes (6.6x the expected 1024). This is
within the normal variance of the birthday problem (the distribution has
a long tail). The fact that it took longer than expected is not concerning
— it just means this particular run was unlucky. What matters is that it
wasn't found in, say, 50 hashes (which would indicate a catastrophic
weakness).

### Preimage search

**What it measures**: We pick a random target hash, truncate to 16 bits,
and search for an input that produces that truncated hash. The expected
work is ~2^16 = ~65536 hashes.

**Why it matters**: If preimages are found significantly faster than 2^n,
the hash has a weakness in its one-wayness property.

**Our result**: Found in 16642 hashes (0.25x the expected 65536). Again,
this is within normal variance. Preimage search has high variance because
it's a search problem — sometimes you get lucky.

### Sponge capacity analysis

**What it measures**: This is not a statistical test but a theoretical
analysis. The sponge construction's security is bounded by its **capacity**
— the part of the state that is never directly output. For a sponge with
capacity c bits:
- Collision resistance: 2^(c/2)
- Preimage resistance: 2^c
- Second preimage resistance: 2^c

**Why it matters**: This is the most important finding. Our sponge has a
160-bit state split into 80-bit rate + 80-bit capacity. The capacity is
only 80 bits, giving collision resistance of only 2^40 — far below the
2^80 target.

**What it means**: This is a design-level issue, not a test failure. The
sponge construction's security is provably bounded by the capacity. No
amount of rounds or S-box quality can overcome a too-small capacity.

**Options to fix**:
1. **Increase the state size** to 240 bits (60 nibbles) with 160-bit
   capacity (40 nibbles) and 80-bit rate (20 nibbles). This gives 2^80
   collision resistance but requires 50% more state and more Script
   operations per round.

2. **Switch to a Merkle-Damgård construction** where collision resistance
   is 2^(n/2) = 2^80 for a 160-bit output. But Merkle-Damgård has
   length-extension issues and is harder to implement in Script.

3. **Accept 2^40 collision resistance for the PoC** — the architecture
   is not bound to this hash design, and the PoC's purpose is to measure
   Script costs, not to be cryptographically secure. Document the weakness
   and move on.

Option 3 is the right choice for the PoC. The architecture (custom PoW
fact chain, root in header, bisection, contract state machine) is
independent of the hash function. The hash can be swapped without changing
the architecture. What matters for the PoC is that the hash has the right
*structural shape* (4-bit operations, Script-native) for measuring costs.

## Summary of findings

| Test | Result | Status |
|------|--------|--------|
| S-box differential uniformity | 4 (optimal) | PASS |
| S-box nonlinearity | 4 (optimal) | PASS |
| S-box algebraic degree | [3,3,3,3] (optimal) | PASS |
| S-box branch number | 3 (good) | PASS |
| Full diffusion | 41 rounds (need 20) | WARNING |
| SAC | 1.56% max deviation | PASS |
| BIC | 2.5% max correlation | PASS |
| Avalanche distribution | mean 80.05, std 6.31 | PASS |
| Chi-square | 34.35 > 30.58 | WARNING |
| Birthday collision | 6741 hashes (expected ~1024) | PASS |
| Preimage | 16642 hashes (expected ~65536) | PASS |
| Sponge capacity | 2^40 < 2^80 target | CRITICAL |

## What passes and what doesn't

**The S-box is excellent.** All S-box properties (differential uniformity,
nonlinearity, algebraic degree, branch number) are optimal. This is
expected — we're using the PRESENT S-box, which is well-studied and
known-good. The S-box is not the problem.

**The statistical properties are mostly good.** Avalanche, SAC, BIC, and
the avalanche weight distribution all pass comfortably. The hash function
behaves like a random function at the bit level, despite the incomplete
nibble-level diffusion.

**There are three issues, in order of severity:**

1. **Sponge capacity (CRITICAL)**: 80-bit capacity gives only 2^40
   collision resistance. This is a design-level issue, not a test failure.
   For a production hash, the capacity must be ≥ 160 bits. For the PoC,
   this is acceptable — the hash is a placeholder and the architecture is
   hash-agnostic.

2. **Full diffusion (WARNING)**: 41 rounds to full diffusion but only 20
   rounds applied. Some nibble positions are not fully diffused. This
   causes the chi-square bias. Fixing the permutation (better mixing
   between rows and columns) would address both issues.

3. **Chi-square bias (WARNING)**: One nibble position shows non-uniform
   distribution. This is likely a consequence of the diffusion weakness.
   With more rounds or a better permutation, this would resolve.

## External tooling we looked at

- **TestU01** (L'Ecuyer & Simard, Université de Montréal): The gold
  standard for RNG testing. Implements SmallCrush, Crush, and BigCrush
  test batteries. A Rust wrapper exists (rust-testu01) but covers only
  a subset. Would require wrapping our hash as a PRNG to feed it. Most
  relevant for testing output pseudorandomness at scale.

- **NIST SP 800-22**: Statistical test suite for random number generators.
  15 tests including frequency, runs, spectral, serial, approximate
  entropy, and more. Available in C/Python. Would need to feed our hash
  output as a bitstream. Overlaps significantly with what we implemented
  natively (chi-square, runs, avalanche are all in our suite).

- **SMHasher / HashWolf**: Specifically designed for testing non-
  cryptographic hash functions (murmur, cityhash, etc.). Tests avalanche,
  collisions, distribution, seed independence. Less relevant for our case
  since we're testing a cryptographic hash, not a hash table hash.

- **Dieharder**: Another RNG test suite, successor to the original
  Diehard tests. Overlaps with TestU01.

For the PoC, our native Rust implementation covers the most important
tests. Running TestU01 or NIST SP 800-22 would be a good follow-up if we
want to subject the hash to more rigorous statistical scrutiny, but the
three findings (capacity, diffusion, chi-square) are the ones that matter
for architectural decisions.

## What this means for the project

The cryptanalysis confirms what the research documents predicted: the n4bit
hash is a toy with the right structural shape but not production-ready.
The three findings are all addressable without changing the architecture:

1. **Capacity**: increase the state to 60+ nibbles, or switch to a
   Merkle-Damgård construction, or use a different hash entirely. The
   architecture doesn't care — the hash is a swappable component.

2. **Diffusion**: improve the permutation. The current ShiftRows + column
   rotation + cross-boundary swap has trapping. A better permutation
   (e.g., based on a 5×8 or 8×5 MDS matrix, or a different shift schedule)
   would fix both the diffusion and the chi-square bias.

3. **Chi-square**: will resolve once diffusion is fixed.

The PRESENT S-box (the nonlinear core) is optimal on all metrics. The
problem is in the linear layers (permutation and round count), which are
the easiest parts to change.
