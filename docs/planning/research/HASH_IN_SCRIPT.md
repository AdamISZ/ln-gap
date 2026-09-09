# How a hash function runs in Bitcoin Script

Background for the bisection dispute path: why the terminal leaf can
recompute a SHA-256 compression at all, and how such a script is built.
Worked through on a toy hash small enough to trace by hand. The toy script
below is built opcode for opcode and checked against all 256 inputs on
regtest by `crates/contract/tests/toy_hash_doc.rs`.

## 1. Why not `OP_SHA256`?

Script has a native hash opcode, but it hashes *one stack element* from the
fixed initial state, with padding. In a dispute the input is not one
element: it is a midstate and a block that the leaf has just verified out
of the prover's one-time signatures, as 192 separate nibbles. Without
`OP_CAT` those nibbles cannot be glued into a single 64-byte element, and
no opcode continues a hash from a chosen midstate. So the compression
function has to be *reimplemented* from arithmetic and stack operations.

That is possible because a compression is a fixed, loop-free computation:
64 rounds of 32-bit add, rotate, XOR and AND with no data-dependent control
flow. Script has no loops, but an unrolled straight-line program needs
none. Tapscript removed the old 10,000-byte script and 201-opcode limits,
so consensus allows a leaf of any size; what remains are the 1,000-element
stack limit, the 520-byte element limit, and the 400,000 weight-unit
standardness ceiling per transaction.

## 2. The building blocks

**Digits as script numbers.** Script numbers are small integers; there
are no 32-bit words. A hash state is kept as a run of stack elements, one
digit each. Real implementations use 4-bit digits (nibbles); the toy uses
2-bit digits (values 0–3) so that tables stay tiny.

**Lookup tables via `OP_PICK`.** There is no memory and no indexing
opcode. A table is a run of constants pushed onto the stack once; a lookup
computes the *depth* of the wanted entry and copies it with `OP_PICK`
(pop `n`, push a copy of the item `n` below the top). For a two-operand
table like XOR the index is `4x + y` (2-bit digits): `x` is doubled twice
with `OP_DUP OP_ADD`, `y` is added, then the constant distance from the
current top to the table is added, then `OP_PICK`.

**Modular add without `OP_MOD`.** `OP_MOD` and `OP_MUL` are disabled. An
addition of two digits is `OP_ADD`, then "if ≥ base, subtract base":
`OP_DUP <base> OP_GREATERTHANOREQUAL OP_IF <base> OP_SUB OP_ENDIF`.

**Static stack bookkeeping.** Every `OP_PICK`/`OP_ROLL` depth is a
constant in the script, so the generator must know, at every instruction,
exactly how many items sit above each table. One unaccounted push and
every later lookup silently reads the wrong entry. This is where all the
"offset" parameters in a real generator come from.

**The altstack** as scratch space for values that must survive a table
teardown or a block of computation.

## 3. The toy hash

State: two digits `(a, b)`. Block: two digits `(m0, m1)`. Two rounds:

```
t  = a XOR m_i
a' = (b + t) mod 4
b' = t
```

Worked example: `(a, b) = (2, 1)`, block `(3, 0)`.
Round 0: `t = 2 XOR 3 = 1`, `a' = (1 + 1) mod 4 = 2`, `b' = 1`.
Round 1: `t = 2 XOR 0 = 2`, `a' = (1 + 2) mod 4 = 3`, `b' = 2`.
Output `(3, 2)`.

The leaf checks "ToyHash(inputs) == (3, 2)". Witness, in consumption order
(top of stack first): `a, b, m0, m1`.

### 3.1 The script, annotated

Stack pictures are written top-right. `T` is the 16-entry XOR table.

```
# 1. Push the XOR table, entry k = 4x+y holds x XOR y, pushed k = 15 … 0
#    so that T[0] ends on top of the table.
OP_0 OP_1 OP_2 OP_3  OP_1 OP_0 OP_3 OP_2  OP_2 OP_3 OP_0 OP_1  OP_3 OP_2 OP_1 OP_0
#    stack: [m1 m0 b a  T15 … T0]

# 2. Bring the four inputs above the table: each is 19 deep (16 table + 3 others).
19 OP_ROLL  19 OP_ROLL  19 OP_ROLL  19 OP_ROLL
#    stack: [T  m1 m0 b a]

# 3. Round 0
OP_DUP OP_ADD OP_DUP OP_ADD        # 4a                      [T m1 m0 b 4a]
2 OP_PICK OP_ADD                   # + m0 = index k          [T m1 m0 b k]
3 OP_ADD OP_PICK                   # t = T[k]; 3 items (m1 m0 b) sit above T after k is popped
                                   #                         [T m1 m0 b t]
OP_TUCK OP_ADD                     # keep t, compute b+t     [T m1 m0 t b+t]
OP_DUP 4 OP_GREATERTHANOREQUAL OP_IF 4 OP_SUB OP_ENDIF   # mod 4  [T m1 m0 b' a']
2 OP_ROLL OP_DROP                  # m0 is used up           [T m1 b' a']

# 4. Round 1 (identical, except only 2 items sit above T after k is popped)
OP_DUP OP_ADD OP_DUP OP_ADD  2 OP_PICK OP_ADD  2 OP_ADD OP_PICK
OP_TUCK OP_ADD  OP_DUP 4 OP_GREATERTHANOREQUAL OP_IF 4 OP_SUB OP_ENDIF
2 OP_ROLL OP_DROP                  #                         [T b'' a'']

# 5. Park the output, drop the table, restore
OP_TOALTSTACK OP_TOALTSTACK  OP_2DROP ×8  OP_FROMALTSTACK OP_FROMALTSTACK
#    stack: [b'' a'']

# 6. Compare with the expected output
3 OP_EQUALVERIFY  2 OP_EQUALVERIFY  OP_1
```

89 bytes. Trace of round 0 with the example: `4a = 8`, `k = 8 + 3 = 11`,
`T[11] = 2 XOR 3 = 1 = t`, `b + t = 2`, `a' = 2`, `b' = 1`. The test
checks all 256 inputs against the native function.

### 3.2 From "hash equals constant" to a disprove leaf

In a dispute nothing is a constant: the inputs and the claimed output are
the prover's *commitments*. The leaf becomes:

```
<challenger key> OP_CHECKSIGVERIFY
verify signature on the claimed output (Winternitz), park its digits on the altstack
verify signature on the input state, park; push the block digits; restore the state
… the hash, exactly as above …
compare the computed output with the parked claim, digit by digit, AND the results
OP_NOT                              # spendable iff the claim is WRONG
```

The prover's signatures come from the confirmed round transactions; the
challenger copies them into its witness. The leaf's job is only "these
committed inputs do not produce that committed output".

## 4. Scaling to SHA-256

Same construction, bigger numbers (BitVM's nibble-wise generator, adapted
to take a midstate; measured on this branch):

| | toy | SHA-256 compression |
|---|---|---|
| digit | 2 bits | 4 bits |
| tables | one 16-entry XOR | half XOR (136), half AND, rotation tables (80), lookup helper |
| rounds unrolled | 2 | 64 (+ 48 message-schedule steps) |
| state on stack | 2 digits | 64 digits state + 128 block + 512 schedule + tables |
| peak stack | ~22 | 905 of 1,000 (the add tables would overflow it) |
| script | 89 B | 368,707 B |
| terminal leaf with two Winternitz midstates | — | 382,865 WU: standard-sized, mempool-relayed |

The stack limit is why everything is nibbles: a byte-wise XOR table is
65,536 entries. The 400 kWU ceiling is why the bisection stops at one
compression per step: two compressions in one leaf is 737 kWU.

## 5. Is the compression the necessary atom?

No. Bisection can go *inside* the compression: the state between rounds
is the eight working words, so three more 4-ary rounds would isolate a
single SHA-256 round and the terminal leaf would be a few kilobytes. The
price is three more Δ windows and three more prover commitments. BitVMX
takes this to the limit by compiling the hash to RISC-V and bisecting
over instructions. We stop at the compression because it is the largest
atom that fits a standard transaction, and every extra round is latency
in a dispute. The atom is a knob, not a law.

## 6. Where the pieces came from

The unrolled-hash-with-nibble-tables technique is the BitVM project's
(2024; `bitvm/src/hash/`, `bitvm/src/u4/`, MIT), with the stack-limit
reasoning written up by BitVMX. Lamport/Winternitz-carried state between
scripts goes back to Rubin's "Script state from Lamport signatures"
(2021). `OP_PICK` tables predate all of it. See
`PRIOR_ART_BISECTION.md` in this folder for citations.
