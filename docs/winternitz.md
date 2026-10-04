# Winternitz signatures in Script, and the parked register file

Script can't verify a Schnorr signature over an arbitrary message
(`OP_CHECKSIG` only checks signatures over the spending transaction). It
*can* verify a hash-based one-time signature, and that is how every
message which a player signs (e.g. a move, a pair of heads, an
outcome code) in a dispute reaches the stack. This page shows the Winternitz scheme used throughout the
repository, the script that verifies it, and why the verified message
stays on the stack afterwards as the **register file** that the
[disprove leaves](tictactoe-predicates.md) read.

## One digit, one hash chain

(I'd advise you to make sure you grok the basic ideas of Lamport and then Winternitz signatures before progressing. Rootstock have a decent explainer [here](https://www.rootstocklabs.com/blog/exploring-lamport-and-winternitz-signatures-for-stateful-bitcoin-scripts/), and you might find others but to be honest you're better off having an LLM take you through it, with diagrams and so on.)

The message is cut into 4-bit digits (nibbles). Each digit `i` gets a
secret `sk_i`, and the public key is the end of a 15-step `HASH160` chain:

```
 sk ──H──▶ H¹ ──H──▶ H² ──H──▶ H³ ── … ──H──▶ H¹⁵ = pk
            │                    │
            sign digit 1         sign digit 3:  reveal σ = H³(sk)

 verify digit d:  hash σ another 15 − d times and compare with pk
                  H¹²(H³(sk)) = H¹⁵(sk) = pk   ✓
```

Signing digit `d` reveals the chain element `d` steps from the secret. The
verifier hashes it the remaining `15 − d` steps. Because the verifier is
told `d` along with `σ`, the digit's value comes out of the verification:
a verified signature *is* the message, one stack element per digit.

## The checksum

Anyone who sees `σ = H³(sk)` can hash it once more and get a valid
signature for the digit **4**. Digits can be pushed upward, never down. So
the signer also signs a checksum:

```
 c = Σ (15 − d_i)     over the message digits, written as a few more digits
```

Raising any message digit lowers `c`, which would need a *smaller* checksum
digit: going back down a chain, which means inverting `HASH160`. A 96-byte
message (two heads) is 192 digits plus 3 checksum digits.

## The script, digit by digit

This is the verification of a one-byte message, 2 digits plus 2 checksum
digits (301 bytes; `cargo run -p lngap-pos --example doc_scripts` prints
it). The witness holds one `(σ, d)` pair per digit, and each digit's step
consumes its pair:

```
OP_SWAP OP_SIZE 20 OP_EQUALVERIFY OP_SWAP     σ must be 20 bytes
15 OP_MIN                                      clamp d to 0..15
OP_DUP OP_TOALTSTACK                           keep d for the checksum
8 OP_2DUP OP_LESSTHAN
OP_IF   OP_DROP OP_TOALTSTACK OP_HASH160 ×8    d < 8:  pre-hash 8 times, remember d
OP_ELSE OP_SUB  OP_TOALTSTACK                  d ≥ 8:  remember d − 8
OP_ENDIF
OP_DUP OP_HASH160 ×7                           build a list of 8 successive hashes
OP_FROMALTSTACK OP_PICK                        pick the one that should equal pk
<pk_i> OP_EQUALVERIFY
OP_2DROP ×4                                    drop the list
```

Rather than looping `15 − d` times (Script has no loops), the step
**builds all candidates and picks one**. This is BitVM's "list-pick"
verifier. Two traces:

```
 d = 3 (below 8)                                d = 11 (8 or above)
 σ = H³(sk)                                      σ = H¹¹(sk)
 pre-hash 8 times      → H⁸(σ)                   no pre-hash, index 11 − 8 = 3
 7 more, keeping each  → H⁸ H⁹ … H¹⁵ (of σ)       7 hashes, keeping each → H⁰ H¹ … H⁷ (of σ)
 PICK 3 (H¹⁵ is on top)→ H¹²(σ) = H¹⁵(sk) = pk ✓   PICK 3 → H⁴(σ) = H¹⁵(sk) = pk ✓
```

The step costs 15 `HASH160`s for a digit below 8 and 7 otherwise, and
about 75 bytes of script per digit. After the last digit, the checksum finale takes the digit values
back off the altstack, recomputes `Σ(15 − d_i)`, rebuilds the declared
checksum from its digits in base 16, and `OP_EQUALVERIFY`s the two.

## What's left: the register file

The finale **leaves the message digits on the stack**, digit 0 deepest and
the last digit on top. Nothing consumes them, so they become the input of
whatever follows in the same script:

```
 witness: (σ₀,d₀) (σ₁,d₁) … (σ₁₉₄,d₁₉₄)        WOTS-VERIFY(K_reb)
                    │                                  │
                    ▼                                  ▼
 stack:   d₀ d₁ d₂ … d₁₉₁   ← 192 digits: the two heads, one nibble per element
                    │
          ┌─────────┴───────────────┬──────────────────────────┐
          ▼                         ▼                          ▼
   the venue readout          a disprove leaf            a checked split
   (EC-OTS: is this what      (is a rule broken?)        (is the outcome what
    the venue sealed?)                                    this state implies?)
```

This is the trick that moves data across the pre-signed graph. A
pre-signed transaction can't carry new data to the next output (Bitcoin
has no covenants), but a **one-time key** can: the rebuttal signs the
two heads under the mover's rebuttal key, and every later leaf that
re-verifies a signature under the *same key* gets the *same digits*,
because a one-time key can only sign one message. That's why the code calls
it *parking*: the rebuttal parks the tuple, and the disproves pick it up.

## The tied variant: checking a signature against digits already there

The authorship check asks: did the mover's **state key** sign this head?
The head's digits are already on the stack (parked by the rebuttal key), so
the witness carries only the reveal hashes, and each digit's value is
copied from the register file with `OP_PICK` instead of coming from the
witness (`wots_verify_tied` in `crates/lamport`). The signature is then
bound to exactly what's parked, by construction:

```
 stack:   d₀ … d₁₉₁                      witness block: σ for each signed digit
               │  OP_PICK the digits of the head's signed region
               ▼
          verify each σ against those digits, and the checksum
          → the parked head is the one the mover signed
```

A rebuttal runs this twice: the mover's key over the new head, and the
claimant's key over the prior head. That second check is what lets the rebuttal skip reading the prior
head out of the venue (see [EC-OTS](ec-ots.md)).

## One-time, and why it matters

Two signatures under one key reveal two chain elements per digit. For
the *state* keys, that's a provable offence: the `equiv_d` leaf pays the
whole pot to the counterparty of a mover who signed two different heads at
the same depth, with no venue data needed. Each depth has its own state
key and rebuttal key, generated and exchanged when the contract is added to
the channel.

## Sizes

| message | digits | witness | verify script |
|---|---|---|---|
| 1 byte | 2 + 2 | 4 pairs | 301 B |
| 44 bytes (a blackjack head's signed region) | 88 + 3 | 91 pairs | ≈ 6.8 KB |
| 96 bytes (two heads) | 192 + 3 | 195 pairs | ≈ 14.2 KB |

The 96-byte verification is in front of every disprove leaf, which is
why each one is about 14–15 KB whatever its rule.
