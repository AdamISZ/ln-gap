# The names contracts: messages and mechanics

Developer-facing walk-through of `nreg` (bonded registration) and
`anchorpay` (payment gated on an anchored entry): what travels between a
user and the hub, what each contract holds, and which transactions appear
on-chain in each failure case. Code: `crates/apps/names` (registry, hub,
programs), `crates/party` (the off-chain protocol and the dispute state
machine), `crates/harness/src/names_world.rs` (the two-channel world and
the users' application steps).

## 1. Cast and channels

- **Alice** (user, owner of `alice`) and **Bob** (user, buyer) each have a
  Lightning-style channel with the **hub**. Every contract lives in one
  channel as a contract output of both parties' commitment transactions.
- The **registry** is the hub's off-chain service: it answers requests with promises,
  batches them into an anchor every `interval` blocks, and serves the
  ledger. In the harness it is one object the world drives; a hub daemon
  would host it.
- The **world** (harness only) mines, delivers blocks to every party and to
  the registry, serves proof data to everyone, and performs the users'
  application steps. It never tells a party what to broadcast.

Three layers of messages exist. Between channel parties:

| layer | messages | purpose |
|---|---|---|
| application | `Statement { label, reveal }` | hand over a Lamport-signed hub statement (unused by these contracts; kept for value-carrying statements) |
| draft | `Draft { spec, change, extra_reveals }` → `DraftKeys { seq, keys }` or `Reject { seq, reason }` | agree a state change and exchange the Lamport/Winternitz keys the new state's leaves need |
| channel | `Propose { state }`, `CommitSigs { seq, commit_sig, graph_sigs }`, `RevokeAndAck { seq, secret, next_rev_hash }` | sign the new commitment transactions and every pre-signed graph transaction; revoke the old state |

Between a user and the registry (off-channel, in the harness a function
call): *request → promise*, and *serve* (ledger entries with their siblings,
the anchor transaction, headers).

## 2. Data the contracts name

**Entry.** Every registry event has a canonical 64-byte content record
(`1 ‖ c` commit; `2 ‖ name ‖ owner` reveal; `3 ‖ name ‖ new_owner ‖
valid_until` transfer) and a 32-bit key, the first 32 bits of
SHA-256(entry). The ledger is a sparse Merkle tree of depth 32 over
`key → SHA-256(entry)`.

**Anchor.** A fixed-layout transaction: one input spending the previous
anchor's output 1, outputs `OP_RETURN <69 zero bytes> <root> OP_0` and a
P2TR change; 208 bytes with the root at byte 128. One spendable output, so
the chain of anchors is a single line.

**Promise.** The hub's answer to a request at height `now`: the terms it
will be bonded to.

```
Promise {
  req_id,
  height h,              // the hub's next scheduled anchor: max(last + interval, now + 2)
  shape: AnchorShape {   // the inclusion proof the hub will owe
    chain: { checkpoint: digest of block `now`, nbits, n_headers: h - now },
    prev_anchor,         // the anchor-chain tip the anchor must spend
    entry, key,          // the event's entry and ledger key
    merkle_sides,        // the anchor's position in its block ([right]: index 1 of 2)
  },
}
```

`merkle_sides` belongs to the proof that the anchor transaction is *in*
the last header's block. This is public information, and the user's node
can check it directly, but the user is not the verifier: the verdict on a
bond is rendered by leaf scripts that see nothing but the claim, so every
fact the verdict rests on — headers, the anchor's bytes, its place in a
block, the ledger path — is re-established inside the claim. The siblings
can be data; the sides cannot, since "node ‖ sibling" versus "sibling ‖
node" is the structure of the hashing step and is fixed when the contract
opens. So the hub must know where its anchor
will sit in its block when it promises, as a hub with its own miner does
(the harness mines the anchor alone with the coinbase). Making the sides
prover-selected needs the same conditional gadget as an "at or before h"
promise.

A promise is not signed and carries no secret. It becomes binding when the
user opens a bond naming its terms and the hub co-signs that channel state:
from then on the hub either proves inclusion of exactly that shape or pays.
(An earlier design also had the hub Lamport-sign a *receipt* that the
user's claim leaf checked; with the request preceding the bond, the hub's
signature on the bond already says everything the receipt did, so it was
removed — D22.)

The shape is a set of constants. From it both parties build the same
128-step `ClaimSpec` (per header: three compressions with link and nBits
predicates, a target check; the anchor transaction as five compressions
with the spent-outpoint, output-count and `OP_RETURN` predicates and the
root copied into a register; the block Merkle path; the entry's leaf hash
and the 32-level ledger path; then `D == R`). The *data* for that program
(header bytes, the anchor's bytes, siblings) is served later.

**Before opening a bond on a promise** the user walks the anchor chain from
the agreed genesis through every anchor its node can see (confirmed, plus a
broadcast one) with `verify_anchor_chain`, and refuses the promise unless
`prev_anchor` is that walk's tip. For a reveal it also checks the promised
height falls inside the commit's window (`h ≤ h_commit + N`), since a later
anchor would not count.

## 3. `nreg`: bonded registration

Program name: `nreg:{json of NRegParams}` with `req_id`, `claim_from =
h + 2`, `shape`, `slot` (where the served data is found).
State machine (2 bits) and who moves:

```
Init ──user: "not anchored by the promised height"──▶ Claimed ──hub: inclusion proof──▶ Refuted ──user: heavier chain──▶ Reinstated
R(Init) = bond to hub       R(Claimed) = bond to user       R(Refuted) = bond to hub       R(Reinstated) = bond to user
```

Every move advances the state by one; the generic leaves `state_mismatch`
(`new != prior + 1`) and `code_mismatch` (`code != (new == Refuted ?
BondToHub : BondToUser)`) catch a Move that claims otherwise.

### 3.1 Opening (cooperative)

```
Alice → registry : request (Commit { c })                       at height now
registry → Alice : Promise { req_id, h, shape }
Alice            : verify_anchor_chain(genesis .. ) tip == shape.prev_anchor
Alice → hub      : Draft { change: Open { id, program: "nreg:{..}", stakes: [0, BOND], deadline },
                           spec: the new channel state with Alice's keys for depths 1..3 filled }
hub              : policy: the promise was made, the shape and claim_from match it, stakes are [0, ≤ BOND]
hub → Alice      : DraftKeys { seq, keys: hub's keys for depths 1..3 }
Alice → hub      : Propose { state }, CommitSigs { .. }        (signatures on the hub's commitment
                                                                and on every graph tx of both versions)
hub → Alice      : CommitSigs { .. }
Alice ↔ hub      : RevokeAndAck (both)                          old state revoked; new state live
```

Keys exchanged in `DraftKeys`, per depth position:

| depth | prover | prover's keys | challenger's keys |
|---|---|---|---|
| 1 | user | Lamport: move (1 bit), state (2 bits), code (2 bits) | — |
| 2 | hub | as above + Winternitz: end state (24 words), 7 × level-1 round states, re-commitments (cur, next), 16 block words, 48 schedule words, 2 × 7 inner states | Lamport: 7 level-1 indices (1 bit each), 2 inner indices (3 bits) |
| 3 | user | as depth 2 (the refutation claim: one header longer) | hub: the same index keys |

The pre-signed graph both parties sign at every state update is, per
commitment version: `settle`, `move_1`, `split_1_*`, `move_2`,
`split_2_*`, the depth-2 dispute chain (`dispute`, 7 × `p_round`/`q_round`,
the inner and check chains: about 20 transactions), `move_3`, `split_3_*`,
and the depth-3 dispute chain. A contract worth 40k reserves ~27k of fees
per depth for this; that is why `BOND = 40k`.

### 3.2 The honest path

```
height h-1  registry builds the anchor; the world mines it at h (a hub with a miner)
height h    registry: anchor confirmed; the world serves the proof data under slot/incl
            Alice's node: the anchor spends prev_anchor, its root includes her entry → "anchored"
Alice → hub : Draft { change: Cancel { id } }     fold the bond: R(Init) = bond back to the hub
hub → Alice : DraftKeys .. ; channel update as above
```

Off-chain, nothing but two channel updates. Alice's reveal follows the
same pattern once her commit is anchored, with its own bond.

### 3.3 The hub never anchors (N2)

```
height h+2  Alice → hub : Draft { change: Move { id, mv: [true], deadline } }
            hub: policy: no proof data for the slot → accepts (a cooperative hub folds later at the deadline);
                 a hub that has stopped signing answers nothing
            Alice: counterparty stalled → force-close
on-chain    commitment_k (Alice's version)
            move_1 : CLTV h+2, CSV to_self_delay (Alice broadcast), 2-of-2, Alice's Lamport reveals
                     (move, state = Claimed, code = BondToUser)
            hub    : has no proof; nothing to broadcast
            split_1_BondToUser after Δ + Δ' (the outcome favours the prover)
```

### 3.4 A false claim against an anchored entry (N3)

```
Alice → hub : Draft { Move .. "not anchored" }
hub         : policy: proof data present → Reject { reason: "I can prove request r is anchored; answering on-chain" }
Alice       : a refused move goes on-chain → force-close
on-chain    move_1 (Alice's claim)
            move_2 (hub): 2-of-2, hub's reveals (state = Refuted, code = BondToHub), the Winternitz-signed
                          end state of the inclusion claim (~5 kvB); C'_2 carries the `dispute` leaf
            Alice       : recomputes the claim on the served data: every predicate holds, the end state
                          matches → nothing to dispute; she could refute the chain (move_3) only with a
                          heavier one, which does not exist
            split_2_BondToHub after Δ
```

### 3.5 A bluffed proof (N8) and a private fork (N9)

Omission: the registry left the reveal out of the anchor but still serves
"proof data" (a path to the empty leaf). The hub refuses Alice's claim
off-chain as in 3.4, `move_2` goes on-chain, and Alice's party finds the
`ledger_root` predicate false:

```
dispute            (Alice; 2-of-2, pre-signed)
p_round_1..7 / q_round_1..7   hub commits register-file states; Alice picks the first wrong segment
q_round_7_check    the isolated step is a simple step
c_re_cur, c_re_next            hub re-commits the step's input and output
simple_ledger_root (Alice; single-signer, pays by size)   D ≠ R → the bond to Alice
```

Fork: the hub mined its anchor on a private fork. Alice's node never sees
it, so she claims; the hub's `move_2` proof is internally valid; the world
serves the real chain's headers under `slot/refute` once it is one longer;
Alice broadcasts `move_3` (the heavier-chain claim, same shape as `move_2`
with `n_headers + 1`); the hub finds nothing to dispute; `split_3_BondToUser`.

### 3.6 An invalid proof proposed off-chain

If the hub proposes its proof as an off-chain move, the user's party
recomputes the claim on the served data before answering the draft and
replies `Reject { reason: "the move's claim does not hold on the served
data" }` if a predicate fails; the hub then force-closes to enforce the
move, and the on-chain path of 3.5 follows.

## 4. `anchorpay`: the sale

Program name: `anchorpay:{json of AnchorPayParams}` with `prover`,
`shape`, `slot`. States: `Init → Paid` (prover's move, the inclusion
claim) `→ Refuted` (the other side's heavier-chain claim). `R(Paid)` pays
the prover, everything else refunds the locker.

The legs name the transfer entry, which exists once Alice signs, so the
order is:

```
Bob → Alice   : offer (off-protocol)
Alice         : sign Transfer { alice → K_B, valid_until h_sale }
Alice → registry : request; registry → Alice : Promise (shape names the transfer entry)
Bob  → hub (Bob's channel)   : Open leg 1  anchorpay { prover: Hub  }, stakes [PRICE, 0], deadline h_sale
hub  → Alice (Alice's channel): Open leg 2  anchorpay { prover: User }, stakes [0, PRICE], deadline h_sale
Alice → hub (Alice's channel) : Open the transfer bond: nreg on the transfer's promise
```

Cooperative (N4): the anchor confirms at `h`; the world serves the data;
the hub proposes `Move` in leg 1 (Bob's party recomputes the claim, accepts)
and Alice proposes `Move` in leg 2 (the hub accepts); both legs are then
terminal and are resolved (`Resolve { id }`) into the balances; the bond is
folded. No transaction on-chain.

Hub refuses to pay Alice (N7): Bob is dark, so the hub force-closes Bob's
channel and broadcasts `move_1` with its proof, then `split_1_Paid`. In
Alice's channel the hub rejects her leg-2 move; she force-closes and
broadcasts `move_1` with *the same* proof, built from the public data, then
`split_1_Paid`. The transfer bond settles back to the hub at its deadline
(the entry was anchored).

Hub stops anchoring after the promise (N6): leg 1 and leg 2 hit `h_sale`
and are cancelled (`Cancel { id }`: `R(Init)` refunds Bob and the hub);
Alice's claim on the transfer bond is accepted off-chain, and at the bond's
deadline `Cancel` pays `R(Claimed)` = bond to Alice.

## 5. What a party checks, and when

| moment | check | on failure |
|---|---|---|
| receiving a promise | `verify_anchor_chain` from genesis; tip == `prev_anchor`; a reveal's height within the commit's window | refuse the promise, open no bond |
| answering an `Open` draft (hub) | promise made, shape and `claim_from` match it, stakes within the bond | `Reject` |
| answering a `Move` draft | transition valid; if the move carries a claim, `spec.valid(served data)`; application policy | `Reject` (the mover may force-close) |
| seeing the counterparty's `move_d` on-chain | decode reveals; `transition`; generic leaves; if it carries a claim, recompute it on the served data | `disprove_*`, or `dispute` and the rounds |
| each dispute stage | it is my turn: answer from the committed values / pick the first wrong segment / disprove the isolated step | after Δ: `timeout` sweep by the other party |
| a counterparty that stops answering drafts | `stall_blocks` without progress | force-close |

## 6. Numbers (regtest, `crates/harness/tests/m4_names.rs`)

| item | value |
|---|---|
| a Move carrying a claim (24-word end state) | ~5 kvB |
| the inclusion claim | 128 steps, 7 level-1 rounds; `p_round` 4.9 kvB, `q_round` 0.2 kvB |
| N8's full dispute | 23 transactions; the disproof leaf `simple_ledger_root` ~10 kvB |
| fee reserve per claim depth | ~27k sat at 1000 sat per pre-signed transaction |
| Δ, Δ' | 6 blocks each; a claim's split waits Δ + Δ' when it favours the prover |
