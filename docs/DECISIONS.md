# Design decisions beyond the plan

Decisions taken while implementing, where the plan was silent or inconsistent.
Each states the default chosen; revisit if a scenario contradicts it.

## D1. Settle is delayed in the broadcaster's commitment version

If a party broadcasts a *revoked* commitment whose contract deadline has passed,
the pre-signed Settle for that state could be broadcast immediately by anyone
holding it, spending the contract output before the counterparty's revocation
sweep. So the broadcaster's own version of the `settle` leaf carries
`CSV to_self_delay` in addition to the CLTV deadline, exactly as the
broadcaster's own `move` leaf does. Since either version's broadcaster could
be the cheater, *every* version's `settle` leaf carries the CSV: honest
settlement after a force-close waits `to_self_delay` blocks.

## D2. Off-chain deadlines leave room for a force-close

The party on turn who force-closes must wait `to_self_delay` before its Move
can confirm. So at every off-chain update the new absolute deadline is
`current_height + to_self_delay + Delta + margin` (regtest: 6 + 6 + 8 = 20
blocks), and a party's watch loop force-closes when the counterparty stalls
and fewer than `to_self_delay + margin` blocks remain before the deadline.

## D3. N-REG uses two deadlines

The hub's receipt promises inclusion by `d_receipt`. The user's `move_user`
leaf carries `CLTV d_receipt` (a claim of non-attestation is meaningless
before then). The `settle` leaf that returns the bond to the hub carries
`CLTV d_contract` with `d_contract = d_receipt + to_self_delay + Delta + margin`.

## D4. Transfers carry a validity height

A signed transfer is `(name, new_owner, valid_until)`; the registry rules
ignore a transfer anchored after `valid_until`. Otherwise a hub that sat on a
receipted transfer (N6) could anchor it later and hand the buyer the name
after the buyer was refunded.

## D5. Sale leg 2 is two contract outputs

In the seller's channel: (a) the attestation-gated payment, (b) an N-REG-style
bond on the transfer receipt. Kept separate so (b) is the same code as N-REG.

## D6. No `disprove_bad_preimage` leaf in sale leg 1

The hub's `move` leaf already verifies the attestation preimages with
`expect_bit` gadgets; a "bad preimage" disproof can never be satisfied. Leg 1
has no disprove leaf, and the doc says so.

## D7. Interpreter for leaf tests

`bitcoinconsensus` (as vendored by rust-bitcoin 0.32) predates Taproot flags,
so all leaf tests run through a regtest node's `testmempoolaccept` and real
spends. The harness is the interpreter.

## D8. Fees and who pays

Every pre-signed transaction pays a fixed 1000-sat fee from the value it
carries. The commitment transaction's fee comes from the broadcaster's own
balance ("price the closer").

## D9. Scenario T6 as written is not fraud

After the hub's legal Move_2 (cell 3) the user is on turn in an open game, so
`R(s')` is *HubWins* (user forfeits): "code HubWins" is the honest code. T6 is
therefore run as a status fraud (hub claims the board is won by O, code
HubWins) disproved by `status_mismatch`, plus T6b, a pure code fraud (code
Draw on an open board) disproved by `code_mismatch`.

## D10. Contract changes are negotiated in two phases

A Lamport key's hashes must be in the counterparty's leaves before the state
is signed, and only the key's owner can produce them. So a contract change is
`Draft` (change + resulting state with the proposer's keys) → `DraftKeys`
(the responder's keys for its prover depths) → the ordinary channel update.
The channel's update policy accepts a `Propose` only if it equals the agreed
draft. Keys are labelled `c{id}/s{seq}/d{depth}/{field}` with the seq at which
the contract tuple was last changed, so no key is ever bound to two values.

## D11. Disprove leaves are declarative and two-phase

A leaf body declares its inputs first (decoded and parked on the altstack),
then computes. This keeps Lamport decoding from ever seeing a script value on
top of the stack, and lets the framework derive the witness layout from the
declaration order. Each leaf also carries a native `detects` closure; the
tests assert interpreter and native agree on every claim, and the party uses
`detects` to pick the leaf.

## D12. One check per leaf, per cell where needed

Tic-tac-toe uses 9 `cell_occupied_i` and 9 `board_mismatch_i` leaves rather
than indexing the board in script. The tree grows (26–28 leaves) but every
leaf stays under 400 B except `status_mismatch` (1.4 KB, the win-line check).

## D13. Force-close triggers

A party force-closes when an update it is waiting on has stalled for
`stall_blocks = 2` blocks, or when the counterparty is on turn in a contract
and the deadline has passed. Both are reactions of the watch loop, not
harness instructions.

## D14. Statements are 32-bit Lamport slots the party layer can learn

Receipts and attestations are Lamport keys owned by the hub. A party keeps a
store of statements (label → reveal) filled by messages, by drafts (an
off-chain Move must show the extras its leaf would require), and by scanning
every confirmed witness for preimages of keys it knows. That last channel is
how Alice copies the attestation the hub revealed in Bob's channel (N7) or in
its own disproof (N3).

*Resolved by D22 (2026-09-10):* receipts are gone; the statement machinery
remains for value-carrying statements.

## D15. Refused valid moves go on-chain

If the counterparty rejects a Move draft, the proposer force-closes and makes
the move on-chain. Rejection is a message, not a stall, so this is explicit.
A cheating proposer (N3) triggers the same path and loses on-chain.

## D16. One registration bond covers commit and reveal

The N-REG bond is opened with the commit's receipt; the attestation the hub
must produce to reclaim it is `attest(name, owner)`, which needs the reveal
anchored too. The reveal gets its own receipt but no second bond.

## D17. Names contract ids and parameters travel in the program name

`nreg:{json}` / `attestpay:{json}` carry the receipt id, the statement keys
and deadlines, so both parties rebuild identical leaves from the name alone.
Verbose (a few KB per contract) but unambiguous.

## D18. Two-level dispute search; pre-signed dispute transactions pay by size

A claim whose steps are SHA-256 compressions is searched in two levels:
bisection over compressions (level 1), then, inside the isolated
compression, publication of the 48 schedule words and bisection over the 64
rounds (`k = 8`), ending in a one-round disprove leaf of 11–23 KB instead of
a 379 KB compression leaf. Costs ~5 more response windows; the largest
transaction drops from 96 kvB to 12 kvB and the whole dispute from 107 to 53
kvB. The schedule and the first inner round are separate transactions
because a transaction's initial witness stack counts against the 1000-item
execution limit (48 + 7 Winternitz signatures would exceed it).

Pre-signed transactions of the inner chain pay `max(1000 sat, 0.2 sat/vB ×
estimated size)`, the estimate being a function of the spent leaf's script
length so both signers agree; the fixed fee alone is below the 0.1 sat/vB
relay floor for a 12 kvB transaction. (D8 otherwise stands.)

## D19. Register-file claims; prover data enters as block words

A claim is a program over at most 24 words of 32-bit registers: SHA-256
compressions and simple check/copy steps. Prover data (headers, siblings,
transaction bytes) enters only as block words of a compression, committed
per word in the dispute, and every check on it is a predicate of that
compression. The width bound comes from the 1000-item execution stack: a
state commitment is `2 (8 n + 3)` witness items and a disprove leaf verifies
at most two states. Wide claims use branching 2 at level 1. The isolated
step's input and output are re-committed under path-independent keys, so
every disprove leaf is shared by all paths and only the two families of
re-commitment mismatch leaves depend on the path.

The challenger judges a claim with the data the prover serves off-chain:
every predicate must hold and the end state must match; a segment with a
failed predicate counts as wrong. A prover serving different data than it
commits on-chain is not caught (see the plan's phase 2b limitations).

## D20. Registry facts are inclusion proofs; the hub promises a height

The names registry keeps no attestations. The hub's answer to a request
(a *promise*, D22; called a receipt when this was written) names the anchor
confirming at a specific height and carries the shape of the
inclusion proof the hub will owe (checkpoint block, header count,
anchor-chain tip, entry), so the bond contract can pre-sign the proof's
dispute graph at open time. The hub's answer to a claim is the proof
itself (a Move at depth 2 carrying a 128-step bisection claim), refutable
by a heavier chain at depth 3. Ledger entries are content-only 64-byte
records keyed by their hash; salts and signatures are served alongside.
Proof data is public (the harness serves it to both parties); a hub that
withholds it fails its own proofs, but a user who must prove (leg 2 of a
sale) depends on the ledger being public. Bonds and payments carrying such
claims are 40k sat because the pre-signed dispute chain reserves ~27k sat
of fees per depth (D8, D18).

The anchor chain is a single line only because every anchor has exactly one
spendable output. That shape is enforced twice: the inclusion claim's first
anchor step has predicates that the transaction spends the agreed tip, has
exactly two outputs, and that output 0 begins with `OP_RETURN`; and before
trusting a promise's `prev_anchor`, a user walks the chain from genesis
through every anchor it can see (`verify_anchor_chain`) and refuses a
promise whose tip is not the chain's. The second is a rule of use, not a
script: an anchor nobody ever proved against could otherwise fork the chain
for later users.

## D21. Claims are state-relative and checked off-chain before acceptance

A program's claim is indexed by the state a move leaves *from*, not by the
depth counted from the contract's initial state: an off-chain accepted
move re-instantiates the contract at its new state, where the next move is
depth 1 again. The generic `state_mismatch` and `code_mismatch` leaves of
the linear programs (`nreg`, `anchorpay`, `spv`) are likewise written
against the prior state (`new == prior + 1`) rather than a depth constant.
Before answering a `Move` draft whose move carries a claim, a party
recomputes the claim on the served data and rejects the draft if a
predicate fails; the mover then force-closes and the claim's committed end
state can be disputed on-chain. Without both, a hub could have moved a bond
from Claimed to Refuted off-chain with no proof at all.

## D22. Promises, not receipts

The hub answers a request with a *promise*: the anchor height and the
inclusion-proof shape (checkpoint, header count, anchor-chain tip, entry).
It is not signed and carries no secret; it binds when the user opens a bond
naming its terms and the hub co-signs that channel state. The earlier
Lamport-signed receipt checked in the user's `move_1` leaf added nothing to
that signature (the request precedes the bond), so it was removed along
with the statement key exchange for these contracts; `move_1` keeps only
the CLTV at the promised height plus a grace. Before opening the bond the
user walks the anchor chain to the promise's tip (D20) and, for a reveal,
checks the promised height lies within the commit's window; the hub's open
policy checks the bond's terms equal the promise's. Saves ~1.4 KB per
claim transaction and one message in the opening exchange.

## D23. The fact chain hashes with the function the claim model computes

`lngap_n4bit::hash_claim` absorbs 8-byte blocks (two 32-bit claim words)
zero-padded to the rate, restarts the round counter at every message and
advances it per block, pads with one all-zero block and outputs the whole
40-nibble state. The chain's digests, roots and proof of work use it.
Before this the claim model and `n4bit::hash` were unrelated functions
(10-byte blocks, a `+1` padding step, a squeeze; and the claim's round
counter depended on the step's position in the whole claim), so the
fact-chain claim could only assert that the prover knew a hash chain of
the header bytes — no prev-link, proof-of-work or root predicate could be
written, and the builder skipped them (`FactChainShape` still does).
`ClaimSpec::round_counter` is the message-relative counter, used by the
native evaluation, the flat terminal leaf and the party's inner-chain
recomputation alike. `Pred::LeTargetBe` compares a nibble range as a
big-endian number, the n4bit target check.

## D24. Slot claims verify inclusion in full

`lngap_factchain::slot::SlotShape`: a 16-word register file `D | P | R | E`
(hash state, previous digest, root field, entry word). Header fields enter
as block nibbles, so the prev-link is an `EqNibbles` predicate on the
absorb steps and the root field is copied to `R` as it streams by; the
proof of work and `D -> P` are one simple step per header; the entry's
constant word is `EqConst` and its `(move, state)` word is copied to `E`;
`root_ok` compares `D` to `R`. With `flat_inner` the compress-step
predicates and copies were unenforced (the flat terminal tree carried only
the compression leaf); it now carries the block, mismatch, `ckeep`,
`cpred` and `ccopy` leaves and the party checks them before the
compression.

## D25. Star graphs, prior reveals, and the end-state bind

`GraphShape::Star`: a claim leaf per depth off the commitment's contract
output, each revealing the counterparty's state at the previous depth
under the counterparty's own per-depth key (the reveal is read off the
venue); off each claim one refutation (`r{d}/move_{d+1}`), and nothing
after a refutation. The refuted claimant is on turn at `s_{d+1}` and
forfeits by the existing rule. `EndBind` makes the Move leaf decode the
move and state reveals and compare them with a word of the WOTS-committed
end state, so a claim's disproofs judge the move the venue entry names.
Star programs never move off-chain: the contract's state is the initial
state until it folds (`Change::Fold`, an agreed distribution the responder
checks against the venue; refused by default).

## D26. The venue is slotted and absence is a lie

One fact-chain block per Bitcoin block; block `d` after the open is move
`d`'s slot, so every claim's header count is fixed at open and a late
move is a stall. A depth-`d` claim carries `CLTV btc_open + d + 1 + grace`:
the counterparty's slot passes before a timeout claim can be made. A
timeout claim refuted by the counterparty's move `d + 1` (with its
inclusion claim) is a lie and forfeits the stake; the summons response on
Bitcoin (VENUE.md §4) is not built, since a single honest miner cannot
censor. Each side stakes `STAKE + RESERVE`; the reserve returns on a fold
and goes to the winner on-chain, so stalling costs more than resigning.

## D27. Entry authentication is off-chain only

A venue entry carries a tag over the mover's Lamport preimages, served
alongside; the claim binds the entry's content to the on-chain reveal but
never hashes the preimages. An entry with the right content and garbage
preimages is a stall the counterparty cannot attribute on-chain. Listed
with the served-data gap (D19, SPV_DISPUTE.md limitations): both are
bytes the commitment does not cover. The fix is to hash the preimages
inside the claim under an n4bit-keyed Lamport key, which needs
conditional predicates.

## TODO

- **N8 / anchor verification.** Omission, a corrupt root and a private fork are
  now enforced on-chain (D20, scenarios N8–N9). Still open: binding the served
  proof data to the Move, and user-side non-inclusion claims.
- **Venue (GAME_PROTOCOL.md §5).** Entry authentication in the claim (D27);
  the summons response on Bitcoin; variable-length claims for response
  windows; the equivocation leaf; `settle` after the deadline ignores the
  venue; a smaller register file for the claim transaction.
- **T9 / liveness rule.** Scenario T9 documents that an honest user who ignores
  a hub force-close during their own turn forfeits the stake (Settle pays R(s)
  = hub wins). Agreed as the PoC reading on 2026-09-06; revisit whether the
  force-move rule should distinguish "did not move" from "could not move".
