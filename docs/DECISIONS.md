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

## D27. A claim verifies the counterparty's published signature; nobody needs the other side's secrets

Revealing Lamport preimages on the venue signs a move, but a signature is
only ever *checked* on Bitcoin by being used in a valid spend, so an
unsigned entry with the right content was indistinguishable from a signed
one to the one party who needed it signed (the counterparty could not
present garbage preimages and could not exhibit that they were garbage).
Resolution, three parts:

- Entries carry the mover's state preimages inline; the block root is a
  two-level hash of the content and the claim-native digest of each
  20-byte chunk (`entry_root`, uniform for all entries). The claim
  absorbs that stream, so the digests are block words, and each must
  equal the commitment selected by the corresponding state bit of the
  content word (`Pred::EqConstBit`, a constant chosen by a register bit).
  The claim never hashes a preimage; the block's root commits to the
  digests and the predicates tie them to the key.
- Every state key has a second commitment set, the claim-native hash of
  each preimage (`DepthKeys::state_n4`), pinned in the signed channel
  state and bound into the claim (`Program::claim_bound`). The HASH160
  commitments are used only by the key's owner in its own Move leaves;
  the claim-native ones only inside claims. Script cannot relate the
  element form of a preimage to its nibble form, and nothing requires it
  to: a mover whose two commitment sets disagree fails its own claims.
- A claim at depth `d` proves slots `d - 1` and `d`. The prior is the
  claimant's own re-commitment of the counterparty's state
  (`DepthKeys::prior`), bound to the counterparty entry's content word
  (`MoveExtras::bind_prior`); the disprove leaves read it from the
  claimant's reveal. So a party builds every claim from public data.

Consequence: an unsigned entry is not a post. The mover cannot claim or
refute with it (G7B: its inclusion claim fails at the signature
predicate), and the counterparty's timeout claim stands (G7). Cost: one
more bisection round and about a quarter more dispute size; nothing on
the stall path (GAME_PROTOCOL.md §4).

## D28. The header carries the entry's head; a stall claim reads slots from headers

Date: 2026-09-16. Context: VENUE.md §10c (depth-independent stall claims).

The fact-chain header grows from 48 to 96 bytes: `prev(20) root(20)
head(48) height(4) nonce(4)`, where `head` is the block's entry's first
48 bytes (zero for an empty block) and consensus requires `head ==
entry[..48]`. For a game entry the head is `(game, depth, mover, move,
state)`; tic-tac-toe fills eight bytes of it, chess all 48 (D30). The
header is then exactly twelve claim-native absorb steps, the head six
of them. (Built first with an 8-byte head and a 56-byte header; widened
2026-09-17 for chess, whose head must carry the whole position.)

Why: the depth-independent stall claim (`lngap_factchain::stall`) covers
`W_max` header slots with every check gated on a revealed depth register,
and it needs three facts about slots `d - 1`, `d` and `d + 1`: the
counterparty's `(move, state)`, mine, and that the next slot holds nothing
of the counterparty's. Reading them from entry streams absorbed at fixed
positions needs a register per entry root (about 28 words, over the
stack budget); reading them from header data needs none. Register file:
`D`, `P`, `E`, `E2`, `DEP`, 13 words; `3 + 14 W_max` steps with the
96-byte header (143 at W_max 10, 2,803 at 200); the same program at
every depth, verified on a mined chain at every depth.

Consequence, deliberate: the stall claim does NOT check signatures. A
slot holds an entry if its head says so; whether the entry's preimages
open the mover's key is a separate fact, and a garbage-signed entry is a
lie its victim exhibits (a claim over the entry stream and the mover's
commitments, VENUE.md §10d), not an absence. This reverses G7's reading
("a garbage signature is a stall") for the stall graph; the per-depth
star graph (D24, D27) keeps it. The exhibit hangs off the stall output as
well as the contract output (CHESS_ON_FACTCHAIN.md §7b), so the victim
never races.

Built 2026-09-17 (scenarios S1-S7, `crates/harness/src/scenarios/fc_stall.rs`):
`GraphShape::Stall` holds, per role, a stall proof and a LIE EXHIBIT off
`C` with fixed keys (four key sets; the lie exhibit is the stall claim
without the next-slot check, slot `d` the counterparty's move). Off a
stall output: the splits, the dispute chain, and the tic-tac-toe disprove
leaves spendable by the counterparty at once. Off a lie output: the
dispute chain (the liar), the same disprove leaves spendable by the
victim after `delta` (so a framed liar can dispute a fabricated exhibit
first), and the splits after `delta + delta'` (paying the liar, by the
code the victim revealed: the exhibit's default is failure). No new rule
Script: the claim binds the prior and the move to the header heads, so
the existing leaves judge the venue's move. 73 pre-signed transactions
for tic-tac-toe against 882; a stall costs three transactions at any
depth (S2A/S2B/S3); a spurious or fabricated stall proof is disputed
(S4/S6); an invalid move is disproved off the liar's stall output (S5A)
or off the victim's exhibit (S5B); a baseless exhibit pays the framed
party (S7). The party still opens star graphs when the program says so
(G1-G7B unchanged). Interim gaps: the venue signing keys are per depth
and, in the harness, generated by the world rather than exchanged in the
draft; the venue entry's move is not signed (only its state), so a miner
could alter a published move's byte, which the garbage-signature exhibit
of part 3 must cover along with the signature itself.

## D29. The n4bit Script round was never right; the flat terminal is now spent on regtest

Date: 2026-09-16. Context: D23, CLAIMCHAIN_PROTOCOL.md §3.

Found while moving the pad step of the names-registry header claim from
index 6 to 7 (D28), which made scenario N8 isolate a compression step
for the first time. The n4bit round in Script (`lngap_n4bit::script`)
had three bugs, none reachable by any earlier scenario: the S-box lookup
picked one element too deep (the nibble is consumed before the pick),
the Feistel gadget leaked one element per pair onto the altstack, and the
mixing and permutation passes rolled by depths computed for the full
stack while elements were being removed. The flat terminal leaf
(`flat_round_leaf`) additionally pushed SHA-256's 64-nibble IV for a
step starting a new n4bit message, unparked the input state on top of the
block-word signatures before verifying them, and rebuilt the state in an
order that could not be unparked. Every measured n4bit dispute number
before this date was a size, not a spend.

Fixed: the round is three park-and-restore passes (constants and S-box,
Feistel, permutation), each tested against the native pass through the
script interpreter (`script_passes_match_native_passes`,
`script_round_matches_native_round`, round counters up to 255); the flat
leaf verifies output, input and block words in witness order (block
words last-first), parks each, and absorbs with the non-rate parked.
Verified on regtest for all eight steps of a one-header claim
(`crates/apps/factchain/tests/regtest_flat.rs`): a lying output is
accepted at 8.4 to 9.4 kvB, an honest one rejected. Scenario N8 now ends
at the flat leaf (`flat_<hash>`), and the party recognises `flat_`,
`cpred_`, `ckeep_` and `ccopy_` spends as disproofs. Also fixed on the
way: the party spent the first `flat_` leaf in the tree rather than the
isolated step's (one leaf per distinct round counter).

## D30. Chess on the stall graph: the position lives in the claim's registers

Date: 2026-09-17. Context: D28, CHESS_ON_FACTCHAIN.md §3-§5.

Chess (`crates/apps/chess`, `crates/apps/chess-fc`) plays on the fact
chain under the stall graph with no chess-specific claim machinery. What
changed to make it fit:

- The header's head is 48 bytes (D28 as revised): the 8-byte content word
  and the whole 40-byte state after the move (36 bytes of position, then
  from, to, promotion, depth). A chess venue entry is 6,768 bytes: the
  head, then one 20-byte preimage per signed bit (320 state bits and 16
  move bits, the move signed as well as the board).
- The stall claim's layout is the game's (`stall::Layout`): chess has
  `D P E E2`, 30 words, `E` and `E2` the 40-byte states of slots `d` and
  `d - 1`, the depth read from `E`'s last byte (`k = 2`; 30 words is the
  most two WOTS state commitments fit under the 1000-item stack limit).
  At `W_max = 20`: 291 steps, 9 rounds; at 200: 2,811 steps, 12 rounds.
- The Move leaf reveals only the outcome code and the claim's WOTS end
  state (`MoveExtras::wots_only`); the prior, the move and the state are
  read from the end state's registers, on Bitcoin by the disprove leaves
  (`lngap_chess::leaf::leaf_over_registers`, `Field::End`, `Field::Exhibit`)
  and natively by `Program::state_from_end`. No Lamport reveal of a
  320-bit board.
- The thirteen chess leaves of CHESS_ON_FACTCHAIN.md §3 become twelve
  disprove leaves (the move-number check has nothing to check: the depth
  is bound by the claim), each a WOTS verification of the end state plus
  the leaf body over the registers, spendable by the counterparty off a
  stall output at once and by the victim off an exhibit after `delta`,
  with the exhibit values (a square, an attacker, a ray square) in the
  witness.

Measured (scenarios C1-C9, `crates/harness/src/scenarios/fc_chess.rs`,
regtest, debug build): a cooperative game costs nothing on Bitcoin (C1);
a stall proof or lie exhibit is one 6.1 kvB transaction and a stall is
settled in three at any depth (C2, C3); an illegal move claimed as a
stall proof is disproved by `disprove_chess_ray` at 6.1 kvB off the stall
output (C4), or off the victim's exhibit after the window (C5); a baseless
exhibit pays the framed party after `delta + delta'` (C6); a fabricated
stall proof is disputed through nine rounds (about 6 kvB per prover
round, 0.2 kvB per challenger pick) and disproved at the head check leaf
`cpred_h2_b5` at 6.7 kvB, about 75 kvB in all (C7): the winner takes the
pot net of roughly 25k sat of fees. 354 pre-signed transactions per game
(six claim sets, D31 included).

Where opening a game spends its time (release build, one core, measured
2026-09-17 after D31): generating a party's keys 37 ms; signing its 354
transactions 8 ms and verifying the counterparty's 9 ms; building the
graph 6.1 s, all of it the dispute chains' terminal trees (about 1.05 s
per signature-exhibit chain of 2,048 steps, 0.26 s per stall or lie chain
of 512, the inner chain's flat leaves dominating), built twice because
the channel record holds both commitment versions. Those trees depend on
the keys and the spec only, so the instance now builds them once per
claim set and shares them (`ContractInstance::terminal_stages`): 3.2 s
per party, and scenario C2 runs in 5.4 s end to end against 14 s
before and 29 s in a debug build. The Schnorr work is not the cost of
pre-signing; script generation is. The workspace's dev profile now
optimises dependencies (`[profile.dev.package."*"] opt-level = 2`), and
the harness suites are run with `--test-threads=2`: nine chess games
opening in parallel is nine cores.

Lesson recorded from C3: a stall proof is correct whenever the OTHER side
is to move and silent. "The loser refuses the fold" only produces a stall
by the refuser when the refuser is the side to move, so the scenario
resigns after an odd move. A winner who stops playing because it expects
a fold is the one who stalls.

## D31. The signature exhibit: a garbage-signed entry is a claim, not an absence

Date: 2026-09-17. Context: D28 (the stall claim checks no signature),
VENUE.md §10c, GAME_PROTOCOL.md §5 item 7.

A slot whose head names the counterparty holds an entry as far as the
stall claim can see, whatever its preimages. So a miner (or the mover)
can fill a slot with the right head and garbage preimages, and the
victim can neither prove a stall (the slot is held) nor exhibit a lie
(the head's move may be legal). The victim exhibits the signature instead
(`lngap_factchain::sig::SigExhibit`, key sets 5 and 6 of the stall graph,
leaves `sig_user`/`sig_hub` off `C`): one claim for every depth and every
signed bit, 22 words, `wots_only`, judged by the claim alone (no disprove
leaves): the liar disputes within `delta`, else the split pays the code
the victim revealed.

What the claim proves, in four phases: (1) the entry stream of slot `d`
hashes to a root `R` and carries, at chunk `i`, the digest `X` (the
stream already holds the digest of every preimage, D23, so no preimage is
hashed inside the claim); (2) the counterparty's depth-`d` commitment
`C = c[i][b]` is leaf `2 i + b` of a 16-ary commitment tree whose root is
a constant of the claim, gated on the depth register (three levels for
chess, two for tic-tac-toe; 320 bytes of siblings per level as prover
data); (3) the headers from the checkpoint to `d` link and meet the
target, header `d`'s root is `R`, its head's content word is the
counterparty's at `d` and slot `d - 1`'s is mine, and the head's bit `i`
(located by the game's `places` table) agrees with `b`, checked on the
absorb that carries it with `EqConstBit` against the index register; and
(4) `X != C` (`Pred::NeNibbles`, new). The two registers `X` and `C` are
bound to the stream and the tree respectively by gated equalities, so the
exhibitor chooses the bit but cannot choose what it compares.

Register economy: `X` becomes `P` once the stream is absorbed, `C` is
overwritten level by level after the inequality is checked up front, so
the claim stays at 22 words with `k = 2`; the per-depth roots are served
through the data store (the D19 gap) and would be draft parameters in a
deployment.

Measured: tic-tac-toe (21 signed bits, 512-byte stream, `W_max` 10) 241
steps at `W_max` 6, 8 rounds; chess (336 signed bits, 8,120-byte stream,
`W_max` 20) 1,430 steps, 11 rounds, 3,950 steps and 12 rounds at
`W_max` 200. On chain: the exhibit is 4.5 kvB (chess), the dispute leaf
0.2 kvB, the split 0.2 kvB; a baseless exhibit (the sound digest equals
the commitment) is disputed in eleven rounds and disproved at the
preamble check leaf (`simple_pre_chk`, 9.5 kvB). Scenarios S8/S9 and
C8/C9.

Left open, deliberately: tic-tac-toe's entry still signs only its state
bits, so a miner could alter its move nibble unexhibited (chess signs the
move; the fix for tic-tac-toe is a wider entry, deferred because the
star graph's slot claim absorbs the 21-chunk entry as built); and the
exhibit's data (stream, siblings) is 8 KB per step of prover data on the
dispute path, the price of absorbing the whole entry rather than a
Merkle path over it.

## D32. The PoS venue seal: an EC-OTS attestation over the unchanged 96-byte header

Date: 2026-09-19. Context: pos-factchain branch (POS_FACTCHAIN_PLAN.md);
the chain/statement/cadence pins the plan's step 1 before code.

The header is byte-identical to the PoW chain's: `prev(20) root(20)
head(48) height(4) pad(4)`, 96 bytes, 192 chunks; `height` carries the
slot and the old nonce field pads to zero. The chain is SPARSE: a block
exists only for a slot that carries an entry, slots strictly increase,
and `prev` links the previous published block. (Amended in place later
the same day after the user's challenge: no empty cadence blocks.
Absence needs no chain representation — the "not published in the
window" claim is enforced by the challenge window itself, since a
refutation that does not exist cannot be exhibited. Density was a
requirement of the D28 PoW stall claim's fixed-position header scan,
which the thin PoS claim drops.) The seal changes, not the shape:
instead of `n4bit(header) <= target`, the venue's attester reveals one
EC-OTS scalar per chunk of the header under that slot's epoch table
(epoch = slot). A block is sealed iff the attestation verifies
off-chain against the slot's table AND the old structural checks pass
(`root = entry_root`, `head = entry_head`, prev link, slot follows the
parent's). Why the header survives intact: all entry/root/head
machinery (and the 48-byte head discipline of D28) carries over
unchanged, comparison runs against the PoW sealer stay meaningful, and
the claim-side absorb machinery remains available to a hybrid.

Statement granularity: the per-chunk statements (`epoch, chunk, value`)
are as built in `lngap-ec-wots`, so one attestation over the header
lets a dispute read out ANY subset of chunk positions — the head for a
stall refutation, the root for an entry exhibit, the prev for linkage —
with no separate attestation forms. Grafting after a real equivocation
(chunk-mixing two attestations) is the known contained case: the venue
bond exceeds the damage, and one attestation per slot is honest
operation by definition (EC_WOTS.md section 6).

Registry: one epoch table per slot (192 x 16 points, 96 KB of off-chain
data per slot), published by the attester, committed by root at
contract open; disputes bind tables as per-epoch leaf constants
(EC_WOTS.md section 5 option (i)). Amortization (checkpoint epochs) is
deliberately deferred (the plan's 5.3).

Consensus for the PoC: a single attester key standing in for the FROST
group key (indistinguishable on-chain, per the ec-wots crate's design).
Equivocation = two attested headers at one slot; detected natively by
the client, slashed on-chain by the built `slash_leaf` (the bond UTXO
and the fixed-R burn path are the plan's step 5). This PoC demonstrates
the mechanism, not the security: quorum formation under partial
participation stays unexercised until the FROST iteration.

## TODO

- **N8 / anchor verification.** Omission, a corrupt root and a private fork are
  now enforced on-chain (D20, scenarios N8–N9). Still open: binding the served
  proof data to the Move, and user-side non-inclusion claims.
- **Venue (GAME_PROTOCOL.md §5).** The summons response on Bitcoin;
  variable-length claims for response windows; the equivocation leaf;
  `settle` after the deadline ignores the venue; a smaller register file
  for the claim transaction; the dispute terminal trees carry one
  predicate leaf per signature step (opening a game takes ~45 s debug).
  The stall graph (D28, D30, D31) answers the last two (13 to 30 words,
  129 to 226 transactions, about a second to open) and is played by the
  party for tic-tac-toe and chess; disputes on the venue (VENUE.md §10d)
  and the equivocation leaf are not built.
- **T9 / liveness rule.** Scenario T9 documents that an honest user who ignores
  a hub force-close during their own turn forfeits the stake (Settle pays R(s)
  = hub wins). Agreed as the PoC reading on 2026-09-06; revisit whether the
  force-move rule should distinguish "did not move" from "could not move".
