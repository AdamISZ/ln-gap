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
slot and the old nonce field pads to zero. The chain runs a CONSTANT
CADENCE by default — one block per slot, empty blocks sealing empty
slots, as venue-level reasons may prefer or even require (liveness,
ordering for non-game apps) — but density is a default, not a validity
rule: clients accept any strictly increasing slot sequence, and a gap
is a liveness event, not a validity failure. (Amended in place later
the same day after the user's challenge: the absence claim-refutation
dance needs no chain representation of absence at all — the window
enforces it, since a refutation that does not exist cannot be
exhibited. Density WAS a hard requirement of the D28 PoW stall claim's
fixed-position header scan, which the thin PoS claim drops.) The seal
changes, not the shape: instead of `n4bit(header) <= target`, the
venue's attester reveals one EC-OTS scalar per chunk of the header
under that slot's epoch table (epoch = slot). A block is sealed iff the
attestation verifies off-chain against the slot's table AND the old
structural checks pass (`root = entry_root`, `head = entry_head`, prev
link, slot follows the parent's). Why the header survives intact: all
entry/root/head machinery (and the 48-byte head discipline of D28)
carries over unchanged, comparison runs against the PoW sealer stay
meaningful, and the claim-side absorb machinery remains available to a
hybrid.

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

## D33. The refutation leaf: the EC-OTS readout tied to a WOTS re-commitment (the park)

Date: 2026-09-19. Context: pos-factchain plan step 3; D28/D31 (the stall
graph's exhibit shapes), D32 (the seal).

The refutation of "you did not publish a valid move in the window" is
one leaf doing two things: the EC-OTS readout of the slot's head chunks
(the venue attestation delivering the 48-byte head as 96 verified
nibbles — `lngap_ec_wots::readout_value_fragment`, the stack-preserving
variant: no claimed value, the values ARE the data) and the mover's
Winternitz re-commitment of the same 48 bytes, tied nibble-equal (per
chunk: the readout fragment, then FROMALTSTACK + EQUALVERIFY against
the re-committed digits, which `wots_verify` left on the stack and a
96x TOALTSTACK parked in pairing order). The re-commitment is the park:
the refutation output's follow-on leaves trust a tuple carried by the
refute key's reveal, and the refutation leaf is the only place that key
is tied to the venue attestation — pre-signed graphs have no covenants,
so run-time data crosses outputs only as pinned-key signatures (the
contract's existing re-commitment discipline, reused unchanged). The
choreography is sim-tested in script32 before regtest, per D29's
discipline (`lngap-pos` tests/sim_refute.rs, five tests).

Considered and not taken (revisit at contract integration): the
self-contained disprove leaf — re-running the readout inside each
disprove leaf instead of parking (the attestation scalars are public,
so anyone can produce the chunk signatures). That drops the refute key
set and the tie, at ~15 kvB per disprove spend against ~2.5 kvB parked;
it also changes the graph's shape (the disprove no longer needs the
refutation's output). The parked form matches D28's exhibit discipline
and keeps disproves cheap.

Measured on regtest (tests/refute.rs, the 96 head chunks of a slot-1
block): the refutation leaf 60,045 B of script, 8,303 B of witness
args, the spend 17,289 vB; sigops budget 68,828 vs 4,800 spent (14x
headroom). The disprove leaf (a toy out-of-range-move predicate over
the parked tuple) 7,306 B, its spend 2,498 vB. Negatives rejected on
chain: a re-commitment to a different tuple fails the tie; a legal
move's tuple cannot fire the disprove predicate. The +2.3 kvB of the
refutation over the bare 96-chunk readout (~15 kvB) is the WOTS tie.

Open for step 4: refute keys are per role per slot, pinned at open (the
graph's key sets grow by one); the disprove leaf's delta timelock and
party gating come with the graph integration; the two-head form of
(state, move, state') (the plan's 5.1) is resolved when the real
predicates are wired.

## D34. The PoS absence-claim graph: the leaf family and tree shapes

Date: 2026-09-19. Context: pos-factchain plan step 4 (first increment);
D33, D28.

Per depth `d`: the contract output carries the claimant's absence claim
`absent_d` (CLTV to the height after the mover's slot window, plus the
claimant's key). The claim output's tree: the mover's refutation (the
D33 leaf, the slot's epoch table as script constants) racing the
claimant's timeout splits (CSV `delta`, code-gated). The refutation
output's tree: the claimant's disprove over the parked tuple (CSV
`delta`, challenger-gated) and the mover's splits after
`delta + delta'` (code-gated, D28's "by the code the victim revealed").
No claim chain, no bisection: the publication leg is the readout, the
validity leg is the parked-tuple predicates. Built as
`lngap_pos::graph::{absent_leaf, claim_tree, refuted_tree}` over the
existing `split_leaf`/`BuilderExt` pieces.

Measured on regtest (tests/pos_graph.rs; all three paths mined, the
too-early split and the legal-tuple disprove rejected): the absence
claim and the splits are ~200 vB; the refutation 17,305 vB; the
disprove 2,532 vB. A stall costs the claim plus the split (two small
transactions); a refuted claim pays the ~17 kvB readout once.

Deferred to 4b+: the ContractInstance/draft plumbing of the per-depth
refute and code key sets; the two-head refutation (the plan's 5.1) and
with it the prior-state predicates (until then the disprove set covers
only move-in-isolation checks like out-of-range — the graph is not yet
safe against occupied-cell claims); the PoS sig exhibit (D31's analogue
needs the entry-tail binding); the party policies and the S1-S9 port.

## D35. The two-head resolution: two readouts for the PoC; digest re-derivation the plan-only long-term form

Date: 2026-09-19. Context: D34's deferral; resolves the pos-factchain
plan's open question 5.1. Locked by the user the same day.

Move legality is a predicate on (state, move, state'); slot d's
attested head carries only (move, state') — the prior state is slot
d-1's head — so the refutation stage must present BOTH heads before
the prior-state predicates (cell_occupied_i, not_on_turn, the
board-mismatch leaves) can exist on the PoS graph. Resolution: option
(a) for the PoC — two independent readouts (slots d-1 and d), ~30
kvB, no new machinery, the pair bound by the chain's own
prev-linkage; step 4b builds it together with the per-depth
refute+code key plumbing (two parked heads = two re-commitments under
per-slot keys). Option (c) — attest a 20-byte digest (40 chunks) and
re-derive the head in Script with the D29 n4bit flat-round machinery —
is the agreed LONGER-TERM form: the motivation is not refutation
weight but flexibility (other games' states may be too large to
attest whole); side effect, the 40-chunk statements shrink the
plan-5.3 epoch tables ~2.4x. (c) is PLAN ONLY: it pulls the
flat-round machinery and the absorb choreography into the refutation
path and is not to be started with the PoC. Option (b) (a
venue-attested 192-chunk per-slot transition statement) remains only
if slot attestations want to be self-contained for other consumers.

## D36. The wired PoS absence-claim graph: two-head refutation, per-depth keys, the ttt disprove family

Date: 2026-09-19. Context: pos-factchain plan step 4b; builds D34's leaf
family out to the wired graph and puts D35's option (a) on regtest.

- The two-head refutation (D35 (a)): at depth `d >= 2` the refutation leaf
  reads out BOTH slots' heads under the two epochs' tables and the mover
  re-commits `head(d-1) || head(d)` under a per-depth 96-byte WOTS pair key
  (`refute_leaf_pair`); depth 1 keeps D33's single-head leaf (the prior is
  the constant initial board). A head's slot binding is its epoch table
  (epoch = slot); `wrong_slot` additionally pins each head's word0 to the
  game's constants, so an empty slot's zero head (or a wrong-depth,
  wrong-mover entry) is itself disprovable. Measured: the pair refutation
  is 34,436 vB (leaf ~116 KB script, ~16.6 KB of args — the witness
  discount is the whole story), the depth-1 refutation 17,329 vB.
- The disprove family over the parked pair (`lngap_pos::ttt`):
  `wrong_slot`, `prior_closed`, `not_on_turn`, `cell_out_of_range`,
  `cell_occupied_0..8`, `board_mismatch_0..8`, `turn_not_flipped`,
  `status_mismatch` — 24 leaves at depth >= 2, 13 at depth 1 (the
  constant-prior leaves that can never fire are dropped, the old graph's
  PriorState::Constant discipline). Each leaf: `wots_verify`, gather the
  read digits via the altstack, compute, `OP_VERIFY`, drop the register
  file (cleanstack). Sim: every leaf agrees with its native mirror over
  legal tuples and each illegal kind, plus a wrong-claim sweep (every
  illegal transition fires some leaf — tests/sim_ttt.rs). Regtest:
  `cell_occupied_4` fires at 4,888 vB and nothing fires on a legal tuple;
  the depth-1 out-of-range disprove is 2,500 vB (leaf 7,312 B). The park
  covers the whole 96-byte pair — the sigs region included, ready for the
  deferred sig exhibit. (`code_mismatch` does not port: a PoS refutation
  carries no code reveal for it to judge. Its job moved into the splits.)
- The refuted output's mover splits are SELF-CHECKING
  (`ttt::checked_split_leaf`): CSV `delta + delta'` + 2-of-2 + the code
  reveal + `wots_verify` of the pair + `code == R(parked new state)`
  proven in-leaf (`resolution_fragment`). Without it the mover could
  reveal a false code over a legal parked tuple (no claim-carried code
  exists to mismatch against); with it a legal refutation resolves to the
  mover (R of an open state forfeits the claimant) and a false code fails
  on-chain. Measured: 4,957 vB at depth >= 2, 2,635 vB at depth 1; the
  wrong-code split is rejected on regtest.
- The wiring the bare leaf family lacked: `absent_d` is 2-of-2 (plus the
  broadcaster's `to_self_delay` when the claimant broadcasts) so the claim
  transaction is pre-signed and the claim output is pinned to the claim
  tree; the refute leaf is gated by the mover's payment key and its
  skeleton pre-signed, pinning the refutation's output to the refuted tree
  — ungated, the refutation could skip the disprove stage by spending the
  claim output elsewhere (safe for a legal move, theft for an illegal
  one). Disprove spends are the claimant's runtime transactions (the
  witness is the refutation's published reveal; nothing to pre-sign). 73
  pre-signed skeletons per game (settle + 9 x (claim, refute, 3 + 3
  splits)) — the same count as the PoW stall graph's 73, coincidentally.
- The key plumbing (the party layer's existing discipline): per depth,
  `refute` (WOTS, 96 B from depth 2 / 48 B at depth 1, the mover's) and
  `code` / `ccode` (Lamport CODE_BITS, the mover's / the claimant's),
  generated in each party's KeyStore under `key_label(id, seq, d, field)`
  and exchanged as public offers (`gen_pos_keys` / `collect_keys`); both
  parties build the same `PosInstance` (the test asserts identical trees —
  the draft's agreement property). The instance lives in lngap-pos, not as
  a `GraphShape` variant in the shared contract crate: the PoS shape has
  no claim keys and no bisection, and the venue's epoch tables are
  build-time data, not wire data. Plan 5.4 answered affirmatively: the
  refutation assembles at dispute time with no counterparty round (the
  chunk signatures are computable from the venue's published attestation;
  the mover's gate signature was pre-signed at setup).
- Discovered, NOT fixed (deliberate): the terminal-claim hole. A claim at
  a depth past the game's natural end ("mover didn't move at d" — true,
  the game was already over) splits to a false outcome, because the thin
  claim parks no state and no legal refutation exists. The fix is a
  mover-side terminal-exhibit leaf family — the same two-head machinery
  over the last move's slot pair with a `status != OPEN` gate, splits
  paying R(parked terminal state) — flagged for the next increment. Until
  then a contract left open past the game's end is unsafe against the
  loser. (The old stall claim read the state off the chain and computed R;
  the thin PoS claim dropped exactly that, and this is the price.)
- Unchanged from D34: the timeout split is 193 vB.

## D37. The terminal exhibit closes the terminal-claim hole: R(s) back on the claim path

Date: 2026-09-20. Context: pos-factchain plan step 4c; closes D36's last
bullet (the hole: a claim at a depth past the game's natural end is
vacuously TRUE and splits to a false outcome — the thin claim parks no
state and no legal refutation exists — and a game ending at the last depth
had no honest initiating leaf at all, so a loser refusing to fold was paid
by `settle`'s R(empty board)).

- The fix restores R(s) to the claim path, which the PoW stall graph had
  all along (its claim revealed R(s_d) and computed it in-leaf; the thin
  PoS claim dropped exactly that). Per depth `d` in `5..=max_depth`
  (`MIN_EXHIBIT_DEPTH`; tic-tac-toe cannot be terminal before move 5 — the
  never-fire-trim discipline), the contract output carries `exhibit_d`:
  the mover of move `d` — the last mover, never the loser in these games —
  exhibits the attested pair `head(d-1) || head(d)` under the depth-`d`
  REFUTE key, with a `status != OPEN` gate on the register file
  (`ttt::terminal_gate_fragment`: two bit picks off the file, ~40 bytes).
  The exhibit output's tree IS the refuted tree verbatim: the disprove
  family guards the exhibited move's legality, then the self-checking
  splits pay R(parked terminal state).
- The gate is load-bearing, not decorative: without it the exhibit fires
  on any attested OPEN state and R(open) pays the mover who just moved — a
  mid-game self-claim button the disprove family cannot see (the exhibited
  move is legal). With it, terminality is read off the state itself, so a
  closure rule of any complexity (checkmate, stalemate, move limits) comes
  through the same two bits; the leaf never models when the game ended.
- The exhibit REUSES the depth-`d` refute key rather than taking a new
  label: both leaves bind the same two epoch tables, so the signed message
  is provably the same 96 bytes, and the contexts are mutually exclusive
  (the contract output is spent once — `exhibit_d` on it, `refute` under
  `absent_d`'s output). WOTS one-time-ness is preserved by construction;
  the draft exchange is unchanged.
- Wiring: `exhibit_d` is `absent_d`'s shape — CLTV to after slot `d`'s
  window, 2-of-2 (pre-signed, output pinned to the exhibit tree) — not the
  refute leaf's mover-gated shape. 93 pre-signed skeletons per game (73 +
  5 x (exhibit + 3 splits)). The exhibit assembles at dispute time with no
  counterparty round (the plan-5.4 property carries over).
- Design rejection worth recording: the cheaper "pad" fix (extend the
  absence family one depth past the natural end — `prior_closed` already
  judges a post-terminal move, so a defended illegal move-10 refutation
  dies) was REJECTED once the exhibit exists: the pad keeps an
  UNCHECKED-code claim path alive past the checked one, and for a draw at
  9 the last mover strictly prefers it (claim at 10, assert "I win", full
  pot over the draw half; the loser has no counter — nothing parked to
  disprove, and the exhibit key is the winner's). The pad's only
  independent value was initiation in a world without the exhibit. (For
  games with INTERIOR draws — chess stalemate at `t` — the last mover
  could still prefer a vacuous dead-depth claim at `t+1`; the close is a
  DUAL exhibit, a second leaf keyed by the non-mover over the same pair,
  so either party can force the checked terminal resolution first. ttt
  needs none of it: draws land only at max depth. Flagged for the chess
  port, not built.)
- Sim: the gate fragment admits exactly the terminal states (win at 5,
  the draw, and two open boards), and the full exhibit leaf runs only
  when terminal (tests/sim_ttt.rs). Regtest: the exhibit at depth 5 is
  34,503 vB and pays UserWins (the wrong-code split rejected in-leaf); the
  exhibit at depth 9 (the drawn board) is 34,505 vB and pays Draw, 5,001
  vB the split; the open-state exhibit is rejected by the gate with
  everything else honest; the loser holds no depth-`d` refute key and
  cannot exhibit at all.

## D38. The validator bond: slash pair + the fixed-R key-leak burn

Date: 2026-09-20. Context: pos-factchain plan step 5.

- The bond (`lngap-pos/src/bond.rs`) is a single UTXO, script-only (NUMS
  internal key — no unilateral keyspend, so the venue cannot yank the
  stake to race a slash), with three spend families: `reclaim` (the
  validator's key + CLTV to the covered range's end plus a challenge
  window — the bond outlives the attestations it secures), `burn`
  (hash160 mirror of the attester's group SECRET, committed at setup via
  `Attester::burn_mirror`), and `slash_{slot}_{j}` — one witness-
  parameterized possession-pair leaf per (covered slot, chunk position)
  (`slash_leaf_any`, new in lngap-ec-wots: the two values arrive in the
  witness, so one leaf per chunk, not 120 hardcoded (v, v2) pairs). The
  covered slots' epoch tables are embedded as leaf constants — the venue
  registry is build-time data, the same discipline as the game graphs.
- The slash rule's semantics, pinned after a mid-build design pass: the
  trigger is two DIFFERENT values opened at one (slot, chunk). Complete
  for message-level equivocation by pigeonhole (two distinct 96-byte
  headers differ at some chunk); sound because signing the SAME value
  twice opens the same point — the leaf's v != v2 check makes the
  no-equivocation case unprovable-as-evidence, and deterministic per-
  statement secrets make honest re-attestation byte-identical.
- The burn path is real only under the fixed-R nonce discipline, now a
  variant on the attester (`Attester::new_fixed_r`, `PosMiner::
  new_fixed_r`): one nonce per (epoch, CHUNK) shared across the chunk's
  sixteen values, so a second value at a chunk is Schnorr nonce reuse
  and the group key falls out of s - s' = (e - e') * x. The extraction
  (`extract_group_key`, with `scalar_inverse` — Fermat inversion built
  only from libsecp256k1's mul_tweak, no hand-rolled field math) runs
  off-chain from public data (the chunk's nonce point is venue registry
  data; Script could not do the division anyway — no CSFS — hence the
  hash mirror). CORRECTION to EC_WOTS.md section 6's phrasing: "ONE
  nonce R per slot" cannot mean one R for the whole slot — that leaks
  the key on the first HONEST attestation (s_j - s_k across two chunks).
  The granularity is per (slot, chunk). A leak forces group-key
  rotation (the key is public; it could forge all future slots) — the
  burn is deliberately the heavier path; the slash pair is always on
  and discipline-independent.
- Regtest (tests/pos_bond.rs — a self-contained fixture, NOT a harness
  world: no channel is involved): the venue seals slot 1 carrying X@4,
  equivocates with a second attested header carrying X@0 (the client
  names it `Observation::Equivocation`); the watcher slashes at the
  first differing chunk — 343 vB, pays the watcher — and burns a second
  bond instance — 143 vB, the value to an OP_RETURN output (the bounty
  variant, paying the slasher, is one line different; "burn" is the
  plan's word and the stricter statement). [Corrected 2026-09-22 by D46:
  neither path constrains the outputs — the OP_RETURN was the spender's
  choice — and the cheater holds the evidence first; the paths are now
  behind a `race_from` CLTV and the penalty is the fee race.] Reclaim: rejected before
  expiry, mines after — 187 vB. Negatives all rejected: same-value
  "evidence" (the v != v2 gate), a sig under the wrong value, a wrong
  burn preimage. Extraction unit tests in ec-wots (inverse roundtrip,
  the leak, the default discipline's non-leak).
- Scope, per the step: the bond itself and the enforcement leaves.
  Deliberately deferred: the watcher/validator plumbing (who watches
  `PosClient::observe`, who files the spend), the rolling-bond cadence
  for an unbounded venue (the PoC bond covers a bounded slot range —
  the amortization question is the epoch-registry one already open),
  and the FROST deployment's mirror artifact (a quorum must produce
  hash160(x) at DKG time without revealing x; the PoC's single attester
  knows its own secret).

## D39. The player-equivocation leaf: both preimages of one state-key bit

Date: 2026-09-20. Context: pos-factchain plan step 6; GAME_PROTOCOL.md
section 5 item 4 (the standing gap), D38 (the venue-side analogue).

The gap, carried since the PoW graph: a mover who gets TWO conflicting
entries attested at one depth — the reorg-aided double-play — could only
be proven an equivocator off-chain. The PoS instance now carries the
per-depth `state` key the entry signature already implies (the venue
entry's signature IS the reveal of the state bits under the mover's
depth-`d` Lamport key; 21 bits for tic-tac-toe), plumbed through the
draft like the refute/code keys (`state_label`, `gen_pos_keys` /
`collect_keys`, asserted in `PosInstance::new`). The leaf family
`equiv_{d}_{i}` hangs off the contract output, one leaf per (depth, state
bit): the 46-byte `LamportExt::equivocation` gadget
(`hash160_verify(h1)` + `hash160_verify(h0)`) over that key's bit `i`,
behind the graph's standard 2-of-2 pre-sign, paying the EXHIBITOR (the
depth's non-mover) the pot. No venue data, no timelock: the evidence is
self-authenticating — only the key holder can produce a preimage at all,
and an honest run reveals exactly one per bit (the idempotent
re-broadcast of the SAME entry after a reorg repeats the same preimages,
so honest re-publication never opens the leaf). The 2-of-2 pinning makes
it watchtower-friendly: any holder of the two preimages can broadcast;
the payout cannot be redirected. One spend of C kills all leaves, so the
exhibit is a terminal resolution — equivocation is a forfeit.

- The witness is `p0, p1, sig_hub, sig_user` (sig_user on top — the
  2-of-2 checks FIRST, so the signatures ride on top of the stack, the
  claim leaf's convention; the first draft of the test got this backwards
  and the negatives passed vacuously until the positive failed).
- Sizes: the gadget is 46 bytes of script (the plan's figure, pinned in
  tests/sim_equiv.rs); the exhibit spend measured 233 vB (user double-
  played depth 1, exhibitor not the broadcaster) and 241 vB (hub double-
  played depth 2, the csv branch — the exhibitor IS the broadcaster and
  waits out `to_self_delay`, the absent-claim discipline). The smallest
  fraud proof in the graph.
- Regtest (tests/pos_equiv.rs): both directions mined with real signed
  entries (the 4b/4c fixtures used dummy sigs — unusable here, the
  signature IS the evidence); the fork block at the same slot is the
  step-5 pattern, and the client names it `Observation::Equivocation` —
  the detection-to-slash link. Negatives all rejected: the same preimage
  twice, a wrong value, the right preimages under the wrong (depth, bit)
  leaf, the early broadcaster spend; the honest keystore's refusal to
  equivocate asserted in both directions (the conflicting reveal is
  reproduced by hand from the keystore's derivation, the 4b wrong-code
  pattern).
- Graph size: 282 pre-signed skeletons per game (93 + 9 x 21). The
  contract tree's 205 leaves deepen every contract-output spend's control
  block by ~4 x 32 bytes — ~32 vB on the claim/exhibit paths, accepted.
- Chess port note: the chess entry signs move||state (SIGNED_BITS = 336),
  so the family is per (depth, signed bit) — same leaf, more bits.
- Unchanged deferrals: the PoS sig exhibit (a garbage-signed attested
  entry is a claim, D31's analogue — the equiv leaf does NOT cover it:
  garbage sigs open no key, so no equivocation), party policies (actually
  signing venue entries with the state key is policy, not graph), the
  S-port. [Superseded 2026-09-20: D41 closes the sig hole by authorship
  at refute time; no sig exhibit is needed.]

## D40. The PS scenario suite: the PoS graph measured against the PoW baselines

Date: 2026-09-20. Context: pos-factchain plan step 7;
harness/src/scenarios/pos_stall.rs.

The stall suite's PoS analogues run on regtest with REAL signed venue
entries (the D39 state key signs every entry; the venue's native check
verifies it against the claim-native mirror commitments of the same key —
the draft now carries both commitment forms). No channel wrapper: C is
funded directly and the graph is played by hand (the party policies stay
deferred; the force-close commitment, ~240 vB and unchanged by the venue
swap, is excluded from the tx tables). The suite is registered in
`scenarios::all()` so `cargo run -p lngap-harness --bin scenarios`
regenerates SCENARIOS.md with the PS sections; tests/pos_stall.rs wraps
each in `cargo test`.

Measured (pot 200k sat, 1k sat pre-signed fee per tx):

| scenario | PoS (txs, vB) | PoW analogue (txs, vB) |
|---|---|---|
| PS1 cooperative | 0, 0 | S1: 0 |
| PS2/PS3 stall at 2 / mid-game | 2, **414** | S2A/S2B: 3, ~4.5-5.0k (incl. commitment) |
| PS4 loser refuses fold | 2, **40,680** (exhibit 35.7k + split 5.0k) | S3: 3, ~5.0k |
| PS5 spurious absence claim | 3, **40,789** (claim 214 + refute 35.6k + checked split) | S4/S6: bisection, 44.2k in 20 txs (S6), ~75k worst |
| PS6A illegal move off the refutation | 3, **40,720** (disprove 4.9k) | S5A: 3, ~6.6k |
| PS6B fabricated terminal off the exhibit | 2, **40,739** (disprove status_mismatch) | no PoW analogue |
| PS7 double-played slot (venue reorg + mover double-sign) | 1, **241** (the csv branch) | NONE (the GAME_PROTOCOL 5.4 gap; closed by D39) |
| PS8 baseless terminal exhibit | gate rejects, never confirms; then 2, 414 | S7: pays the framed party |
| PS9 garbage-signed attested entry | 2, **414** (no refutation exists; D41) | S8/S9 |

The honest summary of the trade: the PoS graph moves cost from the
VALIDITY leg to the PUBLICATION leg. The common failure (a bare stall) is
~10x cheaper than the PoW stall graph (414 vB vs ~4.5 kvB — the thin
claim carries no venue proof). Anything that runs the EC-OTS readout
(the refutation or the terminal exhibit) pays a fixed ~35.6 kvB with the
D41 authorship fragment — heavier
than the PoW stall proof's ~6.1 kvB — but the bisection is gone entirely:
the spurious/fabricated-claim classes that cost 44-75 kvB and ~20
transactions in the PoW graph now cost ~40.7 kvB in 3 transactions, and
the exhibitor of a false claim is never waiting out nine rounds. PS8's
asymmetry with S7 is real and acceptable: the PoS exhibit is not a claim
(it parks attested data or aborts), so a baseless one has no on-chain
footprint to punish — the attacker pays only the failed broadcast.

The pre-signed graph is 282 skeletons per game (73 PoW stall ttt / 129
with D31 / 354 chess). PS9's deferral is the last open resolution gap:
a garbage-signed attested entry counts as held and resolves as if valid
unless its claimed transition trips a disprove — the sig exhibit (D31's
PoS analogue) remains to build. [Superseded 2026-09-20: D41 — authorship
at refute time closes the hole; PS9 runs.]

Deferred, unchanged: the PoS sig exhibit [superseded by D41], the party
policies (this suite's choreography is the specification they implement),
the chess PoS port (PC1-PC9 need the chess disprove family over the
parked pair — the 12-predicate set was never ported; that is the next
increment, not a scenario-suite item), the S-port.

## D41. Authorship at refute time: the garbage-signature hole closed without a sig exhibit

Date: 2026-09-20. Context: D40's PS9 gap (a garbage-signed attested entry
counts as a held slot); D31 (the PoW sig exhibit); the D34/D36/D39/D40
deferral ("the PoS sig exhibit needs the entry-tail binding"). Design
conversation with the user, same day.

The deferred plan was a PoS port of D31: a claim exhibiting that an
attested entry's preimages don't open the mover's key. Two design
failures surfaced in discussion. (1) Pot-flip-on-garbage is unsound: a
junk entry's author is UNATTRIBUTABLE on-chain (the head fields are bare
bytes — the venue, the mover, or anyone can have written them), so
punishing the refuter over junk can be manufactured against an innocent
Bob (junk fills his slot; he refutes and is "wrong", or stays silent and
forfeits by absence — robbed either way). (2) The user's reframe: the
refutation is an EXISTENCE claim — Bob chooses which attested entry to
stand behind — so over a publication WINDOW junk is routed around (play
a later slot) and the only punishable case is a refutation over junk Bob
chose to exhibit.

The resolution that ships: authorship at refute time, no window needed.
The refutation and the terminal exhibit carry, per parked head, an
AUTHORSHIP FRAGMENT: the witness presents the 21 preimages of that head's
mover's depth-`d` state key, and the script checks each opens its bit of
the head's claimed state (per-bit `hash160` against the key's BitCommit
constants, the bit values read off the parked register file). The check
binds the mover to the ATTESTED state (the parked head's state bits), not
to the originally published preimages — and that is what makes it
complete: "standing behind a head" now requires the mover's key over the
head's state, which IS playing the move. Consequences:

- The adoption channel collapses into play: the venue can no longer hand
  Bob a head he costlessly adopts; adopting requires his signature over
  its state, i.e. he authored the move. The transition's legality is the
  disprove family's, as before.
- The junk-block dies: a garbage-signed entry holding Bob's slot supports
  no refutation (nobody can present the authorship of its state except
  its author; Bob won't), so the absence claim proceeds — without any
  pot-flip judgment on unattributable junk. The judgment stays "the slot
  is empty", the resolution is the absence path's.
- The D39 interlock: if Bob DID sign a different depth-`d` state (his
  real move, dropped by a substituting venue), adopting the attested
  head's state is a second signature under the state key — equivocation
  evidence, `equiv_{d}_{i}` pays the victim. So honest Bob never adopts
  a substitute; collusion needs Bob-never-played, where adoption is play.
- No baseless variant exists: the evidence is the attested head's own
  claimed state bits; a well-signed entry's refutation always passes
  (idempotent re-reveal of the same bits). S7/S9's framed-party class
  does not arise — there is no claim to be baseless about.

The residual, explicitly accepted as an economic argument and NOT fixed
here: venue substitution/omission against an honest Bob who DID play —
the venue drops his real entry and seals junk; Bob can't refute the
junk's state without equivocating, so the absence path resolves against
him although he moved. Nothing attested exists to exhibit, so no leaf can
help; the venue's bond must price it (the priced-censorship line of
GAME_PROTOCOL.md section 5 item 2).

The window direction (existence-over-a-publication-window per move) is
recorded, not built: it additionally makes junk routable-around and
stiffens substitution resistance, at the cost of a variable-position
pair readout (per-window-slot leaf families or witness-selected slots)
and window-length finality delay per move. The sig hole did not need it.

Supersedes the "PoS sig exhibit" deferral (D34/D36/D39/D40's lists): the
entry-tail binding is unnecessary — no format change, no head-layout
change, no digest, no n4bit recomputation, no bisection. Measured on
regtest: the pair refutation is 35,623 vB (from 34,436), the terminal
exhibit 35,719/35,722 (from 34,503/34,505), the depth-1 refutation 17,914
(from 17,329) — the fragment is ~1.2 kvB per readout path. PS9 runs in
the suite: a garbage-signed attested entry admits no refutation (the
junk-preimage witness is rejected on-chain) and the absence claim
resolves (414 vB). Chess note for the port: the same fragment over
SIGNED_BITS = 336 covers move||state (chess's move is signed); ~6.7 KB
of witness per head — heavier, fine. [Amended 2026-09-20 by D42: "heavier,
fine" was wrong about WHERE it bites — the preimages are fine by weight
but not by COUNT: 2 x 336 preimage blocks overflow the 1,000-element
script stack under the pair readout. See D42.]

## D42. The chess port: the tied readout, the stack budget, and no exhibit family

Date: 2026-09-20. Context: plan step 7's PC gap (the chess PoS graph did
not exist — the 12-predicate chess disprove family was never ported to
the parked-pair readout); D41's chess note; D37's interior-draw dual
exhibit flag; D39's chess equivocation note.

**The disprove family is the PoW one, riding a different register file.**
`leaf_over_registers` was already parameterized by layout
(`Registers{n_nibbles, e_off, e2_off}`): the PoW claim's end state was
{240, 80, 160}; the PoS parked pair `head(d-1) || head(d)` is
{192, 112, 16} — the two heads' 40-byte states sit at head nibbles
16..96 — so the twelve kinds (all but MoveNumber, which the venue state
does not carry) port UNCHANGED, each preceded by the pair key's
`wots_verify`. Depth 1 parks a single attested head and the leaves push
the 96 constant nibbles of the initial head (game, 0, hub; null move;
the start position) between the verify and the body — the reversed
layout {192, 16, 112}: the constant-prior discipline of the old graph,
kept uniform by making the "prior" physically present as constants.
`wrong_slot` (ttt's, word0's layout is the venue's) leads the family.
Sim: every leaf against its native mirror (the certificate search over
the decoded tuple) over legal and illegal lines (tests/sim_chess.rs);
regtest: tests/pos_chess_graph.rs.

**The stack budget is the binding constraint for big states, found by
measurement.** The first chess pair refutation failed on regtest with
"Stack size limit exceeded": the witness carried 384 chunk items (sig +
value per chunk), ~394 pair-WOTS elements, 2 x 336 authorship preimages,
1 mover sig — ~1,451 elements against consensus's 1,000. (ttt fit at 863:
2 x 21 authorship is why it fit.) The vsize was fine (53,417 vB, under
the 100 kvB standardness ceiling): the constraint is the element COUNT.

The fix de-duplicates the readout: the per-chunk attested value IS the
re-committed digit the pair key's wots_verify already parks on the
altstack, so the witness stops carrying it — one element per chunk (the
possession sig), not two. `readout_tied_fragment` (ec-wots/src/leaf.rs)
takes the value off the altstack; the old form's closing EQUALVERIFY
disappears (the attested value and the parked digit are the same element,
not two witnesses compared after the fact — the tie is by construction,
and the soundness is unchanged: a digit that is not the attested value
selects an anticipation point whose secret nobody holds). The witness
shapes change (`refute_witness`, `refute_witness_pair` take the chunk
SIGS only; the pair's authorship blocks are a slice in consumption
order). −192 elements on every readout path, both games; the ttt pair
refutation measures 35,535 vB (from 35,623) and the whole ttt suite
re-passes under the new readout (pos_graph.rs), INCLUDING a new
regtest negative (path H) for the mismatched-recommitment case the
sim_refute suite covered with the old form — the sim's CHECKSIG stub
cannot see the point selection, so that negative is testable only with
real sigs (the sim tests now say so; the out-of-range-value negative is
unconstructible in the tied form and was removed).

**Chess authorship is new-head-only in the pair refute.** Even after the
de-dup, 2 x 336-bit blocks don't fit (192 chunk sigs + ~394 WOTS + 336 +
1 = ~923 elements fits; 1,259 does not). The refute/exhibit gate checks
the NEW head's 336-bit state key (the judged move's author) and not the
prior head's. Why this is not a weakening: the prior head's authenticity
is inductive — an unauthored head at d-1 supports no refutation at d-1's
own absence claim (its garbage signature opens no key), so a game never
continues past one; and in the venue-substitution residual D41 accepted
(the venue drops the real d-1 entry and seals junk), both forms lose the
honest mover at d identically — the both-heads form's extra coverage was
belt-and-suspenders over the accepted residual. Tic-tac-toe keeps
both-heads (its 2 x 21 fit regardless). The depth-1 refute is single-head
for both games as before. The venue entry format is UNCHANGED (the entry
signs the full 336 signed bits; only the refute's gate narrowed).

**Chess has no terminal-exhibit family** — this resolves D37's flagged
interior-draw dual-exhibit note with "not needed", on the record: chess
terminality is not a state field (mate/stalemate is move-existence, not
Script-computable), and none is needed. Mate at depth t leaves the mated
side with no legal move: the absence claim at t+1 is unanswerable (any
refutation is an illegal transition, disproved) and races ahead of any
dead-depth false claim at t+2 by CLTV order. The last-depth corner is
excluded by chess-fc's standing assumption that the game ends before
w_max. Interior draws do not exist under the PoC's stalemate-loses-by-
stall reading (chess-fc's deferral: a stalemated party has no move and
loses by stall). The checked split's resolution is then trivially
in-script: `code == 1 - side` off the parked new state's side nibble
(state byte 32's low nibble = head digit 81) — open state: the side to
move (the claimant) forfeits; mate: the mated side loses; stalemate the
same under the PoC reading. The Draw split leaf is present but never
satisfiable on this graph: draws remain cooperative-only (the fold).
(For tic-tac-toe the D37 exhibit family stands as built.)

**The two-element exhibit's witness order was wrong upstream and no one
had fired one.** The contract crate's `DisproveSpec::witness_args_with`
appends the exhibit AFTER the end-state signature in consumption order,
so the reversed stack bottoms at the LAST exhibit element — the two
2-element kinds (CastlingAttacked, KingAttacked) read their (crossed,
by) / (king, by) swapped. The PoW path never fired one (the C-suite's
one disprove was a Ray, one element). The port fires chess_kingattacked
on regtest (PC9 / pos_chess_graph path E2): the PoS disprove witness
carries the exhibit in Kind order, deepest-first (sim_chess.rs's note
pins it). Not fixed upstream in this commit — recorded here; the PoW
graph's two 2-element leaves are inert until either fixed or
deliberately fuzzed.

**Fee sizing is real now.** The chess pair refutation is 43,801 vB
(dedup + new-head authorship, down from the broken 53,417), the depth-1
refutation 26,666 vB, the disproves ~4.9-5.0 kvB (the pair WOTS reveal
dominates them), the timeout split 193 vB, the equivocation exhibit 265
vB. The 1k-sat placeholder presign fee sits under the 1 sat/vB relay
floor for the readout paths (true of ttt's 35.5 kvB all along; the
generateblock harness path tolerates it, the mempool path does not) —
the chess instances and the PC suite run with a 60k-sat per-hop fee so
the negatives are script-meaningful, not fee-masked. A real deployment
sizes the pre-sign fee to the largest skeleton (the pair refute).

Measured (the PC suite, real signed entries, regtest): PC2/PC3 the bare
stall 438 vB in 2 txs; PC4 the fool's-mate terminal path 437 vB in 2;
PC5 the spurious claim 48,940 vB in 3; PC6 the illegal move disproved
(chess_ray) 48,993 vB in 3; PC7 the double-played slot 265 vB in 1;
PC8 the garbage-signed entry 438 vB in 2; PC9 the mated side's illegal
answer disproved (chess_kingattacked, the 2-element exhibit) 49,083 vB
in 3. Graph: 2,753 pre-signed skeletons per chess game (settle + 8 x
(claim, refute, 3+3 splits) + 8 x 336 equiv; no exhibit leaves) vs 282
for tic-tac-toe; the contract tree's 2,690+ leaves deepen every
contract-output spend's control block by ~4 x 32 B, accepted. Compared
with the PS baselines the chess readout costs ~9.3 kvB more per
refutation path than tic-tac-toe's — the 12-kind scripts (~14.6 kB
each, the pair WOTS verify dominating) are spent only on the disprove
branch, and the bare stall stays at ~10x under the PoW S6 path. PC1-PC9
pass (tests/pos_chess.rs; the suite runs nine fresh regtests at
--test-threads=2, ~28 s).

Deferred, unchanged from D40's list except as closed here: the party
policies (the suite's choreography is the specification they implement),
the S-port. The PS9-equivalent for chess (PC8) runs. The D37 exhibit
family is tic-tac-toe-only per the above; if a future game has an
interior-draw settlement rule that is NOT loss-by-stall, it needs the
D37 note's dual exhibit revisited.

## D43. WOTS-form authorship: the entry signature, the tied state-key verify, the per-depth equivocation leaf

Date: 2026-09-21. Context: POS_DISPUTE_SIZES.md (written same day) —
the two D42 size warnings (the chess pair refute at ~923 stack elements,
92% of the 1,000-element consensus limit; 43.8 kvB readout paths) plus
the 2,753-skeleton chess graph, 2,688 of it the per-bit equivocation
family. This is that note's Lever 1, landed the day it was recommended.
PS/PC suites, pos_graph / pos_chess_graph / pos_equiv all re-pass on
regtest under it.

**The venue entry's `sigs` region IS the state key's WOTS signature.**
The per-depth state key becomes a Winternitz key over the entry's
authorship message (tic-tac-toe: the 3 state bytes, 6 + 2 digits; chess:
the 40 state bytes then the move low-first, 84 + 3 digits), generated
under the unchanged `state_label` discipline via the keystore's new
`generate_wots(label, game.state_bytes())` / `sign_wots` / `wots_public`
— the one-time discipline moves there: a second signature of a
DIFFERENT message is refused, the same message re-signs idempotently
(the venue's own re-seal is safe). The entry carries the signature's
hashes: 160 B per ttt entry (was 420), 1,740 B per chess entry (was
6,720). The entry wire format is sig-count-agnostic now (content, then
the 20-byte elements) so the PoW graphs' Lamport form is untouched.
`refute::check_entry_sig` is the anyone-runs-it native check (WOTS
verify of the entry's sigs against the authorship message).

**The authorship fragment is the tied WOTS verify.** `wots_verify_tied`
(winternitz.rs): the message digits are PICKed off the parked register
file — the parked head's digits ARE the signed region, so the digit
values never ride the witness; only the reveal hashes do, below the
file (the D42 readout's tie, applied to authorship). This is where the
D42 stack squeeze actually came from: the 336 authorship preimages were
336 witness elements AND ~30 KB of script; the tied form carries 87
hashes and the file supplies the digits. ttt keeps both-heads
authorship; chess KEEPS the D42 new-head-only narrowing (the migration
makes both-heads affordable again, ~180 elements — the narrowing's
inductivity argument stands on its own, so restoring it is a choice,
not a necessity, and was not exercised).

**The equivocation family collapses to one leaf per depth** (graph.rs
`equiv_leaf`; the plan's step 6 rebuilt). A WOTS signature's reveal is
forced given the message, so two distinct valid signatures under one
depth's state key are the double-sign proof on their face: the witness
carries both full signatures (`wots_wire` of the first, then the
second) plus the standard 2-of-2; the leaf verifies both and requires
the two parked message vectors to differ digitwise. Idempotent
re-broadcast of the SAME entry re-presents the same signature and never
fires the differ. Skeletons: 282 -> 102 per ttt game, 2,753 -> 73 per
chess game; the contract tree's ~2,690 leaves collapse likewise, so
every contract-output spend's control block shrinks (~12 -> ~7 hashes).
Presigning is ~28x lighter. The rare path pays for it: the exhibit
grows 233/241 -> 589/597 vB on regtest (two full signatures ride the
witness) — still far under every dispute path.

**The stacked-verify choreography bug, recorded for the next leaf
author.** Two plain `wots_verify` calls in a row cannot see both
witness blocks: the first verify parks its recovered message digits on
the stack TOP, burying the second signature's wire block beneath them.
`equiv_leaf` parks the first vector to the ALTSTACK between the two
verifies and restores it after (the differ then reads [first vector
below, second on top]: b_j at depth m-1-j, a_j at 2m-1-j). Found by the
migration's first honest-case regtest spend (OP_EQUALVERIFY failure
while both signatures verified natively — the witness was reachable,
the second verify's inputs were not). The sims never covered this leaf
(no sim_equiv for the player leaf; the coverage is pos_equiv.rs's two
mined directions plus the same-signature / corrupted-signature /
wrong-depth negatives).

Measured (regtest, post-migration). ttt (pos_graph): pair refute
34,760 vB (was 35,535), depth-1 refute 17,488, terminal exhibit 34,834.
Chess (pos_chess_graph): pair refute 36,545 vB (was 43,801), depth-1
19,471, disprove chess_ray 4,947, chess_kingattacked 5,038. The PC
suite: PC5 41,627 vB in 3 (was 48,940); PC7's double-play 4,611 vB in 1
(the 2 x 87-digit chess exhibit at the suite's 60k-sat fee; was 265);
PC9 41,771 in 3. The ttt equiv exhibit is 589 vB (597 in the csv
branch, pos_equiv.rs). Levers 2-4 of the note remain open and
unaffected: the venue-receipt regime decision (the ~4.6x refute cut at
a venue-model price), the digest seal (gated on TODO #1, and the only
move that lifts the 40-B state cap), the optimistic venue-tie fallback.

## D44. The counter: a thin claim is answerable by the thin claim one depth back

Date: 2026-09-22. Context: a review of the PoS chess graph (2026-09-21)
found that the thin absence claim (D34) has no notion of DUENESS, and
demonstrated the consequence on regtest. Design conversation with the
user the same day; the fix landed 2026-09-22.

**The hole.** `absent_d` is CLTV + 2-of-2 and asserts no venue content.
Nothing in it says the claimant itself moved at `d - 1`, so a staller at
`d - 1` can claim `absent_d` — "you did not move at `d`" — which is
vacuously TRUE: the victim's turn never came. The victim cannot refute
(no attested head of its own at `d` sits on a valid head at `d - 1`; an
attempt over the empty slot's zero head parks a `wrong_slot` violation).
The graph's only separation of the honest claim at `d - 1` from the
vacuous one at `d` was one block of CLTV order, and the broadcaster's
`to_self_delay` CSV on the honest claim (the victim is the one who
force-closed) inverts it. Probe on the PC fixtures: the hub stalls at 2
and claims `absent_3`; at height `btc_open + 5` BOTH the user's
`absent_2` and the hub's `absent_3` were mempool-accepted (a race even
at regtest's 6-block delay); the hub's mined, and after `delta` its
timeout split paid it the pot. Not chess-specific: the graph is shared.
The PoW stall claim was immune by construction (D26: "my valid move `d`
in its slot; the counterparty's slot `d + 1` passed") — the thin claim
dropped exactly that, and D36/D37 saw only its terminal-depth instance
(the exhibit); D42 relied on "CLTV order" for the mate case.

**The fix.** From depth 2 the claim output A_d carries one more leaf,
`counter` (graph.rs `counter_leaf`): the mover's thin claim one depth
BACK — "you did not move at `d - 1`" — which is exactly the negation of
the claim's dueness. 2-of-2 pre-signed, no timelock (it must beat the
claimant's timeout splits at CSV `delta`, like a refutation; no
`to_self_delay`, that guards the contract output against a revoked
commitment). The counter output's tree is the depth-`d - 1` CLAIM tree
verbatim (`PosInstance::counter_tree`): the claimant's refutation by the
`(d - 2, d - 1)` pair readout racing the counter-claimant's timeout
splits; that refutation's output is the depth-`d - 1` refuted tree. The
depth-`d - 1` refute, code and ccode keys are reused in a third mutually
exclusive context (the contract output is spent once — the D37
argument). Skeletons: per depth from 2, +8 (counter, refute, 3 + 3
splits); ttt 102 -> 166, chess 73 -> 129. No new leaf bodies; no readout
or disprove changes.

**Why one level closes it.** A counter is answered by a positive fact or
not at all: the claimant's only reply is the readout of its own attested,
signed head at `d - 1`. A FALSE counter (the claim was due) is refuted by
that readout and then judged by the ordinary disprove family, or paid by
the checked split — R(head `d - 1`) is "side to move forfeits", the right
result for a real stall at `d`. A TRUE counter means the claim was never
due, which should lose regardless of what happened earlier: the only
party a true counter hurts is a claimant who claimed a depth that was not
due, and that party always had a due claim at a shallower depth. So the
counter output's tree carries NO counter of its own; the honest strategy
is "claim the depth right after your own last published move", and any
claim ahead of it is countered for ~180 vB and cannot be defended. The
counter is not a new instance of claim/refute: the refutation of a
counter is the existing pair readout, so the chain of thin claims never
exceeds two.

**Alternatives rejected.** (a) The PoW shape — the claim carries the
claimant's own move (the `(d - 2, d - 1)` pair readout) and the claim
output grows the disprove family: no regress either, but every honest
absence claim becomes a ~36 kvB readout and the bare stall loses D40's
~10x. (b) Channel-level dueness — per-move channel updates presigning
only the due claims: a refused update leaves the pot stuck until
`settle`, which pays R(empty) under the T9 rule, so the refusal is the
attack. The counter keeps the honest bare stall at two small
transactions and every path trustless.

**What it also settles.** The mate race of D42 (the mated side's
dead-depth claim at `t + 2` racing the winner's `absent_{t+1}` on CLTV
order) is gone: the winner counters "you did not move at `t + 1`", true
and unrefutable. The D37 terminal exhibit stays for tic-tac-toe: the
last-depth corner (`absent_{max+1}` does not exist) still needs it.
Untouched: the D41 venue-substitution residual (dueness is a player-side
property) and the malformed-state hole recorded in the same review (a
signed chess entry with from-square 255 fails every kind leaf's board
read and the checked split pays; a well-formedness leaf is the fix, not
built here — landed the next day as D45).

**Measured (regtest, 2026-09-22).** The counter 178 vB. Chess
(pos_chess_graph paths F1/F2): the staller's zero-head refutation of a
true counter mines at 36,534 vB and `wrong_slot` kills it at 4,879 vB;
declining, the victim's timeout split off the counter is 193 vB; a false
counter to a due claim is refuted at 36,545 vB and the checked split
pays at 4,894 vB. Suites: PC10 and PS10 (the claim-ahead countered) 550
vB in 3 transactions; PC11 41,796 vB and PS11 40,058 vB in 4 (the false
counter refuted); all of PC1-PC11 and PS1-PS11 re-pass, SCENARIOS.md
regenerated over the full suite; pos_graph / pos_equiv / pos_bond /
refute re-pass. Fee note: the
deepest path is now four pre-signed hops (claim, counter, refute, split),
so the pot must cover four presign fees — the pos_chess_graph fixture's
pot went 200k -> 400k sat at its 60k-sat fee; the suites' pots already
did.

## D45. The chess well-formedness leaf: the judge's notion of a valid entry is a superset of the client's

Date: 2026-09-22. Context: the second finding of the 2026-09-21 review
of the PoS chess graph, recorded as "untouched" in D44; landed the next
day.

**The hole.** chess.rs's module doc claimed that a malformed-but-attested
state "self-griefs": no disprove fires, but the `1 - side` split cannot
fire either. That holds only when the SIDE nibble is the malformed field.
With a well-formed side and the from-square byte (state byte 36) set to
255, every one of the twelve kind leaves fails at the preamble's board
read (`OP_PICK` with a negative depth — "Operation not valid with the
current stack size" on regtest) and `wrong_slot` does not fire, while
the mover's checked split passes `code == 1 - side`. Regtest probe: the
hub seals a SIGNED entry with from = 255, the user (whose client cannot
decode it) claims absence, the hub refutes, no disprove is spendable
under any exhibit, and the hub's split mined and took the pot. A
related, smaller class: fields the native decoder rejects but the script
never reads (the castling byte's high nibble, state byte 38's low
nibble, the depth byte, word1) — a legal move with garbage there is
upheld on-chain but undecodable off-chain, so an honest client claims
absence over it and loses.

**The fix: `chess_malformed`** (chess.rs `malformed`; `is_malformed` the
native mirror), the last leaf of the chess disprove family, over the
parked NEW head. Pure nibble arithmetic on the register file — it never
errors, so a head that breaks the kinds' board reads still has a live
disprove. It fires iff any of: a from/to square byte >= 64 (the high
nibble >= 4); the castling byte's high nibble != 0; state byte 38's low
nibble != 0; the depth byte != the layout's depth; a promotion code of 1
or >= 6; word1 != the move rebuilt nibble-wise from the state's
from/to/promotion (`to_u16() << 16`: digit 8 = the promotion nibble, 9 =
`to >> 2`, 10 = `(to & 3) << 2 | from >> 4`, 11 = `from & 15`, 12..15 =
0 — the two `split4` steps are the only arithmetic). Everything else the
client's `ChessEntry::decode` rejects is judged by a kind that does not
error on it: board nibbles by `Board`, the side by `Side`, the en-passant
square by `EpField`, the castling low nibble by `CastlingField`, invalid
promotion pieces also by `Promotion`. So the set of entries the chain
upholds is now a subset of the set the client decodes: a client never has
to claim absence over an entry it cannot read and then lose the
refutation.

**The principle worth keeping.** The on-chain judge defines validity; the
client must accept everything the judge upholds. The previous doc had it
backwards (the client was stricter), and "the mover self-griefs" was the
wrong conclusion because the refuted output's split is keyed to one
nibble, not to the whole state being sane. When a leaf family's native
mirrors are "defined on well-formed encodings", the family needs one
total leaf whose job is well-formedness, and its coverage must be the
decoder's rejection set minus what the other leaves provably catch
without erroring.

**Sim and regtest.** sim_chess.rs `malformed_heads_are_disprovable`: a
21-case sweep (both square bytes at 64 and 255, the castling high nibble,
byte 38's low nibble, the depth byte, promotion codes 1/6/7, each word1
digit group, plus the kind-judged fields) asserts the entry decode
rejects each case (bar the castling low nibble, which it accepts), that
`is_malformed` matches the intended field list exactly, and that some
leaf fires on every case, with the kinds' exhibits searched as a
challenger would since a rejected head has no native exhibit to copy; a
legal head fires nothing (the existing safety sweeps now include the
leaf). Regtest (pos_chess_graph path H; PC12): the from = 255 entry is
refuted (36,545 vB), `chess_ray` fails with the stack error, and
`chess_malformed` mines at 4,908 vB, the user taking the pot (PC12:
41,641 vB in 3 transactions; SCENARIOS.md regenerated over the full
suite); path B checks the leaf does not fire on a legal, well-formed
head. The tic-
tac-toe family needs no analogue: its 3-byte state has no field the
native side rejects that the leaves do not judge (`cell_out_of_range`
covers the move byte; every nibble of the state word is read).

## D46. The bond's evidence paths are a fee race, not a burn; prior art for the venue

Date: 2026-09-22. Context: a read of Robin Linus's *Coins: A Billion
Bitcoin Users* (January 2020, coins.github.io/coins.pdf) and its
published successor *Stakechains* (Linus and Tse, CoDecFin 2022); D38
(the validator bond); the incentive discussion of the same day
(ATTESTATION_FEES.md, local). Agreed with the user.

**Prior art.** The PoS venue's base layer is Coins/Stakechains: validators
lock bitcoin in collateral outputs on Bitcoin, sign sidechain blocks with
nonce-committed one-time signatures so that two conflicting signatures
leak the key, checkpoints in Bitcoin prevent long-range attacks, the
validator set is read off Bitcoin's UTXO set, and a majority-signed block
is economically final. D32/D38 are that design with per-chunk one-time
signatures (EC-OTS) instead of per-block ones. What is not in it, and is
this project's own: the venue never settles value and has no asset (his
section 4.2 "altcoin problem" is the reason the attestation-fee design
exists); the attestations are Bitcoin-legible, so contracts consume the
chain's content in Script (the readouts, the claim/refute/disprove
graphs, the certificate predicates); and censorship, which Coins does not
treat. His section 5.1 (commit to the next nonce by signing it with the
previous signature) is a candidate answer to the registry-amortization
question (plan 5.3). His section 2.3 is the burn analysis below, six
years early.

**The hole.** D38 described a `burn` path ("the value to an OP_RETURN
output") and a `slash` path ("pays the watcher"). Neither constrains the
spending transaction's outputs, because Script cannot without a covenant:
`burn` is `hash160_verify(mirror)`, `slash` is two possession signatures
over the spend's sighash, and both are spendable by anyone who holds the
evidence to ANY output. The OP_RETURN in the test was the spender's
choice. And the evidence is held first by the cheater — it produced the
attested scalars, and under fixed-R it computes the leaked key — so as
built the equivocating validator could spend its own bond back to itself
before any watcher moved. The bond deterred nothing by itself. Nobody had
written this down.

**The options** are Linus's: a covenant (CTV or the like) makes a burn
exact; a presigned burn transaction co-signed by a key whose holder then
deletes it (a federation, or the FROST group's DKG ceremony producing a
one-shot key) emulates one, with trust in the deletion; or the FEE RACE:
since anyone can spend, competitors bump each other with RBF until the
whole bond is miner fee, which is an economic burn. Any gate keyed to the
validator's own key is useless, since after a fixed-R leak the cheater
holds that key too; per-contract victim payees do not fit a taptree fixed
at bond creation.

**Chosen: the fee race, engineered.** Every evidence leaf (`burn`, every
`slash_{slot}_{j}`) now carries `CLTV race_from = expiry - race_window`
(`BondSpec::race_window`; the window wide enough for watchers and
miners). The race opens LATE on purpose: the capital then stays locked
until near the reclaim in every outcome, exactly as under a plain
timelocked bond, so the race can only take the principal and never hand
it back early — its worst case (the cheater mines the eligible block) is
the plain lock's every case, which is what makes the evidence path a
free option on the principal rather than a trade (an early race height,
as the first cut of the patch had, would let a winning cheater recover
its capital before expiry). This removes the cheater's head start: the
attestations are public data on the venue for the whole delay, anyone can
build the spend, and at the race height the winning spend is the one
paying the most fee. A miner takes the entire bond as fee by including
its own spend (one zero-value OP_RETURN output, everything to fee), so
the cheater keeps the bond only by mining the first eligible block
itself. The spends already opt into RBF (`Timelock` sequences are
`ENABLE_RBF_NO_LOCKTIME`). Submitting a full-fee spend needs
`maxfeerate=0` at the RPC; miners have no such limit.

**The economics, honestly stated.** With hashpower share `p`, bond `B`,
gain `G` and `V` the present value of the validator's future fee income,
the attacker's expected value is `G − (1 − p)·B − V`; deterrence needs
`(1 − p)·B + V > G`. At `p = 0.2` the bond is sized at 1.25× the gain, not
1×. `p` is the attacker's OWN hashpower: a bribe to include a low-fee
self-payment must beat the full-fee competitor, which already hands that
miner 100% of `B`, so bribery is dominated, and a pool doing it does it
in public (a low-fee spend in the block while a full-fee competitor sat
in every mempool). Watchers earn nothing from the race; the reporting
incentive Ethereum buys with its 1/512 whistleblower reward is replaced
here by miners' own incentive, which is stronger but means the
assumption is "some miner or full-fee broadcaster is watching the venue",
reasonable with a race delay of days. The residual is `p` and there is no
fix for it without a covenant. Ethereum, for the record: 1/32 initial
penalty burned, 1/512 to the proposer, a correlation penalty up to 100%
of the balance when many are slashed together, forced exit; all burns are
balance decrements, which Bitcoin has no analogue of.

**Why G is small for the games, by construction.** A venue equivocation
on its own moves no money on the game graphs: the graph pays only on a
PLAYER's signature (an unsigned substituted head supports no refutation,
D41), and a player who signs both versions is convicted by the
equivocation exhibit the moment the second signature is used on-chain
(D39/D43), even under a partitioned equivocation. Compensation is the
player's forfeit; the bond is deterrence for consensus integrity
generally. `G` is real for a registry, where an equivocated slot can
rewrite a name's owner and no player forfeit compensates anyone. For
such apps the per-contract venue stake — the venue funds an output at
contract open whose slash leaves are `evidence + 2-of-2 of the players`
with a players-presigned skeleton, so the payee is fixed at open and the
cheater's keys are useless — is the covenant-free alternative that
compensates rather than burns, at the cost of venue capital and a signing
round per contract. Recorded as an option, not built.

**What the bond still does not cover** is unchanged: censorship and
substitution are unprovable and never slashable under any burn
mechanism; they rest on the positive incentive (the fee stream) and on
forced inclusion / windows.

**Measured (regtest, tests/pos_bond.rs).** An evidence spend before
`race_from` (the fixture's window puts it 8 blocks after funding, 42
before expiry) is rejected; the slash after it mines (paying the watcher,
344 vB). The burn as a race: the cheater's low-fee self-payment through
the mirror leaf enters the mempool first, the watcher's zero-value
OP_RETURN spend with the whole bond as fee (167 vB) replaces it (RBF),
the next block carries the watcher's, the self-payment never confirms,
the bond's 100,000 sat went to the miner. One practical detail for any
burn broadcaster: with an EMPTY OP_RETURN the spend is 61 bytes and Core
refuses it as `tx-size-small` (the 64-byte-transaction guard, enforced
whatever the standardness flags); the OP_RETURN needs a few bytes of
payload. Negatives (same value, wrong value, wrong preimage, early
reclaim) unchanged; the reclaim after expiry pays the validator. D38's
"burn … the value to an OP_RETURN output" is superseded by this entry's
description of what the paths enforce.

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
