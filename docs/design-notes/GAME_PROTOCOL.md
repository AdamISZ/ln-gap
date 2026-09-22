# Tic-tac-toe on the fact chain: ForceMove with a venue

Branch `ttt-venue`, 2026-09-14. The game is played on the fact chain (the
*venue*) and settled in a channel. Bitcoin sees a game only when someone
stalls or lies. The design record is docs/planning/VENUE.md; this is what
was built and measured.

    cargo test -p lngap-harness --test fc_game
    cargo run -p lngap-harness --bin scenarios -- G1   # etc.

## 1. What this validates

The game-theory point of the venue design: escalation to Bitcoin costs
Lightning's floor (one force-close, one transaction on the contract
output, one settle) whenever the counterparty merely *stalls* or refuses
to fold, at any depth of the game; the multi-stage dispute machinery runs
only when someone *lies*, and then the liar pays. A losing party's best
response is therefore to resign.

| scenario | what happens | on Bitcoin |
|---|---|---|
| G1 | cooperative game, folded off-chain | nothing |
| G2A | the hub stalls at move 2 | commitment, `move_1` (timeout claim), `split_1_UserWins` |
| G2B | the hub stalls at move 6 | commitment, `move_5`, `split_5_UserWins` |
| G3 | the loser refuses the cooperative fold | commitment, `move_7` (terminal claim), `split_7_UserWins` |
| G4 | a spurious timeout claim (the hub ignores a valid move 3) | commitment, `move_2`, the user's refutation `move_3` with its inclusion claim, `r2/split_3_UserWins`: the claimant forfeits |
| G5 | the hub publishes an invalid move and claims it | commitment, `move_4`, `disprove_cell_occupied_0` |
| G6 | the hub claims a move it never published | commitment, `move_4`, `d4/dispute`, 8 bisection rounds, re-commitments, `simple_ent_root`: disproved at the root predicate |
| G7 | the hub publishes move 4 with garbage in place of its signature, then stalls | commitment, `move_3` (timeout claim), `split_3_UserWins`: an unsigned entry is not a post |
| G7B | the hub answers the timeout claim with its garbage-signed move | `move_3`, refutation `move_4`, `r3/d4/dispute`, 8 rounds, re-commitments, `cpred_oe_s0a`: disproved at the signature predicate |

G2A and G2B are the point: three transactions whether the stall happens at
move 2 or move 6. The old tic-tac-toe (docs/design-notes/SCENARIOS.md, T-scenarios)
plays the rest of the game on Bitcoin move by move after a force-close.

## 2. The protocol

**Venue.** One fact-chain block per Bitcoin block (a harness convenience).
The block `d` after the contract opened is *slot* `d`, and move `d` must
sit in it: a move published later is a stall. The header is 96 bytes and
carries the entry's first 48 bytes (D28; widened from eight for chess,
D30). The entry is 428 bytes:
8 bytes of content, `(game_id, depth, mover, move, state)`, followed by the
mover's 21 Lamport preimages for the state bits, its signature. A block's
root is a two-level hash (D23): the content, then the claim-native digest
of each 20-byte chunk. Anyone verifies a published move against the
mover's pinned commitments; an entry whose preimages do not open the key
is not a move (G7). The counterparty never needs the mover's secrets: a
claim re-commits the counterparty's state under the claimant's own key
and proves, from the venue alone, that the counterparty published exactly
that state, signed.

**Contract.** `ttt-fc:{game_id, checkpoint, btc_open, grace}`, opened once
at the empty board with each side staking `STAKE + RESERVE` (50k + 15k
sat) and folded once with the result (`Change::Fold`, a distribution both
sides check against the venue). The reserve returns on a fold and goes to
the winner on any on-chain resolution, so stalling costs the staller more
than resigning. The pre-signed graph is a *star* (`GraphShape::Star`):

- off the contract output `C`: `settle` (after the contract's deadline,
  `R(empty board)`), and a claim leaf `move_d` for every depth `d` in
  `1..=9`;
- a claim at depth `d` (prover: the mover of move `d`) reveals the
  counterparty's state at `d - 1` under the prover's own re-commitment
  key, move `d`, the new state and the outcome code `R(s_d)`, and
  commits a *slot claim*: the fact-chain header chain from the checkpoint
  to slot `d`, the counterparty's entry in slot `d - 1` and the prover's
  in slot `d`, with predicates (§3). `R(s_d)` is the result
  if `s_d` is terminal and "the party on turn forfeits" otherwise, so a
  claim at a non-terminal state is a *timeout claim*. Its leaf carries
  `CLTV btc_open + d + 1 + grace`: the counterparty's slot passes first;
- off `C'_d`: the 28 tic-tac-toe disprove leaves against move `d`, the
  `dispute` leaf opening the bisection against the slot claim, the
  splits, and one *refutation* `r{d}/move_{d+1}`: the counterparty's move
  `d + 1` with its own slot claim, revealing the claimant's state as prior;
- off the refutation's output: disproofs and the dispute against move
  `d + 1` and its claim, and the splits. No further move: a refuted
  timeout claim ends with `R(s_{d+1})`, the claimant on turn, forfeiting.

The graph has 882 pre-signed transactions (9 claims + 8 refutations, each
with 3 splits and a dispute chain) and opens in about 45 s (debug build;
most of it is building the dispute terminal trees, which carry one
predicate leaf per signature step).

**Escalation.** A party whose opponent's slot passed without a valid move
queues a claim; the party force-closes when the claim's `CLTV` is within
`to_self_delay`, then makes the claim. A party that sees a claim against
a state it has moved from answers with its published move (the move
policy finds it by prior state). Everything else is the existing
machinery: disproofs, bisection, timeouts, splits.

## 3. The slot claim (`lngap_factchain::slot`)

A 17-word register file: `D` (the hash state), `P` (previous digest), `R`
(the current header's root field), `E` (my entry's `(move, state)` word),
`E2` (the counterparty's). Per header: 7 absorbs of 16 nibbles with
`EqNibbles` predicates tying the header's `prev` field to `P` and copies of
its `root` field into `R`, a zero pad block, then a simple step checking
`LeTargetBe(D)` (proof of work) and copying `D` to `P`. After header
`d - 1` the counterparty's entry, after header `d` mine: 64 absorbs of the
512-byte entry stream. The first block is the content, with `EqConst` on
`(game_id, depth, mover)` and a copy of `(move, state)` into `E2` or `E`.
The next 63 blocks are the 21 digests of the entry's chunks, the mover's
preimages, each checked with `EqConstBit`: the digest must equal the
commitment `h(p0)` or `h(p1)` pinned for that state bit, selected by the
bit's value in the content word already sitting in `E2` or `E`. Then a pad
block and `ent_root: EqNibbles(D, R)`. `8 d + 66` steps at depth 1,
`8 d + 132` from depth 2, padded to a power of two: 128 steps (7 rounds)
at depth 1, 256 (8 rounds) from depth 2 to 9.

The claim never hashes a preimage. The block's root already commits to
the digests of the entry's chunks; the predicates tie each digest to the
mover's key and to the state the entry states. So "a valid move in slot
`d`" is fully objective on-chain, and a garbage-signed entry fails its own
inclusion claim (G7, G7B).

The Move leaf binds the registers to the Lamport reveals (`EndBind`): it
decodes the prior, move and state to numbers, verifies the WOTS end
state, and compares the state nibbles of `E2` with the prior and the
nibbles of `E` with the move and state. So the disproofs judge exactly the
moves the venue holds, and the prior is the claimant's own commitment,
verified by its own leaf with HASH160; the counterparty's HASH160 key is
never needed by anyone but the counterparty (D27).

None of this held before this branch: the fact-chain claim absorbed
8-byte blocks with a round counter indexed by the step's position in the
whole claim, while the chain's `hash()` absorbed 10-byte blocks with a
padding step and a squeeze, so no prev-link or root predicate could ever
be expressed and the builder skipped them (D23). The chain now hashes with
`hash_claim`, the function the claim model computes.

## 4. Measurements (regtest, debug build)

| transaction | vsize |
|---|---|
| commitment | 240 vB |
| claim `move_d` (prior 21 + move 4 + state 21 + code 2 preimages, WOTS end state over 68 bytes) | 4,077–4,505 vB |
| refutation `r{d}/move_{d+1}` | 4,497 vB |
| split | 217 vB |
| `disprove_cell_occupied_0` | 288 vB |
| bisection (G6): `dispute` 194, `p_round` 3,516 × 8, `q_round` 181 × 8, `c_re_cur`/`c_re_next` 3,516 × 2, `simple_ent_root` 7,410 | 44.2 kvB in 20 transactions |
| bisection (G7B): as above but `p_re_cur` 4,002, `p_re_next` 3,515, `cpred_oe_s0a` 4,164 | 41.5 kvB in 20 transactions |

Stall or refused fold: 3 transactions, about 5.0 kvB, at any depth. The
claim transaction is dominated by the WOTS commitment of the 68-byte end
state; a smaller register file would roughly halve it. Before the
signature check (commit `14fddd1`) the figures were 742 pre-signed
transactions, 4.3 kvB per claim and 35 kvB / 16 transactions per
dispute: the check costs one bisection round and about a quarter of the
dispute, and nothing on the stall path.

## 5. Known gaps

1. **Resolved: entry signatures are verified by the claim** (D27, G7,
   G7B). What remains is the served-data gap for the bisection itself
   (D19): a prover serving different data than it commits is not caught.
2. **Decided, not a gap: absence is final.** A party late on the venue
   loses its bond, and a refuted timeout claim forfeits the claimant's.
   The game never continues on Bitcoin (VENUE.md §4). The consequence is
   that the venue's inclusion is load-bearing: censoring a move for one
   slot takes a bond, which is what the venue's consensus must price
   (VENUE.md §7).
3. **One block per move.** The slot rule fixes every claim's header count
   at open. A response window needs prover-selected header counts
   (variable-length claims), which remain unbuilt.
4. **The equivocation leaf** (two reveals under one per-depth key) is not
   built ON THIS GRAPH; a party with mining power could replace its own
   published move and the counterparty could only prove it holds two
   conflicting reveals off-chain. VENUE.md §5 lists it as the condition
   under which the venue may be advisory at all. CLOSED on the
   pos-factchain branch (D39, per-depth since D43): the `equiv_d` leaf on
   the contract output pays the exhibitor the pot on the exhibit of both
   full signatures under the mover's per-depth state key (two distinct
   valid WOTS signatures of different states ARE the double-sign proof).
5. **`settle` after the deadline pays `R(empty board)`** (the hub, since
   the user forfeits on turn) whatever happened on the venue. A player
   who never claims before the deadline loses; G5's passive user shows it.
6. The mining economy, the hash's cryptanalysis (2^40 capacity) and the
   fee reserve's sizing are parked, as agreed.
7. **The depth-independent stall graph is built and played** (D28,
   `GraphShape::Stall`, `lngap_factchain::stall`, `TttFcParams::stall`;
   scenarios S1-S7 in `scenarios/fc_stall.rs`, run by
   `tests/fc_stall.rs`). Per role a stall proof and a lie exhibit with
   fixed keys, the depth a revealed field bound to a 13-word claim of
   `3 + 9 W_max` steps that reads the three slots from the headers' `head`
   fields and checks no signature: 73 pre-signed transactions, built in
   under a second, against this document's 882 and 45 s. A stall costs
   three transactions at any depth; disproofs of an invalid move hang off
   the liar's stall output and off the victim's exhibit. The star graph
   of sections 2-4 remains what G1-G7B run. Since 2026-09-17 the graph
   also carries per role a SIGNATURE EXHIBIT (D31, key sets 5 and 6): a
   garbage-signed entry, which the stall claim counts as held, is a
   claim the victim makes and the liar may dispute (S8/S9; chess C8/C9);
   the graph is then 6 claim sets and, for tic-tac-toe, 129
   transactions. Chess plays on the same graph (D30, C1-C9). Not yet:
   the venue entry's move is unsigned for tic-tac-toe (chess signs it),
   the equivocation leaf, and disputes on the venue. [The POS-venue
   iteration of this graph — the absence-claim shape with the EC-OTS
   readout replacing the PoW dispute leg — is built and played on the
   pos-factchain branch: D32-D45, scenarios PS1-PS11 (tic-tac-toe) and
   PC1-PC12 (chess); it includes the equivocation leaf (D39, per-depth
   since D43), the counter that makes a thin claim's dueness enforceable
   (D44), the chess well-formedness leaf (D45), and, for chess, needs no
   terminal exhibit family (D42).]
