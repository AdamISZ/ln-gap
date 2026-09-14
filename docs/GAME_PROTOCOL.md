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
| G6 | the hub claims a move it never published | commitment, `move_4`, `d4/dispute`, 6 bisection rounds, re-commitments, `simple_root_ok`: disproved at the predicate |

G2A and G2B are the point: three transactions whether the stall happens at
move 2 or move 6. The old tic-tac-toe (docs/SCENARIOS.md, T-scenarios)
plays the rest of the game on Bitcoin move by move after a force-close.

## 2. The protocol

**Venue.** One fact-chain block per Bitcoin block (a harness convenience).
The block `d` after the contract opened is *slot* `d`, and move `d` must
sit in it: a move published later is a stall. The entry is 28 bytes,
`(game_id, depth, mover, move, state, tag)`, where the tag is the hash of
the mover's Lamport preimages for the move and state, which are served
alongside (`docs/DECISIONS.md` D20 convention: content-only entries,
auxiliary data served). Anyone verifies a published move against the
mover's pinned per-depth key; the counterparty stores the mover's state
reveal, since it is the prior of any claim the counterparty later makes.

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
  counterparty's state at `d - 1` (its own Lamport reveal, read off the
  venue), move `d`, the new state and the outcome code `R(s_d)`, and
  commits a *slot claim*: the fact-chain header chain from the checkpoint
  to slot `d` and the entry, with predicates (§3). `R(s_d)` is the result
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

The graph has 742 pre-signed transactions (9 claims + 8 refutations, each
with 3 splits and a dispute chain) and opens in about 12 s (debug build).

**Escalation.** A party whose opponent's slot passed without a valid move
queues a claim; the party force-closes when the claim's `CLTV` is within
`to_self_delay`, then makes the claim. A party that sees a claim against
a state it has moved from answers with its published move (the move
policy finds it by prior state). Everything else is the existing
machinery: disproofs, bisection, timeouts, splits.

## 3. The slot claim (`lngap_factchain::slot`)

A 16-word register file: `D` (the hash state), `P` (previous digest), `R`
(the last header's root field), `E` (the entry's `(move, state)` word).
Per header: 6 absorbs of 16 nibbles with `EqNibbles` predicates tying the
header's `prev` field to `P` and copies of its `root` field into `R`, a
zero pad block, then a simple step checking `LeTargetBe(D)` (proof of
work) and copying `D` to `P`. Then the entry: 4 absorbs, the first with
`EqConst` on `(game_id, depth, mover)` and a copy of `(move, state)` into
`E`, a pad block, and `root_ok: EqNibbles(D, R)`. `8 d + 6` steps, padded
to a power of two: 16 steps (4 rounds) at depth 1, 128 (7 rounds) at
depth 9.

The Move leaf binds `E` to the Lamport reveals (`EndBind`): it decodes the
move and state to numbers, verifies the WOTS end state, and compares the
nibbles of word `E`. So the claim proves "slot `d` holds an entry saying
`(mover, move, state)`" and the disproofs judge exactly that move.

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
| claim `move_d` (prior reveal 21 + move 4 + state 21 + code 2 preimages, WOTS end state over 64 bytes) | 3,885–4,274 vB |
| refutation `r{d}/move_{d+1}` | 4,273 vB |
| split | 217 vB |
| `disprove_cell_occupied_0` | 288 vB |
| bisection: `dispute` 194, `p_round` 3,324 × 6, `q_round` 181 × 6, `c_re_cur`/`c_re_next` 3,324 × 2, `simple_root_ok` 6,993 | 34.9 kvB in 16 transactions |

Stall or refused fold: 3 transactions, about 4.7 kvB, at any depth. The
claim transaction is dominated by the WOTS commitment of the 64-byte end
state; a smaller register file (or committing only `E` and `D`) would
roughly halve it.

## 5. Known gaps

1. **Entry authentication is not checked on-chain.** The claim binds the
   entry's 8-byte content to the reveal; the 20-byte tag over the
   preimages is not verified by any leaf. A mover can publish the right
   content with garbage preimages: the counterparty cannot build a claim
   from it and cannot exhibit the garbage either. Same class as the
   served-data gap (D19); the fix is hashing the preimages inside the
   claim (n4bit-keyed Lamport, conditional predicates). D27.
2. **No summons response on Bitcoin.** A party late on the venue
   forfeits; the design record's summons rule (answer an absence claim by
   acting on Bitcoin) only matters under venue censorship, which a
   one-miner world cannot produce. A spurious timeout claim is treated as
   a lie and forfeits the whole stake.
3. **One block per move.** The slot rule fixes every claim's header count
   at open. A response window needs prover-selected header counts
   (variable-length claims), which remain unbuilt.
4. **The equivocation leaf** (two reveals under one per-depth key) is not
   built; a party with mining power could replace its own published move
   and the counterparty could only prove it holds two conflicting reveals
   off-chain. VENUE.md §5 lists it as the condition under which the venue
   may be advisory at all.
5. **`settle` after the deadline pays `R(empty board)`** (the hub, since
   the user forfeits on turn) whatever happened on the venue. A player
   who never claims before the deadline loses; G5's passive user shows it.
6. The mining economy, the hash's cryptanalysis (2^40 capacity) and the
   fee reserve's sizing are parked, as agreed.
