# How it works: explainers

Short, diagram-led walk-throughs of the mechanisms that recur across the
code. Each one drills into a single concrete example rather than trying to
be complete; the [short paper](paper/lngap-short.pdf) gives the
motivation, and the [long paper](paper/lngap_draft.pdf) the full design.

| | |
|---|---|
| [Testing a game rule in Script: tic-tac-toe](tictactoe-predicates.md) | the *disprove leaf*: how one rule is checked against two parked heads, opcode by opcode |
| [Testing a chess rule in Script: exhibits](chess-predicates.md) | computed board reads, and a witness value that turns a universal rule into one check |
| [Hidden cards in Script: blackjack's shares](blackjack-shares.md) | committing to a number by a string's length, and inputs that travel outside the heads |
| [Winternitz signatures in Script](winternitz.md) | the one-time signature that carries every message, and the *register file* it leaves behind |
| [EC-OTS: how Script reads what the venue sealed](ec-ots.md) | the venue's anticipation-point tables, the readout fragment, one-bit keys, and the fee lock |
| [The pre-signed dispute graph](presigned-graph.md) | the transactions hanging off a contract output, who signs what and why, and what a channel update exchanges |

A suggested order: tic-tac-toe, then Winternitz and EC-OTS (the two
signatures every dispute leans on), then chess and blackjack, then the
graph that ties them together.

The scripts quoted in these pages are printed by

    cargo run -p lngap-pos --example doc_scripts

from the same builders the dispute graph uses.
