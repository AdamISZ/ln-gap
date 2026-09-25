//! The wired PoS absence-claim graph (POS_FACTCHAIN_PLAN.md step 4b; D34's
//! leaf family, wired per depth, with D35's two-head refutation).
//!
//! Per depth `d` (the slot the mover should have published at), with the
//! claimant the non-mover:
//!
//! - on the contract output: `absent_d`, the claimant's absence claim,
//!   spendable once `claim_from` (the Bitcoin height after the mover's slot
//!   window) has passed (CLTV) — 2-of-2, so the claim transaction is
//!   pre-signed at setup and its output is pinned to the claim tree;
//! - the claim output's tree: the mover's refutation (the D33 leaf at
//!   depth 1, the D35 two-head leaf from depth 2 — the slots' epoch tables
//!   as script constants) racing the claimant's timeout splits (CSV =
//!   `delta`, gated by the claimant's code reveal);
//! - the refutation output's tree: the claimant's disprove family over the
//!   parked tuple (CSV = `delta`), then the mover's self-checking splits by
//!   the revealed outcome code (CSV = `delta + delta'` — "by the code the
//!   victim revealed", the D28 discipline, with `code == R(parked state)`
//!   proven in-leaf).
//!
//! Two wirings the bare leaf family did not have: the refutation leaf is
//! gated by the mover's payment key and pre-signed, so the refutation's
//! output is pinned to the refuted tree (ungated, the mover could skip the
//! disprove stage by spending the claim output elsewhere — safe for a legal
//! move, theft for an illegal one); and the splits on the refuted output
//! check the code against the parked state, because a PoS refutation
//! carries no code reveal for a `code_mismatch` leaf to judge.
//!
//! The timeliness flag (D50, NON_INCLUSION_THRESHOLD.md). A refutation
//! proves the venue attested slot `d`'s head, never WHEN: a proposer
//! colluding with the mover can attest his signed move after the deadline
//! and refute an honest claim. So the refuted tree carries one more
//! claimant leaf, `not_timely`: `k` validator flag points for slot `d` as
//! script constants, counted by CHECKSIGADD against a threshold `t`. A
//! validator that saw the slot pass its deadline empty published its flag
//! secret; the claimant signs its own spend under any `t` of them and the
//! refutation dies. Rule (D50): the refutation dies on `t` flags — the
//! rogue-`t` residual (false emptiness against a timely move) falls on the
//! honest mover, who has a venue to pursue by name (the `t` points in the
//! witness), rather than the late-attestation residual on the claimant,
//! who has nobody.
//!
//! The counter (D44). The thin claim asserts no venue content, so nothing
//! in it says the claim was DUE — that the claimant itself moved at
//! `d - 1`. Without that, the staller at `d - 1` can claim `absent_d`
//! ("you did not move at `d`" — vacuously true, the victim's turn never
//! came) and the victim cannot refute; only CLTV order separated the two
//! claims, and the broadcaster's `to_self_delay` on the honest one inverts
//! it. So from depth 2 the claim output carries one more leaf, `counter`:
//! the mover's thin claim one depth BACK, "you did not move at `d - 1`" —
//! exactly the negation of dueness. Its output tree is the depth-`d - 1`
//! claim tree verbatim (the claimant's refutation by the `(d - 2, d - 1)`
//! pair readout, racing the counter-claimant's timeout splits), and that
//! refutation's output is the depth-`d - 1` refuted tree. One level closes
//! it: a counter is answered by a positive readout or not at all — a false
//! counter is refuted by the claimant's own attested, signed head at
//! `d - 1` (and then judged by the ordinary disprove family / paid by the
//! checked split), and a true counter means the claim was never due, which
//! should lose regardless of what happened earlier (the claimant always had
//! a due claim at a shallower depth). The counter output's tree therefore
//! carries NO counter of its own. The honest bare stall stays two small
//! transactions; the claim-ahead costs the attacker the pot for a ~200 vB
//! counter.

use anyhow::Result;
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Script, Transaction, TxOut};
use lngap_btc::script::BuilderExt;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_contract::leaves::split_leaf;
use lngap_contract::Outcome;
use lngap_ec_wots::EpochTable;
use lngap_lamport::winternitz::{WotsExt, WotsPublic};

use crate::chess;
use crate::instance::{Game, PosDepthKeys};
use crate::refute;
use crate::ttt::{self, Layout};

/// The authorship fragment of the instance's game (D41; the chess mapping
/// is chess.rs's). D43: the per-depth state key is a Winternitz key and
/// the fragment is the tied verify (the signed region's digits are the
/// register file's own).
fn authorship(b: Builder, game: Game, file: usize, head_off: usize, key: &WotsPublic) -> Builder {
    match game {
        Game::Ttt => ttt::authorship_fragment(b, file, head_off, key),
        Game::Chess => chess::authorship_fragment(b, file, head_off, key),
    }
}

/// The absence-claim leaf for one depth on the contract output.
pub fn absent_leaf(ctx: &CommitCtx, name: &str, claimant: Role, claim_from: u32) -> Leaf {
    let mut b = Builder::new().cltv(claim_from);
    let mut tl = Timelock::cltv(claim_from);
    if claimant == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    b = ctx.two_of_two_verify(b);
    Leaf::new(name.to_string(), b.push_int(1).into_script(), tl)
}

/// The mover's refutation leaf on the claim output: the mover's payment
/// signature first (the pre-signed skeleton pins the output to the refuted
/// tree), then the readout-and-park. The D41 authorship fragment rides the
/// gate slot: per parked head, the witness must carry THAT head's mover's
/// state-key signature over the head's signed region (the D43 tied-WOTS
/// verify against the parked digits) — a garbage-signed attested entry
/// admits no refutation.
pub fn refute_leaf(ctx: &CommitCtx, game: Game, l: &Layout, table_prev: Option<&EpochTable>, table: &EpochTable, keys: &PosDepthKeys, keys_prev: Option<&PosDepthKeys>) -> Leaf {
    let body = match table_prev {
        Some(tp) => refute::refute_leaf_pair_gated(tp, table, &keys.refute, |b| {
            // the D41 authorship gate: tic-tac-toe checks BOTH parked heads
            // (21 bits each, cheap); chess checks the NEW head alone — the
            // judged move's — because 2 x 336 preimage blocks do not fit
            // the 1,000-element stack under the readout (D42). The prior
            // head's authenticity is inductive: an unauthored head at d-1
            // is unrefutable at d-1's own claim, so a game never continues
            // past one.
            let b = authorship(b, game, l.file, l.new, &keys.state);
            match game {
                Game::Ttt => authorship(b, game, l.file, 0, &keys_prev.expect("a pair has a prior").state),
                Game::Chess => b,
            }
        }),
        None => refute::refute_leaf(table, &keys.refute, |b| authorship(b, game, l.file, 0, &keys.state)),
    };
    let mut b = Builder::new().checksigverify(&ctx.key(l.mover).payment);
    for ins in body.instructions() {
        b = match ins.expect("valid script") {
            bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
            bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
        };
    }
    Leaf::new("refute", b.into_script(), Timelock::NONE)
}

/// The terminal-exhibit leaf for one depth on the CONTRACT output (D37,
/// the terminal-claim hole's fix): the mover of move `d` — the winner, or
/// the last mover of a draw — exhibits the attested pair
/// `head(d-1) || head(d)` with the status gate on top: the leaf fires only
/// when the parked new state is TERMINAL, and the exhibit output's tree
/// (the refuted tree verbatim) pays R(parked terminal). Without the gate
/// the exhibit would fire on any attested open state, and R(open) pays the
/// mover who just moved — a mid-game self-claim button the disprove family
/// cannot see (the exhibited move is legal).
///
/// The wiring is `absent_d`'s: CLTV to after slot `d`'s window (the
/// attestation must exist) plus 2-of-2, so the exhibit transaction is
/// pre-signed and the exhibit output is pinned to its tree. The key is the
/// depth-`d` refute key — both leaves bind the same two epoch tables, so
/// the signed message is provably the same 96 bytes, and the contexts are
/// mutually exclusive (the contract output is spent once): the WOTS
/// one-time-ness is preserved by construction. The exhibit exists from
/// depth 5 (tic-tac-toe cannot be terminal before move 5 — the
/// never-fire-trim discipline).
pub fn exhibit_leaf(
    ctx: &CommitCtx,
    name: &str,
    l: &Layout,
    table_prev: &EpochTable,
    table: &EpochTable,
    keys: &PosDepthKeys,
    keys_prev: &PosDepthKeys,
    claim_from: u32,
) -> Leaf {
    let mut b = Builder::new().cltv(claim_from);
    let mut tl = Timelock::cltv(claim_from);
    if l.mover == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    b = ctx.two_of_two_verify(b);
    let body = refute::refute_leaf_pair_gated(table_prev, table, &keys.refute, |b| {
        let b = ttt::authorship_fragment(b, l.file, l.new, &keys.state);
        let b = ttt::authorship_fragment(b, l.file, 0, &keys_prev.state);
        ttt::terminal_gate_fragment(b, l.file, l.new)
    });
    for ins in body.instructions() {
        b = match ins.expect("valid script") {
            bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
            bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
        };
    }
    Leaf::new(name.to_string(), b.into_script(), tl)
}

/// The player-equivocation leaf for one depth on the CONTRACT output
/// (POS_FACTCHAIN_PLAN.md step 6; D39; D43's per-depth form): the witness
/// exhibits TWO full signatures under the depth-`d` mover's state key over
/// DIFFERENT signed regions — possible only if the mover double-signed at
/// that depth (a reorg-aided double-play, GAME_PROTOCOL.md section 5 item
/// 4). With the Lamport per-bit key this was one bit's two preimages (the
/// `equiv_{d}_{i}` family); a WOTS signature's reveal is forced given the message, so two
/// distinct valid signatures under one key are the equivocation proof (the
/// checksum guarantees at least one digit where one side needed a preimage
/// the other can't supply), and the family collapses to one leaf per depth.
/// Idempotent re-broadcast of the SAME entry re-presents the same
/// signature, which never fires the differ check. The spend is the graph's
/// standard 2-of-2 pre-signed skeleton paying the exhibitor (the depth's
/// non-mover) the pot; the witness carries the two signatures in wire order
/// (`wots_wire` of the first, then the second), then the two payment
/// signatures (sig_user on top: the 2-of-2 checks first).
///
/// The choreography: the FIRST wots_verify consumes the SECOND wire block
/// (the topmost), leaving its message digits; those park to the altstack so
/// the SECOND verify can reach the first block below them; the parked
/// vector restores ON TOP. The differ then compares the two parked message
/// vectors ([a below, b on top]: b_j at depth m-1-j, a_j at 2m-1-j).
pub fn equiv_leaf(ctx: &CommitCtx, name: &str, key: &WotsPublic, exhibitor: Role) -> Leaf {
    let mut b = Builder::new();
    let mut tl = Timelock::NONE;
    if exhibitor == ctx.broadcaster && ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    let m = key.params.message_digits as usize;
    b = ctx.two_of_two_verify(b).wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_TOALTSTACK); // park the second signature's digits
    }
    b = b.wots_verify(key);
    for _ in 0..m {
        b = b.push_opcode(OP_FROMALTSTACK); // restore them on top
    }
    // the two parked message vectors must DIFFER
    b = b.push_int(0);
    for j in 0..m {
        b = b
            .push_int((m - j) as i64) // b_j (the top vector, one deeper under the accumulator)
            .push_opcode(OP_PICK)
            .push_int((2 * m - j + 1) as i64) // a_j (the deeper vector, post-pick)
            .push_opcode(OP_PICK)
            .push_opcode(OP_SUB)
            .push_opcode(OP_0NOTEQUAL)
            .push_opcode(OP_ADD);
    }
    b = b.push_opcode(OP_VERIFY); // some digit differs
    for _ in 0..m {
        b = b.push_opcode(OP_2DROP);
    }
    Leaf::new(name.to_string(), b.push_int(1).into_script(), tl)
}

/// The counter leaf on the claim output A_d (D44): the mover's thin claim
/// one depth back — "the claimant did not move at `d - 1`", the negation
/// of the claim's dueness. 2-of-2 and pre-signed (the counter output is
/// pinned to the depth-`d - 1` claim tree), no timelock: it must land
/// inside the claimant's timeout window (`delta`), like a refutation. No
/// `to_self_delay`: that delay guards the CONTRACT output against a
/// revoked commitment, and this spends a claim output.
pub fn counter_leaf(ctx: &CommitCtx, name: &str) -> Leaf {
    let b = ctx.two_of_two_verify(Builder::new());
    Leaf::new(name.to_string(), b.push_int(1).into_script(), Timelock::NONE)
}

/// The tree of the claim output A_d: the mover's refutation plus the
/// claimant's timeout splits after the dispute window (`delta`), gated by
/// the claimant's code reveal — and, with `counter`, the mover's counter
/// claim one depth back (D44; `counter` is set on the contract output's
/// claims from depth 2 and NEVER on a counter output's own tree).
#[allow(clippy::too_many_arguments)]
pub fn claim_tree(
    ctx: &CommitCtx,
    game: Game,
    l: &Layout,
    table_prev: Option<&EpochTable>,
    table: &EpochTable,
    keys: &PosDepthKeys,
    keys_prev: Option<&PosDepthKeys>,
    outcomes: &[Outcome],
    counter: bool,
) -> Result<TapTree> {
    let mut leaves = vec![refute_leaf(ctx, game, l, table_prev, table, keys, keys_prev)];
    if counter {
        leaves.push(counter_leaf(ctx, "counter"));
    }
    for o in outcomes {
        leaves.push(split_leaf(ctx, o, ctx.params.delta, &keys.claimant_code));
    }
    TapTree::new(leaves)
}

/// The `not_timely` leaf on the refutation output P_d (D50): the
/// claimant's timeliness disprove. Same gate as the disprove family (CSV
/// `delta`, the challenger's payment key), then the slot's `k` validator
/// flag points counted by CHECKSIGADD against the threshold `t`:
///
/// ```text
///   <delta> CSV DROP <challenger> CHECKSIGVERIFY
///   <F_1> CHECKSIG <F_2> CHECKSIGADD ... <F_k> CHECKSIGADD
///   <t> GREATERTHANOREQUAL
/// ```
///
/// Witness (consumption order): the challenger's signature, then one slot
/// per validator — a 64-byte signature of THIS spend under `F_i` (made
/// with the published scalar `f_i`), or empty. BIP342 makes an empty
/// signature add zero and continue and a non-empty invalid one fail, so
/// exactly the validators whose scalars the claimant holds count, and each
/// counted signature names its validator. No pair reveal: the leaf judges
/// the slot, not the parked tuple.
pub fn not_timely_leaf(ctx: &CommitCtx, l: &Layout, flags: &[XOnlyPublicKey], t: u32) -> Leaf {
    assert!(!flags.is_empty() && 1 <= t && t as usize <= flags.len(), "1 <= t <= k");
    let challenger = ctx.key(l.mover.other()).payment;
    let mut b = Builder::new().csv(ctx.params.delta).checksigverify(&challenger);
    for (i, f) in flags.iter().enumerate() {
        b = b.push_x_only_key(f).push_opcode(if i == 0 { OP_CHECKSIG } else { OP_CHECKSIGADD });
    }
    b = b.push_int(i64::from(t)).push_opcode(OP_GREATERTHANOREQUAL);
    Leaf::new("not_timely", b.into_script(), Timelock::csv(ctx.params.delta))
}

/// The `not_timely` witness (wire order, bottom first) for the spend `tx`
/// of input `input` through `leaf`: `scalars[i]` is validator `i`'s
/// published flag secret for the slot, or `None` (an empty slot in the
/// witness); `challenger` signs first in consumption order (last in wire
/// order). The claimant signs its OWN transaction under every scalar it
/// holds — nobody signs anybody else's transaction.
pub fn not_timely_witness(tx: &Transaction, input: usize, prevouts: &[TxOut], leaf: &Script, challenger: &Keypair, scalars: &[Option<SecretKey>]) -> Vec<Vec<u8>> {
    let mut w = Vec::with_capacity(scalars.len() + 1);
    for f in scalars.iter().rev() {
        w.push(match f {
            Some(f) => sign_tapscript(&Keypair::from_secret_key(SECP256K1, f), tx, input, prevouts, leaf).expect("sighash").as_ref().to_vec(),
            None => Vec::new(),
        });
    }
    w.push(sign_tapscript(challenger, tx, input, prevouts, leaf).expect("sighash").as_ref().to_vec());
    w
}

/// The tree of the refutation output P_d: the claimant's disprove family
/// over the parked tuple (after `delta`) — the game's own predicate set —
/// and its `not_timely` leaf over slot `d`'s `flags` with threshold `t`
/// (D50), then the mover's self-checking splits after `delta + delta'`.
#[allow(clippy::too_many_arguments)]
pub fn refuted_tree(ctx: &CommitCtx, game: Game, l: &Layout, keys: &PosDepthKeys, outcomes: &[Outcome], flags: &[XOnlyPublicKey], t: u32) -> Result<TapTree> {
    let challenger = ctx.key(l.mover.other()).payment;
    let family = match game {
        Game::Ttt => ttt::disprove_leaves(l, &keys.refute),
        Game::Chess => chess::disprove_leaves(l, &keys.refute),
    };
    let mut leaves = vec![];
    for pl in family {
        let mut b = Builder::new().csv(ctx.params.delta).checksigverify(&challenger);
        for ins in pl.script.instructions() {
            b = match ins.expect("valid script") {
                bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
                bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
            };
        }
        leaves.push(Leaf::new(format!("disprove_{}", pl.name), b.into_script(), Timelock::csv(ctx.params.delta)));
    }
    leaves.push(not_timely_leaf(ctx, l, flags, t));
    let w = ctx.params.delta + ctx.params.delta_prime;
    for o in outcomes {
        let leaf = match game {
            Game::Ttt => ttt::checked_split_leaf(ctx, l, o, w, &keys.mover_code, &keys.refute),
            Game::Chess => chess::checked_split_leaf(ctx, l, o, w, &keys.mover_code, &keys.refute),
        };
        leaves.push(leaf);
    }
    TapTree::new(leaves)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::Amount;
    use lngap_btc::keys::Seed;
    use lngap_channel::{ChannelParams, PartyKeys};
    use lngap_ec_wots::FlagKeys;

    /// The leaf's script grows by exactly one 32-byte key push plus one
    /// opcode per validator (34 bytes, 8.5 vB); at k = 15 it is under 560
    /// bytes. Each signer then costs a 64-byte witness element (16 vB) and
    /// each non-signer an empty one (~0.25 vB): 10-of-15 is ~0.4 kvB all in.
    #[test]
    fn not_timely_leaf_size_is_linear_in_k() {
        let params = ChannelParams::regtest(Amount::from_sat(400_000));
        let pubs = [
            PartyKeys::from_seed(Role::User, Seed::from_label("nt/user")).public(),
            PartyKeys::from_seed(Role::Hub, Seed::from_label("nt/hub")).public(),
        ];
        let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
        let l = Layout::at(2, 1, Role::Hub);
        let validators: Vec<FlagKeys> = (0..15u8).map(|i| FlagKeys::new([i + 1; 32])).collect();
        let points: Vec<XOnlyPublicKey> = validators.iter().map(|v| v.flag_point(2)).collect();
        let len = |k: usize| not_timely_leaf(&ctx, &l, &points[..k], 1).script.len();
        let base = len(1) - 34;
        for k in [1usize, 2, 5, 10, 15] {
            assert_eq!(len(k), base + 34 * k, "34 bytes per validator");
        }
        assert!(len(15) < 560, "15 validators: {} B", len(15));
        // t up to 16 is a single-byte push; the threshold is checked
        let leaf = not_timely_leaf(&ctx, &l, &points, 10);
        assert_eq!(leaf.script.len(), base + 34 * 15);
        assert_eq!(leaf.name, "not_timely");
        assert_eq!(leaf.timelock, Timelock::csv(params.delta));
    }
}
