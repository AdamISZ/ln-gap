//! The withdrawal statement (docs/planning/WITHDRAW_STATEMENT.md): a note
//! owned by the hub, of value `b` and memo `c`, is in the commitment tree
//! of a state root the L2's sequencer signed. Commits `b ‖ c ‖ D`
//! (little-endian u32s, then the deployment id of the sequencer's and the
//! hub's keys, which are part of the input). The check is
//! `lngap_r0_core::check`, shared with the host.

use lngap_r0_core::{check, WithdrawInput};
use risc0_zkvm::guest::env;

fn main() {
    let input: WithdrawInput = env::read();
    let journal = check(&input).expect("the withdrawal statement must hold");
    env::commit_slice(&journal);
}
