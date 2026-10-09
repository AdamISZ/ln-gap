//! The withdrawal statement (docs/planning/WITHDRAW_STATEMENT.md): a note
//! owned by the hub, of value `b` and memo `c`, is in the commitment tree
//! of a state root the L2's sequencer signed. Commits `b ‖ c`
//! (little-endian u32s). The check is `lngap_r0_core::check`, shared with
//! the host; the sequencer's and the hub's keys are constants of the
//! image.

use lngap_r0_core::{check, WithdrawInput, HUB_KEY, SEQUENCER_KEY};
use risc0_zkvm::guest::env;

fn main() {
    let input: WithdrawInput = env::read();
    let journal = check(&input, &SEQUENCER_KEY, &HUB_KEY).expect("the withdrawal statement must hold");
    env::commit_slice(&journal);
}
