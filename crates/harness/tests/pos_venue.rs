//! Step 2 of POS_FACTCHAIN_PLAN.md: the PoS venue world. A scripted game of
//! tic-tac-toe lands on the venue as attested heads at the right slots; empty
//! slots still get their block (the cadence default); the chain verifies
//! against the published registry.

use anyhow::{anyhow, ensure, Result};
use lngap_factchain::slot::SlotEntry;
use lngap_harness::game_world::Brain;
use lngap_harness::pos_world::{PosWorld, GAME_ID};
use lngap_tictactoe::OPEN;
use lngap_tictactoe_fc::TicTacToeFc;

/// A full cooperative game (the user takes the top row at depth 5), then two
/// cadence blocks. Every move sits in its slot's block as an attested head.
#[test]
fn moves_land_as_attested_heads() -> Result<()> {
    let brains = [
        Brain {
            moves: vec![0, 1, 2], // user: the top row
            ..Default::default()
        },
        Brain {
            moves: vec![3, 4], // hub: the middle row, left and centre
            ..Default::default()
        },
    ];
    let mut w = PosWorld::new("pos-venue", brains)?;

    // The game: depths 1-5 sealed at slots 1-5.
    w.steps(5)?;
    assert_eq!(w.depth, 5);
    assert_ne!(w.board.status, OPEN, "the game is over on the venue");
    assert_eq!(w.tip(), 5);

    for d in 1..=5u32 {
        let mover = TicTacToeFc::mover_at(d);
        let entry = SlotEntry::decode(&w.blocks[&d]).expect("the block's entry decodes");
        // The attested head's content words ARE the move.
        let head = w.client.header_at(d).expect("sealed at slot").head();
        let w0 = u32::from_be_bytes(head[0..4].try_into().unwrap());
        let w1 = u32::from_be_bytes(head[4..8].try_into().unwrap());
        ensure!(w0 == SlotEntry::word0(GAME_ID, d as u8, mover.idx() as u8));
        ensure!(w1 == SlotEntry::word1(entry.mv, entry.state));
        // The seal verifies against the slot's published registry table.
        w.sealed[&d]
            .verify_seal(&w.tables[&d])
            .map_err(|e| anyhow!("slot {d}: {e}"))?;
        // And the world's native check saw a correctly signed entry.
        assert!(entry.check_sigs(&w.venue_commits[mover.idx()][d as usize - 1]));
    }

    // Cadence: two more steps seal empty blocks at slots 6 and 7.
    w.steps(2)?;
    assert_eq!(w.tip(), 7);
    assert!(w.blocks[&6].is_empty() && w.blocks[&7].is_empty());
    assert_eq!(w.client.header_at(6).unwrap().head(), [0u8; 48]);
    w.sealed[&7]
        .verify_seal(&w.tables[&7])
        .map_err(|e| anyhow!("slot 7: {e}"))?;
    Ok(())
}
