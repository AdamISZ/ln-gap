//! The PoS venue world: one channel's worth of keystores (for real per-depth
//! entry signatures), one PoS venue (`lngap_pos::PosMiner` — since D51 a
//! five-member roster in strict round robin, its registry announced at
//! open), slots driven by the Bitcoin clock. Step 2 of
//! POS_FACTCHAIN_PLAN.md (D32).
//!
//! The world plays a scripted game of tic-tac-toe INTO the venue: each move
//! becomes the entry of the block sealed at its slot, attested under that
//! slot's epoch table. There is no contract and no dispute machinery here
//! yet (steps 3-4): this world proves the venue layer only — moves land as
//! attested heads at the right slots, anyone verifies the chain against the
//! published registry, and empty slots still get their (empty) block, the
//! cadence default.

use std::collections::HashMap;

use anyhow::{anyhow, ensure, Result};
use bitcoin::Amount;
use lngap_channel::Role;
use lngap_contract::instance::key_label;
use lngap_contract::Contract;
use lngap_ec_wots::EpochTable;
use lngap_factchain::slot::SlotEntry;
use lngap_lamport::Reveal;
use lngap_n4bit::{hash_claim, Digest};
use lngap_names::ServedData;
use lngap_pos::{Member, PosClient, PosMiner, Registry, SealedBlock};
use lngap_tictactoe::{Board, OPEN};
use lngap_tictactoe_fc::{registry, TicTacToeFc, TttFcParams};
use tracing::info;

use crate::game_world::Brain;
use crate::{init_log, Harness};

/// Each side's stake (unused until the contract integration, step 4).
pub const STAKE: Amount = Amount::from_sat(50_000);
pub const ID_GAME: u32 = 30;
pub const GAME_ID: u16 = 1;
/// The roster's base seed: member `i` is seeded `VENUE_SEED[0] + i` (five
/// members in strict round robin, D51).
pub const VENUE_SEED: [u8; 32] = [0x5A; 32];
pub const N_MEMBERS: u8 = 5;
/// The registry announced at open covers slots `0..=REGISTRY_SLOTS`.
pub const REGISTRY_SLOTS: u32 = 32;

pub fn members() -> Vec<Member> {
    (0..N_MEMBERS).map(|i| Member::new([VENUE_SEED[0] + i; 32])).collect()
}

/// A block the venue sealed, kept whole for later steps' exhibit
/// construction (the attestation is the refutation's raw material).
pub struct PosWorld {
    pub h: Harness,
    pub miner: PosMiner,
    pub client: PosClient,
    /// The registry the members announced at open (the scheduled member's
    /// table per slot, every member's flag point), what the client
    /// verifies seals against.
    pub registry: Registry,
    /// Every sealed slot's epoch table, as the venue published it.
    pub tables: HashMap<u32, EpochTable>,
    /// Every sealed block, by slot.
    pub sealed: HashMap<u32, SealedBlock>,
    /// What each sealed slot's block carried (empty for an empty block).
    pub blocks: HashMap<u32, Vec<u8>>,
    pub program: TicTacToeFc,
    pub brains: [Brain; 2],
    pub board: Board,
    pub depth: u32,
    pub btc_open: u32,
    /// The entry for the coming slot, prepared by the mover's brain.
    pending: Option<(SlotEntry, Vec<u8>)>,
    /// Each role's per-depth venue key commitments (index `[role][d - 1]`),
    /// what anyone checks a published entry's signature against.
    pub venue_commits: [Vec<Vec<[Digest; 2]>>; 2],
    pub log: Vec<String>,
}

impl PosWorld {
    /// A funded channel, a PoS venue at genesis, and the game program; no
    /// contract is opened (that is step 4).
    pub fn new(label: &str, brains: [Brain; 2]) -> Result<PosWorld> {
        init_log();
        let store = ServedData::default();
        let h = Harness::new(label, registry(store.clone()))?;
        let members = members();
        let (gen, table0) = lngap_pos::genesis(&members[0].attester);
        let checkpoint = gen.header.digest();
        let mut miner = PosMiner::new(members, checkpoint, 0);
        let registry = miner.registry(REGISTRY_SLOTS)?;
        let btc_open = h.height();
        let program = TicTacToeFc::new(
            TttFcParams {
                game_id: GAME_ID,
                checkpoint,
                btc_open,
                grace: 1,
                stall: true,
                w_max: 10,
            },
            store,
        );
        let mut w = PosWorld {
            miner,
            client: PosClient::from_checkpoint(0, checkpoint),
            registry,
            tables: HashMap::from([(0u32, table0)]),
            sealed: HashMap::from([(0u32, gen)]),
            blocks: HashMap::new(),
            h,
            program,
            brains,
            board: Board::empty(),
            depth: 0,
            btc_open,
            pending: None,
            venue_commits: [vec![], vec![]],
            log: Vec::new(),
        };
        w.make_venue_keys()?;
        Ok(w)
    }

    /// Each role's per-depth venue signing keys, generated in its party's
    /// key store (the D28 stall-graph discipline; exchanged in the draft in
    /// a deployment).
    fn make_venue_keys(&mut self) -> Result<()> {
        let n = lngap_tictactoe::TicTacToe.n_state_bits();
        for r in Role::BOTH {
            let mut commits = Vec::new();
            for d in 1..=9u32 {
                let label = key_label(ID_GAME, 0, d, "venue");
                let ks = self.h.party(r).keystore();
                ks.generate(&label, n)?;
                commits.push(ks.commit_with(&label, |p| hash_claim(p))?);
            }
            self.venue_commits[r.idx()] = commits;
        }
        Ok(())
    }

    fn say(&mut self, s: String) {
        info!(world = "pos", "{s}");
        self.log.push(format!(
            "[pos @ {} / slot {}] {s}",
            self.h.height(),
            self.depth
        ));
    }

    /// The slot the venue seals at this step: the Bitcoin block just mined
    /// (one venue block per Bitcoin block, the harness cadence).
    fn coming_slot(&self) -> u32 {
        self.h.height() - self.btc_open
    }

    /// The mover's reveal of the state after move `d` (its venue key).
    fn state_reveal(&mut self, r: Role, d: u32, new: &Board) -> Result<Reveal> {
        let bits = lngap_tictactoe::TicTacToe.state_bits(new);
        self.h
            .party(r)
            .keystore()
            .reveal_bits(&key_label(ID_GAME, 0, d, "venue"), &bits)
    }

    /// The brain on turn prepares the coming slot's entry.
    fn publish_step(&mut self) -> Result<()> {
        if self.board.status != OPEN {
            return Ok(());
        }
        let d = self.depth + 1;
        if d > 9 {
            return Ok(());
        }
        let r = TicTacToeFc::mover_at(d);
        let brain = &self.brains[r.idx()];
        let Some(&cell) = brain.moves.get((d as usize - 1) / 2) else {
            self.say(format!("{r} has no move {d} scripted"));
            return Ok(());
        };
        let new = self
            .program
            .transition(&self.board, &cell, r)
            .map_err(|e| anyhow!("{r}'s scripted move {d} is invalid: {e}"))?;
        let st_r = self.state_reveal(r, d, &new)?;
        let entry = self.program.entry(d, cell, &new, &st_r);
        let bytes = entry.encode();
        self.pending = Some((entry, bytes));
        Ok(())
    }

    /// Seal the coming slot (with the pending entry, or empty), verify it
    /// natively as anyone would, and file the registry data.
    fn seal_step(&mut self) -> Result<()> {
        let slot = self.coming_slot();
        let pending = self.pending.take();
        if let Some((_, bytes)) = &pending {
            self.miner.submit(bytes.clone());
        }
        let (block, table) = self.miner.seal_next(slot).map_err(|e| anyhow!(e))?;
        self.client
            .verify_and_append(&block, &self.registry)
            .map_err(|e| anyhow!(e))?;
        let proposer = self.miner.proposer_at(slot);
        if let Some((entry, bytes)) = pending {
            // anyone verifies the entry: content, and the signature against
            // the mover's venue commitments
            let mover = TicTacToeFc::mover_at(slot);
            let decoded = SlotEntry::decode(&bytes).ok_or_else(|| anyhow!("undecodable entry"))?;
            ensure!(
                decoded == entry
                    && decoded.depth == slot as u8
                    && decoded.mover == mover.idx() as u8
            );
            ensure!(
                decoded.check_sigs(&self.venue_commits[mover.idx()][slot as usize - 1]),
                "{mover}'s entry at slot {slot} does not open its venue key"
            );
            self.board = self
                .program
                .transition(&self.board, &decoded.mv, mover)
                .map_err(|e| anyhow!(e))?;
            self.depth = slot;
            self.say(format!(
                "slot {slot} sealed by member {proposer} with {mover}'s move ({}); attested",
                self.board.render()
            ));
            self.blocks.insert(slot, bytes);
        } else {
            self.blocks.insert(slot, Vec::new());
            self.say(format!("slot {slot} sealed EMPTY by member {proposer} (cadence)"));
        }
        self.tables.insert(slot, table);
        self.sealed.insert(slot, block);
        Ok(())
    }

    /// One step: mine a Bitcoin block, prepare the move, seal the slot.
    pub fn step(&mut self) -> Result<u32> {
        self.h.rt.mine(1)?;
        let h = self.h.height();
        let txs = self.h.rt.block_txs(h)?;
        self.h.deliver(h, &txs)?;
        self.publish_step()?;
        self.seal_step()?;
        Ok(h)
    }

    pub fn steps(&mut self, n: u32) -> Result<()> {
        for _ in 0..n {
            self.step()?;
        }
        Ok(())
    }

    /// The venue's tip slot.
    pub fn tip(&self) -> u32 {
        self.client.tip_height()
    }
}
