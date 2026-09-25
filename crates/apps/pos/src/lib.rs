//! The PoS venue chain: the fact chain's 96-byte header sealed by an EC-OTS
//! attestation instead of proof of work.
//!
//! Design: docs/design-notes/DECISIONS.md D32 and
//! docs/planning/hermes-research/POS_FACTCHAIN_PLAN.md. The header is
//! byte-identical to the PoW chain's (`prev(20) root(20) head(48) height(4)
//! pad(4)`); the `height` field carries the SLOT (epoch = slot). The seal is
//! an attestation over all [`HEADER_CHUNKS`] chunks of the header under the
//! slot's epoch table, produced by a single attester key standing in for the
//! FROST group key. The per-chunk statements let a later dispute read out any
//! subset of the header (the head for a stall refutation, the root for an
//! entry exhibit) without a separate attestation form.
//!
//! Since D51/D53 the sealer is a ROSTER (`roster.rs`): n members sharing
//! ONE content key (the attestation under it is the same whoever makes
//! it), each revealing a per-slot PROPOSER scalar in the block it seals
//! (the block's name tag) and flagging every slot it saw pass its
//! deadline empty (D50). Any member seals any slot. [`PosMiner`] holds the
//! content key and the members' secrets, [`PosClient`] verifies each seal
//! against the slot's shared table in the [`Registry`] and the block's
//! proposer reveal against that member's point, and an equivocation names
//! the block's proposer.
//!
//! The chain runs a CONSTANT CADENCE by default: one block per slot, empty
//! if no entry is pending (various venue-level reasons may prefer or even
//! require this — liveness, ordering for non-game apps). But density is a
//! default, not a validity rule: clients accept any strictly increasing
//! slot sequence, and the dispute layer never depends on it — a "Bob did
//! not publish in the window" claim is enforced by the challenge window
//! itself: a refutation that does not exist cannot be exhibited. (Density
//! WAS a hard requirement of the D28 PoW stall claim's fixed-position
//! header scan; the thin PoS claim drops that, and gaps are a liveness
//! event, not a validity failure.)

use std::collections::{HashMap, HashSet};

use bitcoin::secp256k1::SecretKey;
use lngap_ec_wots::{Attestation, Attester, EpochTable};
use lngap_factchain::{entry_head, entry_root, Header, HEADER_BYTES, HEAD_BYTES};
use lngap_n4bit::{Digest, DIGEST_BYTES};

pub mod bond;
pub mod chess;
pub mod fee;
pub mod graph;
pub mod refute;
pub mod instance;
pub mod roster;
pub mod ttt;

pub use roster::{Member, MemberPublic, Registry, Roster};

/// Attested chunks per header: one per nibble (96 bytes = 192 chunks).
pub const HEADER_CHUNKS: usize = HEADER_BYTES * 2;

/// A block sealed by the venue's attestation over the header bytes, with
/// its proposer's name tag: the member index and the revealed proposer
/// scalar for the slot (D53).
pub struct SealedBlock {
    pub header: Header,
    /// The single entry this block carries (stage 1).
    pub entry: Vec<u8>,
    /// One revealed scalar per header chunk, under the slot's epoch table.
    pub attestation: Attestation,
    /// Which member sealed it, and its revealed proposer scalar for the
    /// slot (`p_{i,s}`: a private key for the registry's point `P_{i,s}`).
    pub proposer: usize,
    pub proposer_secret: SecretKey,
}

impl SealedBlock {
    /// The proposer reveal opens the named member's point for the slot.
    pub fn verify_proposer(&self, registry: &Registry) -> Result<(), String> {
        let slot = self.header.height();
        let points = registry.proposers(slot);
        if self.proposer >= points.len() {
            return Err(format!("slot {slot}: proposer index {} is not a member", self.proposer));
        }
        let pt = bitcoin::key::Keypair::from_secret_key(bitcoin::secp256k1::SECP256K1, &self.proposer_secret).x_only_public_key().0;
        if pt != points[self.proposer] {
            return Err(format!("slot {slot}: the proposer reveal does not open member {}'s point", self.proposer));
        }
        Ok(())
    }

    /// The positional checks: head = entry's head, root = entry's root,
    /// prev link. Shared with the PoW chain minus the target.
    pub fn verify_structure(&self, expected_prev: &Digest) -> Result<(), String> {
        self.verify_content()?;
        if self.header.prev() != *expected_prev {
            return Err(format!(
                "prev mismatch at slot {}: expected {} but got {}",
                self.header.height(),
                hex::encode(expected_prev),
                hex::encode(self.header.prev())
            ));
        }
        Ok(())
    }

    /// The position-free checks: head = entry's head, root = entry's root.
    pub fn verify_content(&self) -> Result<(), String> {
        if self.header.head() != entry_head(&self.entry) {
            return Err(format!("head mismatch at slot {}", self.header.height()));
        }
        let computed_root = entry_root(&self.entry);
        if computed_root != self.header.root() {
            return Err(format!(
                "root mismatch at slot {}: header says {} but hash(entry) = {}",
                self.header.height(),
                hex::encode(self.header.root()),
                hex::encode(computed_root)
            ));
        }
        Ok(())
    }

    /// The seal: the attestation opens every chunk of the header under the
    /// slot's table (the table's epoch must be the slot).
    pub fn verify_seal(&self, table: &EpochTable) -> Result<(), String> {
        if table.index != self.header.height() as u64 {
            return Err(format!(
                "table epoch {} is not slot {}",
                table.index,
                self.header.height()
            ));
        }
        if table.chunks != HEADER_CHUNKS {
            return Err(format!(
                "table has {} chunks, the header has {HEADER_CHUNKS}",
                table.chunks
            ));
        }
        if !self.attestation.verify(table, self.header.as_bytes()) {
            return Err(format!(
                "attestation does not open the header at slot {}",
                self.header.height()
            ));
        }
        Ok(())
    }
}

/// The genesis block: slot 0, prev = all-zeros, empty entry, attested at
/// epoch 0 under the venue's `content` key, sealed by `member` (index
/// `member_index`, member 0 in the harness). Returns the block and its
/// epoch table (registry data).
pub fn genesis(content: &Attester, member: &Member, member_index: usize) -> (SealedBlock, EpochTable) {
    let entry = vec![];
    let header = Header::new(
        &[0u8; DIGEST_BYTES],
        &entry_root(&entry),
        &[0u8; HEAD_BYTES],
        0,
    );
    let table = content.epoch_table(0, HEADER_CHUNKS);
    let attestation = content.attest(&table, header.as_bytes());
    (
        SealedBlock {
            header,
            entry,
            attestation,
            proposer: member_index,
            proposer_secret: member.proposer.flag_secret(0),
        },
        table,
    )
}

/// The sealer: the venue's shared content key and the roster's members,
/// accepting pending entries, building blocks and attesting them. Any
/// member seals any slot (D53); the harness's default preference is
/// `slot mod n`, skipping silent members (`seal_next`), or an explicit
/// member (`seal_by`). One block per slot on a constant cadence — empty
/// blocks seal empty slots (see the crate docs: cadence is the default,
/// not a validity rule). Every non-silent member flags a slot that
/// passed its deadline empty ([`PosMiner::flag`], D50).
pub struct PosMiner {
    content: Attester,
    members: Vec<Member>,
    roster: Roster,
    silent: HashSet<usize>,
    /// The content table per slot, computed once (a table is ~100 ms of
    /// curve arithmetic; announcing and sealing share it).
    tables: HashMap<u32, EpochTable>,
    /// The slot of the last sealed block.
    pub height: u32,
    pub tip: Digest,
    pending: Vec<Vec<u8>>,
}

impl PosMiner {
    /// The venue: its content key from `content_seed` (shared by the
    /// members) and its `members`, checkpointed on genesis.
    pub fn new(content_seed: [u8; 32], members: Vec<Member>, genesis_digest: Digest, genesis_height: u32) -> PosMiner {
        let roster = Roster::new(members.iter().map(Member::public).collect());
        PosMiner { content: Attester::new(content_seed), members, roster, silent: HashSet::new(), tables: HashMap::new(), height: genesis_height, tip: genesis_digest, pending: Vec::new() }
    }

    /// A one-member venue from a seed (the content key and the member both
    /// from it).
    pub fn single(seed: [u8; 32], genesis_digest: Digest, genesis_height: u32) -> PosMiner {
        PosMiner::new(seed, vec![Member::new(seed)], genesis_digest, genesis_height)
    }

    /// The shared content key (every member holds it).
    pub fn content(&self) -> &Attester {
        &self.content
    }

    pub fn roster(&self) -> &Roster {
        &self.roster
    }

    pub fn members(&self) -> &[Member] {
        &self.members
    }

    pub fn member(&self, i: usize) -> &Member {
        &self.members[i]
    }

    pub fn n(&self) -> usize {
        self.members.len()
    }

    /// Member `i` goes silent: it seals nothing and flags nothing until
    /// [`PosMiner::wake`].
    pub fn silence(&mut self, i: usize) {
        assert!(i < self.members.len());
        self.silent.insert(i);
    }

    pub fn wake(&mut self, i: usize) {
        self.silent.remove(&i);
    }

    pub fn is_silent(&self, i: usize) -> bool {
        self.silent.contains(&i)
    }

    /// The harness's default sealer for `slot`: the member `slot mod n`
    /// if it is live, else the next live one; `None` if all are silent.
    pub fn default_sealer(&self, slot: u32) -> Option<usize> {
        let n = self.n();
        (0..n).map(|k| (slot as usize + k) % n).find(|i| !self.silent.contains(i))
    }

    /// The content table for `slot`, computed once.
    pub fn table(&mut self, slot: u32) -> &EpochTable {
        let content = &self.content;
        self.tables.entry(slot).or_insert_with(|| content.epoch_table(u64::from(slot), HEADER_CHUNKS))
    }

    /// The content tables for slots `0..=max_slot` and every member's
    /// signed announcement over them.
    pub fn announce(&mut self, max_slot: u32) -> (Vec<EpochTable>, Vec<MemberPublic>) {
        let tables: Vec<EpochTable> = (0..=max_slot).map(|s| self.table(s).clone()).collect();
        let anns = self.members.iter().map(|m| m.announce(&tables, max_slot)).collect();
        (tables, anns)
    }

    /// The registry for slots `0..=max_slot`, as a client or contract
    /// builds it from the announcements.
    pub fn registry(&mut self, max_slot: u32) -> anyhow::Result<Registry> {
        let (tables, anns) = self.announce(max_slot);
        Registry::build(self.roster.clone(), &tables, &anns, max_slot)
    }

    /// Member `i`'s proposer scalar for `slot` (what its block reveals;
    /// fixtures that build blocks by hand need it).
    pub fn proposer_secret(&self, i: usize, slot: u32) -> SecretKey {
        self.members[i].proposer.flag_secret(u64::from(slot))
    }

    /// The flags for `slot` (D50): every non-silent member's flag scalar
    /// (index member), `None` for a silent one. Called by the world once
    /// the slot has passed its deadline empty — the members' statement.
    pub fn flag(&self, slot: u32) -> Vec<Option<SecretKey>> {
        (0..self.members.len()).map(|i| (!self.silent.contains(&i)).then(|| self.members[i].flags.flag_secret(u64::from(slot)))).collect()
    }

    /// Submit an entry to be included in the next sealed block.
    pub fn submit(&mut self, entry: Vec<u8>) {
        self.pending.push(entry);
    }

    /// How many entries are waiting.
    pub fn pending_count(&self) -> usize {
        self.pending.len()
    }

    /// Seal the block at `slot` by the default sealer: the first pending
    /// entry, or an empty block (the cadence default). Returns the block
    /// and its content table (registry data the venue publishes
    /// alongside). `slot` must follow the last sealed slot; if every
    /// member is silent nothing seals.
    pub fn seal_next(&mut self, slot: u32) -> Result<(SealedBlock, EpochTable), String> {
        let i = self.default_sealer(slot).ok_or_else(|| format!("slot {slot}: every member is silent"))?;
        self.seal_by(slot, i)
    }

    /// Seal the block at `slot` by member `i` (any member may; a silent
    /// one does not).
    pub fn seal_by(&mut self, slot: u32, i: usize) -> Result<(SealedBlock, EpochTable), String> {
        if slot <= self.height {
            return Err(format!(
                "slot {slot} does not follow the tip slot {}",
                self.height
            ));
        }
        if i >= self.members.len() {
            return Err(format!("no member {i}"));
        }
        if self.silent.contains(&i) {
            return Err(format!("slot {slot}: member {i} is silent"));
        }
        let entry = if self.pending.is_empty() {
            Vec::new()
        } else {
            self.pending.remove(0)
        };
        let header = Header::new(&self.tip, &entry_root(&entry), &entry_head(&entry), slot);
        let table = self.table(slot).clone();
        let attestation = self.content.attest(&table, header.as_bytes());
        self.tip = header.digest();
        self.height = slot;
        Ok((
            SealedBlock {
                header,
                entry,
                attestation,
                proposer: i,
                proposer_secret: self.proposer_secret(i, slot),
            },
            table,
        ))
    }
}

/// What an observed sealed block turned out to be.
#[derive(Debug, PartialEq, Eq)]
pub enum Observation {
    /// Extends the verified tip (or the checkpoint).
    ExtendsTip,
    /// Already held: the same header at that slot.
    Known,
    /// A second, DIFFERENT attested header at a slot we already hold: the
    /// venue equivocated. Both headers open under the same content table,
    /// which is the clean on-chain slash case (`lngap_ec_wots::slash_leaf`)
    /// and, since D48/D53, ejection evidence against the second block's
    /// named proposer.
    Equivocation(Equivocation),
    /// The block continues a held non-tip header while we hold a different
    /// continuation: a chain-level fork. Distinct from same-slot
    /// equivocation (the two successors have different slots); slash-relevant
    /// through the venue's fork-choice rule rather than the per-epoch leaf.
    Fork(Fork),
}

/// Two conflicting attested headers at one slot, and the member whose
/// proposer reveal the SECOND carries.
#[derive(Debug, PartialEq, Eq)]
pub struct Equivocation {
    pub slot: u32,
    pub member: usize,
    /// The header the client already held.
    pub first: Header,
    /// The newly observed conflicting header.
    pub second: Header,
}

/// Two attested continuations of one parent: the held one and the new one.
#[derive(Debug, PartialEq, Eq)]
pub struct Fork {
    pub parent_slot: u32,
    /// The continuation the client already holds.
    pub first: Header,
    /// The newly observed conflicting continuation.
    pub second: Header,
}

/// A PoS venue client: verifies structure and seals, tracks the chain.
#[derive(Clone, Debug, Default)]
pub struct PosClient {
    /// Verified headers in slot order.
    pub headers: Vec<Header>,
    /// The checkpoint the client started from (slot, digest).
    pub checkpoint: (u32, Digest),
}

impl PosClient {
    /// Start from a checkpoint.
    pub fn from_checkpoint(slot: u32, digest: Digest) -> Self {
        PosClient {
            headers: Vec::new(),
            checkpoint: (slot, digest),
        }
    }

    /// The tip digest (or the checkpoint if no blocks verified yet).
    pub fn tip(&self) -> Digest {
        self.headers
            .last()
            .map(|h| h.digest())
            .unwrap_or(self.checkpoint.1)
    }

    /// The tip slot.
    pub fn tip_height(&self) -> u32 {
        self.headers
            .last()
            .map(|h| h.height())
            .unwrap_or(self.checkpoint.0)
    }

    /// Find the header at a given slot, if verified.
    pub fn header_at(&self, slot: u32) -> Option<&Header> {
        self.headers.iter().find(|h| h.height() == slot)
    }

    /// Number of headers since the checkpoint.
    pub fn chain_length(&self) -> usize {
        self.headers.len()
    }

    /// The headers from the checkpoint to the tip.
    pub fn chain_headers(&self) -> &[Header] {
        &self.headers
    }

    /// The registry's content table for the block's slot, after checking
    /// the block's proposer reveal; a block at a slot beyond the registry
    /// is not verifiable.
    fn slot_table<'r>(block: &SealedBlock, registry: &'r Registry) -> Result<&'r EpochTable, String> {
        let slot = block.header.height();
        if slot > registry.max_slot() {
            return Err(format!("slot {slot} is beyond the registry (0..={})", registry.max_slot()));
        }
        block.verify_proposer(registry)?;
        Ok(registry.table(slot))
    }

    /// Verify and append a block extending the tip: structure, the
    /// proposer reveal against the named member's point, the seal under
    /// the slot's shared content table, and a strictly increasing slot.
    pub fn verify_and_append(
        &mut self,
        block: &SealedBlock,
        registry: &Registry,
    ) -> Result<(), String> {
        let expected_prev = self.tip();
        block.verify_structure(&expected_prev)?;
        block.verify_seal(Self::slot_table(block, registry)?)?;
        if block.header.height() <= self.tip_height() {
            return Err(format!(
                "slot {} does not follow the tip slot {}",
                block.header.height(),
                self.tip_height()
            ));
        }
        self.headers.push(block.header.clone());
        Ok(())
    }

    /// Observe a sealed block that names its own parent — possibly a fork.
    /// The parent is found BY the prev link: a held header, or the
    /// checkpoint. The result says whether the block extends the tip, is
    /// already known, equivocates at a held slot (naming the block's
    /// proposer), or forks a held parent.
    pub fn observe(&self, block: &SealedBlock, registry: &Registry) -> Result<Observation, String> {
        let slot = block.header.height();
        let table = Self::slot_table(block, registry)?;
        let parent_slot = if block.header.prev() == self.checkpoint.1 {
            self.checkpoint.0
        } else {
            match self
                .headers
                .iter()
                .find(|h| h.digest() == block.header.prev())
            {
                Some(p) => p.height(),
                None => return Err(format!("unknown parent for slot {slot}")),
            }
        };
        if slot <= parent_slot {
            return Err(format!(
                "slot {slot} does not follow its parent slot {parent_slot}"
            ));
        }
        block.verify_content()?;
        block.verify_seal(table)?;
        if let Some(held) = self.header_at(slot) {
            return if held.digest() == block.header.digest() {
                Ok(Observation::Known)
            } else {
                Ok(Observation::Equivocation(Equivocation {
                    slot,
                    member: block.proposer,
                    first: held.clone(),
                    second: block.header.clone(),
                }))
            };
        }
        if block.header.prev() == self.tip() {
            return Ok(Observation::ExtendsTip);
        }
        // The parent is held but the block enters history behind the tip:
        // the held chain continues the parent with a different block.
        let held_successor = self
            .headers
            .iter()
            .find(|h| h.prev() == block.header.prev())
            .expect("the held parent has a held successor")
            .clone();
        Ok(Observation::Fork(Fork {
            parent_slot,
            first: held_successor,
            second: block.header.clone(),
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEED: [u8; 32] = [7u8; 32];
    const MAX_SLOT: u32 = 12;

    /// A running start: genesis sealed by member 0 of a 3-member roster
    /// under the shared content key, a miner, a client checkpointed on it
    /// (the ChainClient idiom: the checkpoint is not itself a held
    /// header), and the registry.
    fn boot() -> (PosMiner, PosClient, Registry) {
        let members: Vec<Member> = (0..3u8).map(|i| Member::new([SEED[0] + i; 32])).collect();
        let (gen, _table0) = genesis(&Attester::new(SEED), &members[0], 0);
        let client = PosClient::from_checkpoint(0, gen.header.digest());
        let mut miner = PosMiner::new(SEED, members, gen.header.digest(), 0);
        let registry = miner.registry(MAX_SLOT).unwrap();
        (miner, client, registry)
    }

    /// A block by hand: `entry` at `slot` on `parent`, attested under the
    /// shared key, tagged by member `i`.
    fn block_by(miner: &mut PosMiner, i: usize, slot: u32, parent: &Digest, entry: Vec<u8>) -> SealedBlock {
        let header = Header::new(parent, &entry_root(&entry), &entry_head(&entry), slot);
        let table = miner.table(slot).clone();
        let attestation = miner.content().attest(&table, header.as_bytes());
        SealedBlock { header, entry, attestation, proposer: i, proposer_secret: miner.proposer_secret(i, slot) }
    }

    #[test]
    fn genesis_verifies() {
        let (gen, table0) = genesis(&Attester::new(SEED), &Member::new(SEED), 0);
        gen.verify_structure(&[0u8; DIGEST_BYTES]).unwrap();
        gen.verify_seal(&table0).unwrap();
        assert_eq!(gen.header.height(), 0);
        assert_eq!(gen.header.head(), [0u8; HEAD_BYTES]);
    }

    #[test]
    fn cadence_seals_empty_slots() {
        let (mut miner, mut client, reg) = boot();
        // Nothing pending: the slot still gets its (empty) block.
        let (b1, t1) = miner.seal_next(1).unwrap();
        assert!(b1.entry.is_empty());
        assert_eq!(b1.header.head(), [0u8; HEAD_BYTES]);
        assert_eq!(&t1, reg.table(1), "sealed under the slot's shared table");
        assert_eq!(b1.proposer, 1, "the default sealer prefers slot mod n");
        client.verify_and_append(&b1, &reg).unwrap();
    }

    /// Any member seals any slot; the block's proposer reveal must open
    /// the named member's point; a silent member is skipped by the default
    /// sealer and flags nothing; a slot beyond the registry is
    /// unverifiable.
    #[test]
    fn any_member_seals_and_is_named() {
        let (mut miner, mut client, reg) = boot();
        // slot 1 by member 2 (off the default preference): fine
        let (b1, _) = miner.seal_by(1, 2).unwrap();
        assert_eq!(b1.proposer, 2);
        client.verify_and_append(&b1, &reg).unwrap();
        // a block whose proposer tag does not open the named member's point
        let mut forged = block_by(&mut miner, 0, 2, &client.tip(), Vec::new());
        forged.proposer = 1; // claims member 1 with member 0's scalar
        assert!(client.verify_and_append(&forged, &reg).unwrap_err().contains("does not open member 1"));
        assert!(client.observe(&forged, &reg).is_err());
        let mut forged = block_by(&mut miner, 0, 2, &client.tip(), Vec::new());
        forged.proposer = 7;
        assert!(client.verify_and_append(&forged, &reg).unwrap_err().contains("not a member"));
        // member 2 goes silent: slot 2 (its preferred slot) is sealed by member 0
        miner.silence(2);
        assert_eq!(miner.default_sealer(2), Some(0));
        assert!(miner.seal_by(2, 2).err().expect("silent").contains("silent"));
        let (b2, _) = miner.seal_next(2).unwrap();
        assert_eq!(b2.proposer, 0);
        client.verify_and_append(&b2, &reg).unwrap();
        let flags = miner.flag(3);
        assert!(flags[0].is_some() && flags[1].is_some() && flags[2].is_none());
        // everyone silent: nothing seals
        miner.silence(0);
        miner.silence(1);
        assert!(miner.seal_next(3).err().expect("all silent").contains("every member"));
        miner.wake(0);
        miner.wake(1);
        miner.wake(2);
        for s in 3..=MAX_SLOT {
            let (b, _) = miner.seal_next(s).unwrap();
            client.verify_and_append(&b, &reg).unwrap();
        }
        let (b13, _) = miner.seal_next(MAX_SLOT + 1).unwrap();
        assert!(client.verify_and_append(&b13, &reg).unwrap_err().contains("beyond the registry"));
    }

    #[test]
    fn chain_verifies_with_gaps() {
        let (mut miner, mut client, reg) = boot();
        miner.submit(b"move at slot 1".to_vec());
        miner.submit(b"move at slot 3".to_vec());
        miner.submit(b"move at slot 7".to_vec());
        let (b1, t1) = miner.seal_next(1).unwrap();
        let (b3, t3) = miner.seal_next(3).unwrap();
        let (b7, t7) = miner.seal_next(7).unwrap();
        // Gaps are legal to the client: validity is strictly-increasing
        // slots, not density (cadence is the sealer's default, not a rule).
        for (b, t) in [(&b1, &t1), (&b3, &t3), (&b7, &t7)] {
            assert_eq!(t, reg.table(b.header.height()));
            client.verify_and_append(b, &reg).unwrap();
        }
        assert_eq!(client.tip_height(), 7);
        assert_eq!(client.chain_length(), 3);
        assert_ne!(client.header_at(1).unwrap().head(), [0u8; HEAD_BYTES]);
        assert!(client.header_at(2).is_none());
    }

    #[test]
    fn non_increasing_slot_rejected() {
        let (mut miner, mut client, reg) = boot();
        miner.submit(b"a".to_vec());
        miner.submit(b"b".to_vec());
        let (b3, _t3) = miner.seal_next(3).unwrap();
        // Miner-side: the next seal must follow slot 3.
        assert!(miner.seal_next(3).is_err());
        assert!(miner.seal_next(2).is_err());
        // Client-side: a block at a held-or-earlier slot does not append.
        client.verify_and_append(&b3, &reg).unwrap();
        assert!(client.verify_and_append(&b3, &reg).is_err());
    }

    #[test]
    fn seal_rejects_tampered_header() {
        let (mut miner, client, _reg) = boot();
        miner.submit(b"x".to_vec());
        let (mut block, table) = miner.seal_next(1).unwrap();
        // Flip a byte in the pad field (the old nonce): the structural
        // checks do not read it, so only the seal can catch this.
        block.header.0[95] ^= 1;
        block
            .verify_structure(&client.tip())
            .expect("structure passes");
        assert!(block.verify_seal(&table).is_err());
    }

    #[test]
    fn seal_rejects_wrong_epoch_table() {
        let (mut miner, _client, _reg) = boot();
        miner.submit(b"x".to_vec());
        let (block, _table) = miner.seal_next(1).unwrap();
        let wrong = miner.content().epoch_table(99, HEADER_CHUNKS);
        assert!(block.verify_seal(&wrong).is_err());
    }

    #[test]
    fn structure_rejects_tampered_entry() {
        let (mut miner, client, _reg) = boot();
        miner.submit(b"some move".to_vec());
        let (mut block, _table) = miner.seal_next(1).unwrap();
        block.entry[0] ^= 1;
        assert!(block.verify_structure(&client.tip()).is_err());
    }

    #[test]
    fn equivocation_is_detected() {
        let (mut miner, mut client, reg) = boot();
        miner.submit(b"move A".to_vec());
        let (block_a, table) = miner.seal_next(1).unwrap();
        client.verify_and_append(&block_a, &reg).unwrap();

        // Member 2 equivocates at slot 1: a second, different block at
        // slot 1, attested under the SAME (shared) table, tagged by it.
        let prev = client.checkpoint.1;
        let block_b = block_by(&mut miner, 2, 1, &prev, b"move B".to_vec());
        let _ = &table;
        // Both verify in isolation...
        block_b.verify_structure(&prev).unwrap();
        block_b.verify_seal(&table).unwrap();
        // ...and the client names the equivocation and the second block's
        // proposer.
        match client.observe(&block_b, &reg) {
            Ok(Observation::Equivocation(e)) => {
                assert_eq!(e.slot, 1);
                assert_eq!(e.member, 2);
                assert_eq!(e.first, block_a.header);
                assert_eq!(e.second, block_b.header);
            }
            other => panic!("expected equivocation, got {other:?}"),
        }
        // Re-observing the held block is just Known.
        assert_eq!(
            client.observe(&block_a, &reg).unwrap(),
            Observation::Known
        );
    }

    #[test]
    fn fork_is_detected() {
        let (mut miner, mut client, reg) = boot();
        miner.submit(b"move at 1".to_vec());
        miner.submit(b"move at 7".to_vec());
        let (b1, _t1) = miner.seal_next(1).unwrap();
        let (b7, _t7) = miner.seal_next(7).unwrap();
        client.verify_and_append(&b1, &reg).unwrap();
        client.verify_and_append(&b7, &reg).unwrap();

        // A block appears continuing slot 1 while we hold the slot-7
        // continuation: a fork, with no same-slot clash.
        let block_c = block_by(&mut miner, 1, 4, &b1.header.digest(), b"fork move at 4".to_vec());
        block_c.verify_seal(reg.table(4)).unwrap();
        match client.observe(&block_c, &reg) {
            Ok(Observation::Fork(f)) => {
                assert_eq!(f.parent_slot, 1);
                assert_eq!(f.first, b7.header);
                assert_eq!(f.second, block_c.header);
            }
            other => panic!("expected fork, got {other:?}"),
        }
    }
}
