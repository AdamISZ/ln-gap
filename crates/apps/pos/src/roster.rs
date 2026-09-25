//! The roster: the venue as a schedule of one-time attesters (D47, D48,
//! D51). No group key, no FROST, no DKG. Content is attested by ONE member
//! per slot under its own one-time table; time by every member's
//! individual flag (D50) counted in script. The venue is n members, a
//! schedule, Bitcoin as the clock.
//!
//! - [`Member`]: the venue side — a plain BIP340 member key (what a
//!   registry announcement is signed with, and what ejection names), its
//!   EC-OTS [`Attester`] (the tables of the slots it proposes) and its
//!   [`FlagKeys`] (one flag point per slot, every slot).
//! - [`MemberPublic`]: the member's signed announcement — its tables for
//!   the slots it is scheduled for and its flag points for every slot.
//!   Table ownership is not provable from the points alone (`S = R + e·P`
//!   with `R` unpublished), so the announcement's signature is what ties a
//!   table to a member.
//! - [`Roster`]: the member keys and the schedule — strict round robin,
//!   `proposer_at(slot) = slot mod n`, genesis by member 0. No backup, no
//!   window: a silent scheduled proposer stalls the mover, who loses by
//!   absence (the accepted limitation of this step; ROSTER_PLAN.md).
//! - [`Registry`]: what a contract pins at open and a client verifies
//!   seals against — per slot the scheduled member's table and every
//!   member's flag point, built from verified announcements; the flag
//!   threshold is the majority (D50 amended).

use anyhow::{bail, ensure, Result};
use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::secp256k1::{Message, SecretKey, SECP256K1};
use lngap_ec_wots::{Attester, EpochTable, FlagKeys};

use crate::HEADER_CHUNKS;

fn tagged(tag: &str, parts: &[&[u8]]) -> [u8; 32] {
    let th = sha256::Hash::hash(tag.as_bytes());
    let mut eng = sha256::Hash::engine();
    eng.input(th.as_ref());
    eng.input(th.as_ref());
    for p in parts {
        eng.input(p);
    }
    sha256::Hash::from_engine(eng).to_byte_array()
}

/// One venue member's secrets: its member key, its attester, its flag keys
/// — all derived from one seed.
pub struct Member {
    pub key: Keypair,
    pub attester: Attester,
    pub flags: FlagKeys,
}

impl Member {
    pub fn new(seed: [u8; 32]) -> Member {
        let sk = SecretKey::from_slice(&tagged("lngap/roster/member", &[&seed])).expect("a tagged hash is a key");
        Member {
            key: Keypair::from_secret_key(SECP256K1, &sk),
            attester: Attester::new(tagged("lngap/roster/attester", &[&seed])),
            flags: FlagKeys::new(tagged("lngap/roster/flags", &[&seed])),
        }
    }

    pub fn public(&self) -> XOnlyPublicKey {
        self.key.x_only_public_key().0
    }

    /// The member's signed announcement: its epoch tables for `slots` (the
    /// slots the schedule gives it) and its flag points for every slot
    /// `0..=max_slot`.
    pub fn announce(&self, slots: impl IntoIterator<Item = u32>, max_slot: u32) -> MemberPublic {
        let tables: Vec<EpochTable> = slots.into_iter().map(|s| self.attester.epoch_table(u64::from(s), HEADER_CHUNKS)).collect();
        self.announce_tables(tables, max_slot)
    }

    /// As [`Member::announce`] with the tables already computed (they must
    /// be this member's).
    pub fn announce_tables(&self, tables: Vec<EpochTable>, max_slot: u32) -> MemberPublic {
        let flag_points: Vec<XOnlyPublicKey> = (0..=max_slot).map(|s| self.flags.flag_point(u64::from(s))).collect();
        let msg = MemberPublic::message(&self.public(), &tables, &flag_points);
        let sig = SECP256K1.sign_schnorr(&msg, &self.key);
        MemberPublic { key: self.public(), tables, flag_points, sig }
    }
}

/// A member's announced registry data, signed under its member key.
#[derive(Clone, Debug)]
pub struct MemberPublic {
    pub key: XOnlyPublicKey,
    /// The tables of the slots the member proposes (each table's `index`
    /// is its slot).
    pub tables: Vec<EpochTable>,
    /// The member's flag point per slot (index slot).
    pub flag_points: Vec<XOnlyPublicKey>,
    pub sig: Signature,
}

impl MemberPublic {
    fn message(key: &XOnlyPublicKey, tables: &[EpochTable], flag_points: &[XOnlyPublicKey]) -> Message {
        let mut eng = sha256::Hash::engine();
        eng.input(&key.serialize());
        eng.input(&(tables.len() as u64).to_be_bytes());
        for t in tables {
            eng.input(&t.digest());
        }
        eng.input(&(flag_points.len() as u64).to_be_bytes());
        for f in flag_points {
            eng.input(&f.serialize());
        }
        Message::from_digest(tagged("lngap/roster/announce", &[sha256::Hash::from_engine(eng).as_ref()]))
    }

    /// The signature opens the member key over exactly this data.
    pub fn verify(&self) -> Result<()> {
        let msg = Self::message(&self.key, &self.tables, &self.flag_points);
        SECP256K1.verify_schnorr(&self.sig, &msg, &self.key).map_err(|e| anyhow::anyhow!("announcement signature: {e}"))
    }

    pub fn table(&self, slot: u32) -> Option<&EpochTable> {
        self.tables.iter().find(|t| t.index == u64::from(slot))
    }
}

/// The member keys in schedule order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Roster {
    pub members: Vec<XOnlyPublicKey>,
}

impl Roster {
    pub fn new(members: Vec<XOnlyPublicKey>) -> Roster {
        assert!(!members.is_empty(), "a roster has at least one member");
        Roster { members }
    }

    pub fn n(&self) -> usize {
        self.members.len()
    }

    /// Strict round robin: slot `s` is proposed by member `s mod n`
    /// (genesis, slot 0, by member 0).
    pub fn proposer_at(&self, slot: u32) -> usize {
        slot as usize % self.n()
    }

    /// The slots in `0..=max_slot` member `i` proposes.
    pub fn slots_of(&self, i: usize, max_slot: u32) -> impl Iterator<Item = u32> + '_ {
        (0..=max_slot).filter(move |s| self.proposer_at(*s) == i)
    }

    /// The PoC's flag threshold: a simple majority, `⌈(n + 1) / 2⌉` (D50
    /// amended). The flag is one-sided — silence votes for presence — so
    /// false emptiness costs `t` flaggers and a standing late attestation
    /// `n − t + 1` abstainers plus the proposer; they balance at the
    /// majority and no `t` beats half.
    pub fn majority(n: usize) -> u32 {
        (n as u32 + 2) / 2
    }
}

/// One slot's registry entry: who proposes it, under which table, and
/// every member's flag point for it.
#[derive(Clone, Debug)]
pub struct SlotEntry {
    pub proposer: usize,
    pub table: EpochTable,
    pub flags: Vec<XOnlyPublicKey>,
}

/// The registry a contract pins at open and a client verifies seals
/// against: per slot the SCHEDULED member's announced table (a seal under
/// any other table is not this venue's), and the flag points of every
/// member; plus the flag threshold.
#[derive(Clone, Debug)]
pub struct Registry {
    pub roster: Roster,
    pub threshold: u32,
    slots: Vec<SlotEntry>,
}

impl Registry {
    /// Build from verified announcements (one per member, in roster
    /// order): every slot `0..=max_slot` must carry its scheduled member's
    /// table at that slot and every member's flag point. The threshold is
    /// the majority.
    pub fn build(roster: Roster, announcements: &[MemberPublic], max_slot: u32) -> Result<Registry> {
        ensure!(announcements.len() == roster.n(), "{} announcements for {} members", announcements.len(), roster.n());
        for (i, a) in announcements.iter().enumerate() {
            ensure!(a.key == roster.members[i], "announcement {i} is not under member {i}'s key");
            a.verify()?;
            ensure!(a.flag_points.len() > max_slot as usize, "member {i}: flag points for slots 0..={max_slot} required");
        }
        let mut slots = Vec::with_capacity(max_slot as usize + 1);
        for s in 0..=max_slot {
            let p = roster.proposer_at(s);
            let Some(table) = announcements[p].table(s) else {
                bail!("slot {s}: its scheduled proposer (member {p}) announced no table");
            };
            ensure!(table.chunks == HEADER_CHUNKS, "slot {s}: the table has {} chunks", table.chunks);
            slots.push(SlotEntry { proposer: p, table: table.clone(), flags: announcements.iter().map(|a| a.flag_points[s as usize]).collect() });
        }
        Ok(Registry { threshold: Roster::majority(roster.n()), roster, slots })
    }

    pub fn max_slot(&self) -> u32 {
        self.slots.len() as u32 - 1
    }

    pub fn n(&self) -> usize {
        self.roster.n()
    }

    pub fn entry(&self, slot: u32) -> &SlotEntry {
        &self.slots[slot as usize]
    }

    /// The scheduled member's table for `slot`.
    pub fn table(&self, slot: u32) -> &EpochTable {
        &self.entry(slot).table
    }

    /// Every member's flag point for `slot` (index member).
    pub fn flags(&self, slot: u32) -> &[XOnlyPublicKey] {
        &self.entry(slot).flags
    }

    pub fn proposer(&self, slot: u32) -> usize {
        self.entry(slot).proposer
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn members(n: u8) -> Vec<Member> {
        (0..n).map(|i| Member::new([0x30 + i; 32])).collect()
    }

    #[test]
    fn round_robin_and_majority() {
        let ms = members(5);
        let roster = Roster::new(ms.iter().map(Member::public).collect());
        for s in 0..20u32 {
            assert_eq!(roster.proposer_at(s), s as usize % 5);
        }
        assert_eq!(roster.slots_of(2, 12).collect::<Vec<_>>(), vec![2, 7, 12]);
        for (n, t) in [(1usize, 1u32), (2, 2), (3, 2), (4, 3), (5, 3), (15, 8), (16, 9), (100, 51)] {
            assert_eq!(Roster::majority(n), t, "n = {n}");
            let late = n as u32 - t + 1; // a standing late attestation's abstainers
            assert!(late == t || late + 1 == t, "n = {n}: {t} vs {late}");
        }
    }

    #[test]
    fn registry_from_verified_announcements() {
        let ms = members(5);
        let roster = Roster::new(ms.iter().map(Member::public).collect());
        let max_slot = 9;
        let anns: Vec<MemberPublic> = ms.iter().enumerate().map(|(i, m)| m.announce(roster.slots_of(i, max_slot), max_slot)).collect();
        let reg = Registry::build(roster.clone(), &anns, max_slot).unwrap();
        assert_eq!(reg.threshold, 3);
        assert_eq!(reg.max_slot(), 9);
        for s in 0..=max_slot {
            assert_eq!(reg.proposer(s), s as usize % 5);
            assert_eq!(reg.table(s).index, u64::from(s));
            assert_eq!(reg.table(s), &ms[s as usize % 5].attester.epoch_table(u64::from(s), HEADER_CHUNKS));
            assert_eq!(reg.flags(s).len(), 5);
            assert_eq!(reg.flags(s)[3], ms[3].flags.flag_point(u64::from(s)));
        }
        // an announcement under the wrong key
        let mut bad = anns.clone();
        bad.swap(0, 1);
        assert!(Registry::build(roster.clone(), &bad, max_slot).is_err());
        // a tampered announcement (one flag point replaced) fails its signature
        let mut bad = anns.clone();
        bad[2].flag_points[4] = anns[3].flag_points[4];
        assert!(Registry::build(roster.clone(), &bad, max_slot).is_err());
        // a member that announced no table for a slot it is scheduled for
        let mut bad = anns.clone();
        bad[4] = ms[4].announce([4u32], max_slot); // slot 9 missing
        assert!(Registry::build(roster.clone(), &bad, max_slot).is_err());
        // a member's table for a slot it does NOT propose is simply unused
        let mut extra = anns.clone();
        extra[1] = ms[1].announce([1u32, 2, 6], max_slot);
        assert_eq!(Registry::build(roster, &extra, max_slot).unwrap().table(2), reg.table(2));
    }
}
