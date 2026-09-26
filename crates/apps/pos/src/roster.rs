//! The roster: the venue as members with ONE shared content key (D51,
//! D53). No signing session, no DKG: the content attestation of every
//! slot is EC-OTS under a key every member holds (a 1-of-n key is a
//! shared secret), so the contract pins ONE table per slot and does not
//! care which member opens it. Everything that must NAME a member is a
//! one-bit statement beside it — a per-member per-slot point whose
//! scalar the member reveals:
//!
//! - the PROPOSER point `P_{i,s}` ("I sealed slot s"), revealed by the
//!   member that seals and carried by its block; the refute leaf requires
//!   a signature under one of the n points (`graph::proposer_fragment`),
//!   so every refutation names its proposer;
//! - the FLAG point `F_{i,s}` ("slot s was empty at its deadline", D50),
//!   revealed by every member that saw it.
//!
//! - [`Member`]: the venue side — a plain BIP340 member key (what an
//!   announcement is signed with, and what ejection names), its proposer
//!   keys and its flag keys.
//! - [`MemberPublic`]: the member's signed announcement — the DIGESTS of
//!   the shared content tables (every member co-signs the content
//!   registry) and its proposer and flag points for every slot.
//! - [`Roster`]: the member keys; the majority threshold.
//! - [`Registry`]: what a contract pins at open and a client verifies
//!   seals against — per slot the shared table and every member's
//!   proposer and flag points.
//!
//! Any member seals any slot; the schedule, if the venue keeps one, is
//! its own business (the harness prefers `slot mod n` and skips silent
//! members). A silent member costs nothing: inclusion liveness is 1-of-n
//! per slot.

use anyhow::{ensure, Result};
use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::secp256k1::{Message, SecretKey, SECP256K1};
use lngap_ec_wots::{EpochTable, FlagKeys};

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

/// One venue member's secrets: its member key, its proposer keys and its
/// flag keys — all derived from one seed. (The content key is the
/// venue's, shared: `PosMiner::content`.)
pub struct Member {
    pub key: Keypair,
    /// One point per slot: "I sealed slot s", revealed by the block.
    pub proposer: FlagKeys,
    /// One point per slot: "slot s was empty at its deadline" (D50).
    pub flags: FlagKeys,
}

impl Member {
    pub fn new(seed: [u8; 32]) -> Member {
        let sk = SecretKey::from_slice(&tagged("lngap/roster/member", &[&seed])).expect("a tagged hash is a key");
        Member {
            key: Keypair::from_secret_key(SECP256K1, &sk),
            proposer: FlagKeys::new(tagged("lngap/roster/proposer", &[&seed])),
            flags: FlagKeys::new(tagged("lngap/roster/flags", &[&seed])),
        }
    }

    pub fn public(&self) -> XOnlyPublicKey {
        self.key.x_only_public_key().0
    }

    /// The member's signed announcement over the shared content
    /// `tables` (index slot; their digests are what it signs) and its
    /// proposer and flag points for every slot `0..=max_slot`.
    pub fn announce(&self, tables: &[EpochTable], max_slot: u32) -> MemberPublic {
        assert!(tables.len() > max_slot as usize, "tables for slots 0..={max_slot}");
        let table_digests: Vec<[u8; 32]> = tables[..=max_slot as usize].iter().map(EpochTable::digest).collect();
        let proposer_points: Vec<XOnlyPublicKey> = (0..=max_slot).map(|s| self.proposer.flag_point(u64::from(s))).collect();
        let flag_points: Vec<XOnlyPublicKey> = (0..=max_slot).map(|s| self.flags.flag_point(u64::from(s))).collect();
        let msg = MemberPublic::message(&self.public(), &table_digests, &proposer_points, &flag_points);
        let sig = SECP256K1.sign_schnorr(&msg, &self.key);
        MemberPublic { key: self.public(), table_digests, proposer_points, flag_points, sig }
    }
}

/// A member's announced registry data, signed under its member key.
#[derive(Clone, Debug)]
pub struct MemberPublic {
    pub key: XOnlyPublicKey,
    /// The digest of the shared content table per slot (index slot): the
    /// member's co-signature of the content registry.
    pub table_digests: Vec<[u8; 32]>,
    /// The member's proposer point per slot (index slot).
    pub proposer_points: Vec<XOnlyPublicKey>,
    /// The member's flag point per slot (index slot).
    pub flag_points: Vec<XOnlyPublicKey>,
    pub sig: Signature,
}

impl MemberPublic {
    fn message(key: &XOnlyPublicKey, digests: &[[u8; 32]], proposer_points: &[XOnlyPublicKey], flag_points: &[XOnlyPublicKey]) -> Message {
        let mut eng = sha256::Hash::engine();
        eng.input(&key.serialize());
        eng.input(&(digests.len() as u64).to_be_bytes());
        for d in digests {
            eng.input(d);
        }
        eng.input(&(proposer_points.len() as u64).to_be_bytes());
        for p in proposer_points {
            eng.input(&p.serialize());
        }
        eng.input(&(flag_points.len() as u64).to_be_bytes());
        for f in flag_points {
            eng.input(&f.serialize());
        }
        Message::from_digest(tagged("lngap/roster/announce", &[sha256::Hash::from_engine(eng).as_ref()]))
    }

    /// The signature opens the member key over exactly this data.
    pub fn verify(&self) -> Result<()> {
        let msg = Self::message(&self.key, &self.table_digests, &self.proposer_points, &self.flag_points);
        SECP256K1.verify_schnorr(&self.sig, &msg, &self.key).map_err(|e| anyhow::anyhow!("announcement signature: {e}"))
    }
}

/// The member keys.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Roster {
    pub members: Vec<XOnlyPublicKey>,
}

impl Roster {
    pub fn new(members: Vec<XOnlyPublicKey>) -> Roster {
        assert!(!members.is_empty(), "a roster has at least one member");
        assert!(members.len() <= 16, "the proposer fragment indexes members by a nibble");
        Roster { members }
    }

    pub fn n(&self) -> usize {
        self.members.len()
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

/// One slot's registry entry: the shared content table, and every
/// member's proposer and flag points for it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct SlotEntry {
    pub table: EpochTable,
    pub proposers: Vec<XOnlyPublicKey>,
    pub flags: Vec<XOnlyPublicKey>,
}

/// The registry a contract pins at open and a client verifies seals
/// against: per slot the shared content table (co-signed by every
/// member), the proposer points and the flag points of every member;
/// plus the flag threshold.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Registry {
    pub roster: Roster,
    pub threshold: u32,
    slots: Vec<SlotEntry>,
}

impl Registry {
    /// Build from the shared content `tables` (index slot) and verified
    /// announcements (one per member, roster order): every member must
    /// have co-signed every table's digest and announced its points for
    /// every slot `0..=max_slot`. The threshold is the majority.
    pub fn build(roster: Roster, tables: &[EpochTable], announcements: &[MemberPublic], max_slot: u32) -> Result<Registry> {
        ensure!(announcements.len() == roster.n(), "{} announcements for {} members", announcements.len(), roster.n());
        ensure!(tables.len() > max_slot as usize, "content tables for slots 0..={max_slot} required");
        for (s, t) in tables.iter().enumerate().take(max_slot as usize + 1) {
            ensure!(t.index == s as u64 && t.chunks == HEADER_CHUNKS, "slot {s}: the content table is not slot {s}'s");
        }
        for (i, a) in announcements.iter().enumerate() {
            ensure!(a.key == roster.members[i], "announcement {i} is not under member {i}'s key");
            a.verify()?;
            ensure!(a.table_digests.len() > max_slot as usize && a.proposer_points.len() > max_slot as usize && a.flag_points.len() > max_slot as usize, "member {i}: announcement covers too few slots");
            for s in 0..=max_slot as usize {
                ensure!(a.table_digests[s] == tables[s].digest(), "member {i} did not co-sign slot {s}'s content table");
            }
        }
        let slots = (0..=max_slot as usize)
            .map(|s| SlotEntry {
                table: tables[s].clone(),
                proposers: announcements.iter().map(|a| a.proposer_points[s]).collect(),
                flags: announcements.iter().map(|a| a.flag_points[s]).collect(),
            })
            .collect();
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

    /// The shared content table for `slot`.
    pub fn table(&self, slot: u32) -> &EpochTable {
        &self.entry(slot).table
    }

    /// Every member's proposer point for `slot` (index member).
    pub fn proposers(&self, slot: u32) -> &[XOnlyPublicKey] {
        &self.entry(slot).proposers
    }

    /// Every member's flag point for `slot` (index member).
    pub fn flags(&self, slot: u32) -> &[XOnlyPublicKey] {
        &self.entry(slot).flags
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lngap_ec_wots::Attester;

    fn members(n: u8) -> Vec<Member> {
        (0..n).map(|i| Member::new([0x30 + i; 32])).collect()
    }

    #[test]
    fn majority() {
        for (n, t) in [(1usize, 1u32), (2, 2), (3, 2), (4, 3), (5, 3), (15, 8), (16, 9)] {
            assert_eq!(Roster::majority(n), t, "n = {n}");
            let late = n as u32 - t + 1; // a standing late attestation's abstainers
            assert!(late == t || late + 1 == t, "n = {n}: {t} vs {late}");
        }
    }

    #[test]
    fn registry_from_verified_announcements() {
        let ms = members(5);
        let roster = Roster::new(ms.iter().map(Member::public).collect());
        let content = Attester::new([0x99; 32]);
        let max_slot = 9;
        let tables: Vec<EpochTable> = (0..=max_slot as u64).map(|s| content.epoch_table(s, HEADER_CHUNKS)).collect();
        let anns: Vec<MemberPublic> = ms.iter().map(|m| m.announce(&tables, max_slot)).collect();
        let reg = Registry::build(roster.clone(), &tables, &anns, max_slot).unwrap();
        assert_eq!(reg.threshold, 3);
        assert_eq!(reg.max_slot(), 9);
        for s in 0..=max_slot {
            assert_eq!(reg.table(s), &tables[s as usize]);
            assert_eq!(reg.proposers(s).len(), 5);
            assert_eq!(reg.proposers(s)[3], ms[3].proposer.flag_point(u64::from(s)));
            assert_eq!(reg.flags(s)[3], ms[3].flags.flag_point(u64::from(s)));
            assert_ne!(reg.proposers(s)[3], reg.flags(s)[3]);
        }
        // an announcement under the wrong key
        let mut bad = anns.clone();
        bad.swap(0, 1);
        assert!(Registry::build(roster.clone(), &tables, &bad, max_slot).is_err());
        // a tampered announcement (one point replaced) fails its signature
        let mut bad = anns.clone();
        bad[2].proposer_points[4] = anns[3].proposer_points[4];
        assert!(Registry::build(roster.clone(), &tables, &bad, max_slot).is_err());
        // a member that co-signed a DIFFERENT content table for slot 4
        let mut other = tables.clone();
        other[4] = Attester::new([0x98; 32]).epoch_table(4, HEADER_CHUNKS);
        let mut bad = anns.clone();
        bad[1] = ms[1].announce(&other, max_slot);
        assert!(Registry::build(roster.clone(), &tables, &bad, max_slot).is_err());
        // too few slots announced
        let mut bad = anns.clone();
        bad[4] = ms[4].announce(&tables, 3);
        assert!(Registry::build(roster, &tables, &bad, max_slot).is_err());
    }
}
