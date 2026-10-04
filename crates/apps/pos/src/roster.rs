//! The roster: the venue as members with ONE shared content key (D51,
//! D53). No signing session, no DKG: the content attestation of every
//! `(contract, depth)` is EC-OTS under a key every member holds (a 1-of-n
//! key is a shared secret), so the contract pins ONE table per depth and
//! does not care which member opens it. Everything that must NAME a
//! member is a one-bit statement beside it — a per-member point per
//! `(contract, depth)` whose scalar the member reveals (D55: keyed by
//! `crate::key_index`, not by a venue slot):
//!
//! - the PROPOSER point `P_{i,s}` ("I sealed depth d of contract c"), revealed by the
//!   member that seals and carried by its block; the rebut leaf requires
//!   a signature under one of the n points (`graph::proposer_fragment`),
//!   so every rebuttal names its proposer;
//! - the FLAG point `F_{i,s}` ("no mover-signed entry for (c, d) at its
//!   deadline", D50, D55),
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
//!   seals against — per depth of ONE contract the shared table and every
//!   member's proposer and flag points.
//!
//! Any member seals any depth; the designated one is the rotation
//! (`crate::rotation`), the mover falling back along it (D55). A silent
//! member costs nothing: inclusion liveness is 1-of-n.

use anyhow::{ensure, Result};
use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::secp256k1::schnorr::Signature;
use bitcoin::secp256k1::{Message, SecretKey, SECP256K1};
use lngap_ec_wots::{EpochTable, FlagKeys};

use crate::{key_index, HEADER_CHUNKS};

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
    /// One point per `(c, d)`: "I sealed it", revealed by the seal.
    pub proposer: FlagKeys,
    /// One point per `(c, d)`: "no signed entry at its deadline" (D50).
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

    /// The member's signed announcement for contract `contract`: over the
    /// shared content `tables` (index depth; their digests are what it
    /// signs) and its proposer and flag points for every depth
    /// `0..=max_depth`.
    pub fn announce(&self, contract: u32, tables: &[EpochTable], max_depth: u32) -> MemberPublic {
        assert!(tables.len() > max_depth as usize, "tables for depths 0..={max_depth}");
        let table_digests: Vec<[u8; 32]> = tables[..=max_depth as usize].iter().map(EpochTable::digest).collect();
        let proposer_points: Vec<XOnlyPublicKey> = (0..=max_depth).map(|d| self.proposer.flag_point(key_index(contract, d))).collect();
        let flag_points: Vec<XOnlyPublicKey> = (0..=max_depth).map(|d| self.flags.flag_point(key_index(contract, d))).collect();
        let msg = MemberPublic::message(&self.public(), contract, &table_digests, &proposer_points, &flag_points);
        let sig = SECP256K1.sign_schnorr(&msg, &self.key);
        MemberPublic { key: self.public(), contract, table_digests, proposer_points, flag_points, sig }
    }
}

/// A member's announced registry data, signed under its member key.
#[derive(Clone, Debug)]
pub struct MemberPublic {
    pub key: XOnlyPublicKey,
    /// The contract the announcement is for.
    pub contract: u32,
    /// The digest of the shared content table per depth (index depth): the
    /// member's co-signature of the content registry.
    pub table_digests: Vec<[u8; 32]>,
    /// The member's proposer point per depth (index depth).
    pub proposer_points: Vec<XOnlyPublicKey>,
    /// The member's flag point per depth (index depth).
    pub flag_points: Vec<XOnlyPublicKey>,
    pub sig: Signature,
}

impl MemberPublic {
    fn message(key: &XOnlyPublicKey, contract: u32, digests: &[[u8; 32]], proposer_points: &[XOnlyPublicKey], flag_points: &[XOnlyPublicKey]) -> Message {
        let mut eng = sha256::Hash::engine();
        eng.input(&key.serialize());
        eng.input(&contract.to_be_bytes());
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
        let msg = Self::message(&self.key, self.contract, &self.table_digests, &self.proposer_points, &self.flag_points);
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

/// One depth's registry entry: the shared content table, and every
/// member's proposer and flag points for it.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DepthEntry {
    pub table: EpochTable,
    pub proposers: Vec<XOnlyPublicKey>,
    pub flags: Vec<XOnlyPublicKey>,
}

/// The registry a contract pins at open and a client verifies seals
/// against: for ONE contract, per depth the shared content table
/// (co-signed by every member), the proposer points and the flag points
/// of every member; plus the flag threshold.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct Registry {
    pub contract: u32,
    pub roster: Roster,
    pub threshold: u32,
    depths: Vec<DepthEntry>,
}

impl Registry {
    /// Build contract `contract`'s registry from the shared content
    /// `tables` (index depth) and verified announcements (one per member,
    /// roster order): every member must have co-signed every table's
    /// digest and announced its points for every depth `0..=max_depth`,
    /// all for this contract. The threshold is the majority.
    pub fn build(contract: u32, roster: Roster, tables: &[EpochTable], announcements: &[MemberPublic], max_depth: u32) -> Result<Registry> {
        ensure!(announcements.len() == roster.n(), "{} announcements for {} members", announcements.len(), roster.n());
        ensure!(tables.len() > max_depth as usize, "content tables for depths 0..={max_depth} required");
        for (d, t) in tables.iter().enumerate().take(max_depth as usize + 1) {
            ensure!(t.index == key_index(contract, d as u32) && t.chunks == HEADER_CHUNKS, "depth {d}: the content table is not contract {contract} depth {d}'s");
        }
        for (i, a) in announcements.iter().enumerate() {
            ensure!(a.key == roster.members[i], "announcement {i} is not under member {i}'s key");
            ensure!(a.contract == contract, "member {i} announced for contract {}, not {contract}", a.contract);
            a.verify()?;
            ensure!(a.table_digests.len() > max_depth as usize && a.proposer_points.len() > max_depth as usize && a.flag_points.len() > max_depth as usize, "member {i}: announcement covers too few depths");
            for d in 0..=max_depth as usize {
                ensure!(a.table_digests[d] == tables[d].digest(), "member {i} did not co-sign depth {d}'s content table");
            }
        }
        let depths = (0..=max_depth as usize)
            .map(|d| DepthEntry {
                table: tables[d].clone(),
                proposers: announcements.iter().map(|a| a.proposer_points[d]).collect(),
                flags: announcements.iter().map(|a| a.flag_points[d]).collect(),
            })
            .collect();
        Ok(Registry { contract, threshold: Roster::majority(roster.n()), roster, depths })
    }

    pub fn max_depth(&self) -> u32 {
        self.depths.len() as u32 - 1
    }

    pub fn n(&self) -> usize {
        self.roster.n()
    }

    pub fn entry(&self, d: u32) -> &DepthEntry {
        &self.depths[d as usize]
    }

    /// The shared content table for depth `d`.
    pub fn table(&self, d: u32) -> &EpochTable {
        &self.entry(d).table
    }

    /// Every member's proposer point for depth `d` (index member).
    pub fn proposers(&self, d: u32) -> &[XOnlyPublicKey] {
        &self.entry(d).proposers
    }

    /// Every member's flag point for depth `d` (index member).
    pub fn flags(&self, d: u32) -> &[XOnlyPublicKey] {
        &self.entry(d).flags
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
        let (c, max_depth) = (17u32, 9u32);
        let tables: Vec<EpochTable> = (0..=max_depth).map(|d| content.epoch_table(key_index(c, d), HEADER_CHUNKS)).collect();
        let anns: Vec<MemberPublic> = ms.iter().map(|m| m.announce(c, &tables, max_depth)).collect();
        let reg = Registry::build(c, roster.clone(), &tables, &anns, max_depth).unwrap();
        assert_eq!(reg.threshold, 3);
        assert_eq!(reg.max_depth(), 9);
        assert_eq!(reg.contract, c);
        for d in 0..=max_depth {
            assert_eq!(reg.table(d), &tables[d as usize]);
            assert_eq!(reg.proposers(d).len(), 5);
            assert_eq!(reg.proposers(d)[3], ms[3].proposer.flag_point(key_index(c, d)));
            assert_eq!(reg.flags(d)[3], ms[3].flags.flag_point(key_index(c, d)));
            assert_ne!(reg.proposers(d)[3], reg.flags(d)[3]);
        }
        // announced for another contract
        let other: Vec<MemberPublic> = ms.iter().map(|m| m.announce(c + 1, &tables, max_depth)).collect();
        assert!(Registry::build(c, roster.clone(), &tables, &other, max_depth).is_err());
        // another contract's tables
        let tables_other: Vec<EpochTable> = (0..=max_depth).map(|d| content.epoch_table(key_index(c + 1, d), HEADER_CHUNKS)).collect();
        assert!(Registry::build(c, roster.clone(), &tables_other, &anns, max_depth).is_err());
        // an announcement under the wrong key
        let mut bad = anns.clone();
        bad.swap(0, 1);
        assert!(Registry::build(c, roster.clone(), &tables, &bad, max_depth).is_err());
        // a tampered announcement (one point replaced) fails its signature
        let mut bad = anns.clone();
        bad[2].proposer_points[4] = anns[3].proposer_points[4];
        assert!(Registry::build(c, roster.clone(), &tables, &bad, max_depth).is_err());
        // a member that co-signed a DIFFERENT content table for depth 4
        let mut other = tables.clone();
        other[4] = Attester::new([0x98; 32]).epoch_table(key_index(c, 4), HEADER_CHUNKS);
        let mut bad = anns.clone();
        bad[1] = ms[1].announce(c, &other, max_depth);
        assert!(Registry::build(c, roster.clone(), &tables, &bad, max_depth).is_err());
        // too few depths announced
        let mut bad = anns.clone();
        bad[4] = ms[4].announce(c, &tables, 3);
        assert!(Registry::build(c, roster, &tables, &bad, max_depth).is_err());
    }
}
