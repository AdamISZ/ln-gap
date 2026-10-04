//! The PoS venue: EC-OTS attestations of entries, keyed by (contract,
//! depth), with per-member proposer and flag bits (D32, D51, D53, D55).
//!
//! Since D55 the venue is NOT a chain and has no slots. A contract `c`
//! registers with the venue for depths `0..=M`; for every `(c, d)` the
//! venue publishes one shared content table (the D53 shared key, the table
//! index packing `(c, d)`, [`key_index`]) and every member's proposer and
//! flag point. Sealing is attesting the entry for `(c, d)` under its own
//! table, whenever the mover submits it; the attested object is the
//! fact chain's 96-byte header (`prev(20) root(20) head(48) height(4)
//! pad(4)`) with `height = d` and `prev` all zeros, so two members sealing
//! the same entry produce byte-identical headers and attestations. A
//! dispute reads out the head chunks only.
//!
//! TIME is not the venue's sequence but the members' flags (D50): member
//! `i` reveals its flag scalar for `(c, d)` if at the contract's deadline
//! `T_d` it held no attested, mover-signed entry for `(c, d)`. Deadlines
//! are the contract's (instance.rs); the members judge them on their
//! clocks. Members seal only entries the mover signed (the contract's
//! [`Authorship`] check, registered with the venue); a rogue member's
//! unsigned seal is provable misbehaviour, and inert in the contract.
//!
//! [`PosMiner`] holds the shared content key and the members' secrets;
//! [`PosClient`] holds one contract's attested heads and classifies what
//! it observes: new, known (the same head again, by any member), or an
//! equivocation (a DIFFERENT head at a held depth, naming the second
//! block's proposer).

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use bitcoin::hashes::{sha256, Hash};
use bitcoin::secp256k1::SecretKey;
use lngap_ec_wots::{Attestation, Attester, EpochTable};
use lngap_factchain::{entry_head, entry_root, Header, HEADER_BYTES, HEAD_BYTES};
use lngap_n4bit::DIGEST_BYTES;

pub mod blackjack;
pub mod bond;
pub mod chess;
pub mod ext;
pub mod fee;
pub mod graph;
pub mod rebut;
pub mod instance;
pub mod roster;
pub mod ttt;


pub use roster::{Member, MemberPublic, Registry, Roster};

/// Attested chunks per header: one per nibble (96 bytes = 192 chunks).
pub const HEADER_CHUNKS: usize = HEADER_BYTES * 2;

/// The venue's key index for depth `d` of contract `c` (D55): the content
/// table's epoch index and every member's proposer and flag key index.
/// Contract ids must be unique on a venue (two contracts sharing an id
/// would share tables).
pub fn key_index(contract: u32, d: u32) -> u64 {
    (u64::from(contract) << 32) | u64::from(d)
}

/// The designated sealer's position in the rotation for `(c, d)`:
/// `(h(c) + d) mod n` (D55), `h` a hash of the contract id so contracts
/// spread their load.
pub fn rotation(contract: u32, d: u32, n: usize) -> usize {
    let h = sha256::Hash::hash(&contract.to_be_bytes()).to_byte_array();
    (u32::from_be_bytes([h[0], h[1], h[2], h[3]]) as usize + d as usize) % n
}

/// The header a venue attests for an entry at depth `d`: `prev` zero (no
/// chain), the entry's root and head, `height = d`.
pub fn entry_header(d: u32, entry: &[u8]) -> Header {
    Header::new(&[0u8; DIGEST_BYTES], &entry_root(entry), &entry_head(entry), d)
}

/// A contract's authorship check, registered with the venue (D55): does
/// `entry` carry the mover's valid signature for depth `d`? Honest members
/// seal nothing else.
pub type Authorship = Arc<dyn Fn(u32, &[u8]) -> bool + Send + Sync>;

/// An entry sealed by the venue: the attestation over its header under the
/// `(contract, depth)` table, with its proposer's name tag: the member
/// index and the revealed proposer scalar for `(contract, depth)` (D53).
#[derive(Clone, Debug)]
pub struct SealedBlock {
    pub contract: u32,
    pub header: Header,
    /// The entry this seal attests.
    pub entry: Vec<u8>,
    /// One revealed scalar per header chunk, under the `(c, d)` table.
    pub attestation: Attestation,
    /// Which member sealed it, and its revealed proposer scalar for
    /// `(c, d)` (`p_{i,(c,d)}`: a private key for the registry's point).
    pub proposer: usize,
    pub proposer_secret: SecretKey,
}

impl SealedBlock {
    /// The depth the seal is for.
    pub fn depth(&self) -> u32 {
        self.header.height()
    }

    /// The attested head.
    pub fn head(&self) -> [u8; HEAD_BYTES] {
        self.header.head()
    }

    /// The proposer reveal opens the named member's point for the depth,
    /// under the contract's registry.
    pub fn verify_proposer(&self, registry: &Registry) -> Result<(), String> {
        let d = self.depth();
        if registry.contract != self.contract {
            return Err(format!("the seal is for contract {} but the registry is contract {}'s", self.contract, registry.contract));
        }
        if d > registry.max_depth() {
            return Err(format!("depth {d} is beyond the registry (0..={})", registry.max_depth()));
        }
        let points = registry.proposers(d);
        if self.proposer >= points.len() {
            return Err(format!("depth {d}: proposer index {} is not a member", self.proposer));
        }
        let pt = bitcoin::key::Keypair::from_secret_key(bitcoin::secp256k1::SECP256K1, &self.proposer_secret).x_only_public_key().0;
        if pt != points[self.proposer] {
            return Err(format!("depth {d}: the proposer reveal does not open member {}'s point", self.proposer));
        }
        Ok(())
    }

    /// The content checks: head = entry's head, root = entry's root, prev
    /// zero.
    pub fn verify_content(&self) -> Result<(), String> {
        let d = self.depth();
        if self.header.head() != entry_head(&self.entry) {
            return Err(format!("head mismatch at depth {d}"));
        }
        let computed_root = entry_root(&self.entry);
        if computed_root != self.header.root() {
            return Err(format!(
                "root mismatch at depth {d}: header says {} but hash(entry) = {}",
                hex::encode(self.header.root()),
                hex::encode(computed_root)
            ));
        }
        if self.header.prev() != [0u8; DIGEST_BYTES] {
            return Err(format!("depth {d}: a venue seal has no prev link"));
        }
        Ok(())
    }

    /// The seal: the attestation opens every chunk of the header under the
    /// `(contract, depth)` table.
    pub fn verify_seal(&self, table: &EpochTable) -> Result<(), String> {
        let d = self.depth();
        if table.index != key_index(self.contract, d) {
            return Err(format!("table index {:#x} is not contract {} depth {d}'s", table.index, self.contract));
        }
        if table.chunks != HEADER_CHUNKS {
            return Err(format!("table has {} chunks, the header has {HEADER_CHUNKS}", table.chunks));
        }
        if !self.attestation.verify(table, self.header.as_bytes()) {
            return Err(format!("attestation does not open the header at depth {d}"));
        }
        Ok(())
    }

    /// Everything a client checks: content, proposer, seal under the
    /// registry's table.
    pub fn verify(&self, registry: &Registry) -> Result<(), String> {
        self.verify_content()?;
        self.verify_proposer(registry)?;
        self.verify_seal(registry.table(self.depth()))
    }
}

/// A contract the venue serves: its depth range and authorship check.
struct Registration {
    max_depth: u32,
    authorship: Authorship,
}

/// The venue: the shared content key and the members, registering
/// contracts, sealing submitted entries and flagging. Any member may seal
/// any `(c, d)` (D53); the designated one is [`PosMiner::default_sealer`]
/// (the rotation, skipping silent members). Members seal only entries the
/// contract's authorship check accepts ([`PosMiner::seal_entry`]);
/// [`PosMiner::seal_unchecked`] is a rogue member's seal, for fixtures.
pub struct PosMiner {
    content: Attester,
    members: Vec<Member>,
    roster: Roster,
    silent: HashSet<usize>,
    /// The content table per key index, computed once (a table is ~100 ms
    /// of curve arithmetic; announcing and sealing share it).
    tables: HashMap<u64, EpochTable>,
    contracts: HashMap<u32, Registration>,
    /// What the venue has attested, per `(c, d)`: the heads, in order.
    attested: HashMap<(u32, u32), Vec<[u8; HEAD_BYTES]>>,
}

impl PosMiner {
    /// The venue: its content key from `content_seed` (shared by the
    /// members) and its `members`.
    pub fn new(content_seed: [u8; 32], members: Vec<Member>) -> PosMiner {
        let roster = Roster::new(members.iter().map(Member::public).collect());
        PosMiner { content: Attester::new(content_seed), members, roster, silent: HashSet::new(), tables: HashMap::new(), contracts: HashMap::new(), attested: HashMap::new() }
    }

    /// A one-member venue from a seed (the content key and the member both
    /// from it).
    pub fn single(seed: [u8; 32]) -> PosMiner {
        PosMiner::new(seed, vec![Member::new(seed)])
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

    /// The designated sealer for `(c, d)`: the rotation's member if it is
    /// live, else the next live one in rotation order; `None` if all are
    /// silent. The mover submits to it and falls back along the rotation.
    pub fn default_sealer(&self, contract: u32, d: u32) -> Option<usize> {
        let n = self.n();
        let first = rotation(contract, d, n);
        (0..n).map(|k| (first + k) % n).find(|i| !self.silent.contains(i))
    }

    /// The content table for `(c, d)`, computed once.
    pub fn table(&mut self, contract: u32, d: u32) -> &EpochTable {
        let content = &self.content;
        self.tables.entry(key_index(contract, d)).or_insert_with(|| content.epoch_table(key_index(contract, d), HEADER_CHUNKS))
    }

    /// Register contract `c` for depths `0..=max_depth` with its authorship
    /// check. Contract ids are unique on the venue.
    pub fn register(&mut self, contract: u32, max_depth: u32, authorship: Authorship) -> Result<(), String> {
        if self.contracts.contains_key(&contract) {
            return Err(format!("contract {contract} is already registered"));
        }
        self.contracts.insert(contract, Registration { max_depth, authorship });
        Ok(())
    }

    /// The content tables for contract `c`'s depths `0..=max_depth` and
    /// every member's signed announcement over them.
    pub fn announce(&mut self, contract: u32, max_depth: u32) -> (Vec<EpochTable>, Vec<MemberPublic>) {
        let tables: Vec<EpochTable> = (0..=max_depth).map(|d| self.table(contract, d).clone()).collect();
        let anns = self.members.iter().map(|m| m.announce(contract, &tables, max_depth)).collect();
        (tables, anns)
    }

    /// The registry for contract `c`, depths `0..=max_depth`, as a client
    /// or contract builds it from the announcements.
    pub fn registry(&mut self, contract: u32, max_depth: u32) -> anyhow::Result<Registry> {
        let (tables, anns) = self.announce(contract, max_depth);
        Registry::build(contract, self.roster.clone(), &tables, &anns, max_depth)
    }

    /// Member `i`'s proposer scalar for `(c, d)` (what its seal reveals;
    /// fixtures that build seals by hand need it).
    pub fn proposer_secret(&self, i: usize, contract: u32, d: u32) -> SecretKey {
        self.members[i].proposer.flag_secret(key_index(contract, d))
    }

    /// The flags for `(c, d)` (D50, D55): every non-silent member's flag
    /// scalar (index member), `None` for a silent one. The caller (the
    /// venue's clock) calls it once the deadline has passed with no
    /// mover-signed attested entry ([`PosMiner::holds_signed`]).
    pub fn flag(&self, contract: u32, d: u32) -> Vec<Option<SecretKey>> {
        (0..self.members.len()).map(|i| (!self.silent.contains(&i)).then(|| self.members[i].flags.flag_secret(key_index(contract, d)))).collect()
    }

    /// Whether the venue has attested a mover-signed entry for `(c, d)`
    /// (what a member checks at the deadline before flagging).
    pub fn holds_signed(&self, contract: u32, d: u32, entry_of: impl Fn(&[u8; HEAD_BYTES]) -> Option<Vec<u8>>) -> bool {
        let Some(reg) = self.contracts.get(&contract) else { return false };
        self.attested.get(&(contract, d)).map(|hs| hs.iter().any(|h| entry_of(h).is_some_and(|e| (reg.authorship)(d, &e)))).unwrap_or(false)
    }

    /// The heads the venue attested for `(c, d)`, in order.
    pub fn attested(&self, contract: u32, d: u32) -> &[[u8; HEAD_BYTES]] {
        self.attested.get(&(contract, d)).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Member `i` seals `entry` for `(c, d)` — an honest member's seal:
    /// the contract must be registered, the depth in range, the member
    /// live, and the entry must carry the mover's signature.
    pub fn seal_entry(&mut self, contract: u32, d: u32, i: usize, entry: &[u8]) -> Result<SealedBlock, String> {
        let reg = self.contracts.get(&contract).ok_or_else(|| format!("contract {contract} is not registered"))?;
        if d == 0 || d > reg.max_depth {
            return Err(format!("contract {contract} has depths 1..={}, not {d}", reg.max_depth));
        }
        if !(reg.authorship)(d, entry) {
            return Err(format!("contract {contract} depth {d}: the entry does not carry the mover's signature; an honest member refuses it"));
        }
        self.seal_unchecked(contract, d, i, entry)
    }

    /// Member `i` seals `entry` for `(c, d)` without the authorship check
    /// (a rogue member's seal; provable misbehaviour, inert in the
    /// contract). The member must still be live.
    pub fn seal_unchecked(&mut self, contract: u32, d: u32, i: usize, entry: &[u8]) -> Result<SealedBlock, String> {
        if i >= self.members.len() {
            return Err(format!("no member {i}"));
        }
        if self.silent.contains(&i) {
            return Err(format!("contract {contract} depth {d}: member {i} is silent"));
        }
        let header = entry_header(d, entry);
        let table = self.table(contract, d).clone();
        let attestation = self.content.attest(&table, header.as_bytes());
        let heads = self.attested.entry((contract, d)).or_default();
        if !heads.contains(&header.head()) {
            heads.push(header.head());
        }
        Ok(SealedBlock { contract, header, entry: entry.to_vec(), attestation, proposer: i, proposer_secret: self.proposer_secret(i, contract, d) })
    }
}

/// What an observed seal turned out to be.
#[derive(Debug, PartialEq, Eq)]
pub enum Observation {
    /// The first attested head at its depth.
    New,
    /// The same head again (any member; same header, same attestation).
    Known,
    /// A DIFFERENT attested head at a held depth (D55: equivocation is two
    /// heads, not two headers). Whose fault depends on the heads: both
    /// mover-signed is the mover's (the contract's `equiv` leaf); an
    /// unsigned one is its sealer's (provable). Names the second seal's
    /// proposer.
    Equivocation(Equivocation),
}

/// Two different attested heads at one `(contract, depth)`, and the member
/// whose proposer reveal the SECOND carries.
#[derive(Debug, PartialEq, Eq)]
pub struct Equivocation {
    pub depth: u32,
    pub member: usize,
    /// The header the client already held.
    pub first: Header,
    /// The newly observed conflicting header.
    pub second: Header,
}

/// A client of one contract's attestations: verifies seals against the
/// contract's registry and holds the attested heads by depth.
#[derive(Clone, Debug)]
pub struct PosClient {
    pub contract: u32,
    headers: BTreeMap<u32, Header>,
}

impl PosClient {
    pub fn new(contract: u32) -> Self {
        PosClient { contract, headers: BTreeMap::new() }
    }

    /// The attested header held at depth `d`.
    pub fn header_at(&self, d: u32) -> Option<&Header> {
        self.headers.get(&d)
    }

    /// The deepest depth held.
    pub fn deepest(&self) -> u32 {
        self.headers.keys().next_back().copied().unwrap_or(0)
    }

    /// Verify a seal and classify it; a new head is recorded, an
    /// equivocation is not (the first head stays held).
    pub fn observe(&mut self, block: &SealedBlock, registry: &Registry) -> Result<Observation, String> {
        if block.contract != self.contract {
            return Err(format!("a seal for contract {} observed by contract {}'s client", block.contract, self.contract));
        }
        block.verify(registry)?;
        let d = block.depth();
        match self.headers.get(&d) {
            None => {
                self.headers.insert(d, block.header.clone());
                Ok(Observation::New)
            }
            Some(held) if held.head() == block.header.head() => Ok(Observation::Known),
            Some(held) => Ok(Observation::Equivocation(Equivocation { depth: d, member: block.proposer, first: held.clone(), second: block.header.clone() })),
        }
    }

    /// Verify and record a seal that must not conflict with what is held.
    pub fn verify_and_append(&mut self, block: &SealedBlock, registry: &Registry) -> Result<(), String> {
        match self.observe(block, registry)? {
            Observation::New | Observation::Known => Ok(()),
            Observation::Equivocation(e) => Err(format!("depth {}: a second, different head (sealed by member {})", e.depth, e.member)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SEED: [u8; 32] = [7u8; 32];
    const C: u32 = 42;
    const MAX_DEPTH: u32 = 9;

    /// Entries in these tests are "signed" iff they start with b"ok".
    fn authorship() -> Authorship {
        Arc::new(|_d: u32, e: &[u8]| e.starts_with(b"ok"))
    }

    /// A 3-member venue with contract C registered, a client, the registry.
    fn boot() -> (PosMiner, PosClient, Registry) {
        let members: Vec<Member> = (0..3u8).map(|i| Member::new([SEED[0] + i; 32])).collect();
        let mut miner = PosMiner::new(SEED, members);
        miner.register(C, MAX_DEPTH, authorship()).unwrap();
        let registry = miner.registry(C, MAX_DEPTH).unwrap();
        (miner, PosClient::new(C), registry)
    }

    #[test]
    fn key_index_separates_contracts() {
        assert_ne!(key_index(1, 2), key_index(2, 1));
        assert_eq!(key_index(1, 2) >> 32, 1);
        let (mut miner, _c, _r) = boot();
        let a = miner.table(1, 3).clone();
        let b = miner.table(2, 3).clone();
        assert_ne!(a.digest(), b.digest(), "two contracts' depth-3 tables differ");
    }

    /// Any member seals any depth; the same entry sealed by two members is
    /// the same header and attestation (Known); the proposer reveal must
    /// open the named member's point.
    #[test]
    fn seal_on_submission_and_same_head_collisions() {
        let (mut miner, mut client, reg) = boot();
        let b1 = miner.seal_entry(C, 3, 2, b"ok move 3").unwrap();
        assert_eq!(b1.depth(), 3);
        assert_eq!(client.observe(&b1, &reg).unwrap(), Observation::New);
        let b1_other = miner.seal_entry(C, 3, 0, b"ok move 3").unwrap();
        assert_eq!(b1_other.header, b1.header);
        assert_eq!(b1_other.attestation.scalar_sum(0..HEADER_CHUNKS), b1.attestation.scalar_sum(0..HEADER_CHUNKS), "the shared key's attestation is deterministic");
        assert_eq!(client.observe(&b1_other, &reg).unwrap(), Observation::Known);
        // a forged proposer tag
        let mut forged = b1.clone();
        forged.proposer = 1;
        assert!(client.observe(&forged, &reg).unwrap_err().contains("does not open member 1"));
        forged.proposer = 7;
        assert!(client.observe(&forged, &reg).unwrap_err().contains("not a member"));
        // the wrong contract's registry
        let other = miner.registry(C + 1, MAX_DEPTH).unwrap();
        assert!(b1.verify(&other).is_err());
    }

    #[test]
    fn honest_members_seal_only_signed_entries() {
        let (mut miner, _client, _reg) = boot();
        assert!(miner.seal_entry(C, 2, 0, b"junk").unwrap_err().contains("refuses"));
        assert!(miner.seal_entry(C + 1, 2, 0, b"ok").unwrap_err().contains("not registered"));
        assert!(miner.seal_entry(C, MAX_DEPTH + 1, 0, b"ok").is_err());
        assert!(miner.seal_entry(C, 0, 0, b"ok").is_err());
        // a rogue member seals it anyway: attested, but not "signed"
        let rogue = miner.seal_unchecked(C, 2, 1, b"junk").unwrap();
        assert_eq!(miner.attested(C, 2), &[rogue.head()]);
        let entries: HashMap<[u8; HEAD_BYTES], Vec<u8>> = HashMap::from([(rogue.head(), rogue.entry.clone())]);
        assert!(!miner.holds_signed(C, 2, |h| entries.get(h).cloned()), "junk does not suppress the flags");
        let good = miner.seal_entry(C, 2, 0, b"ok real").unwrap();
        let entries: HashMap<[u8; HEAD_BYTES], Vec<u8>> = HashMap::from([(rogue.head(), rogue.entry.clone()), (good.head(), good.entry.clone())]);
        assert!(miner.holds_signed(C, 2, |h| entries.get(h).cloned()));
        assert!(miner.register(C, 3, authorship()).is_err(), "contract ids are unique");
    }

    #[test]
    fn rotation_designates_and_skips_silent() {
        let (mut miner, _client, _reg) = boot();
        let p = miner.default_sealer(C, 4).unwrap();
        assert_eq!(p, rotation(C, 4, 3));
        assert_eq!(miner.default_sealer(C, 5).unwrap(), (p + 1) % 3);
        miner.silence(p);
        assert_eq!(miner.default_sealer(C, 4), Some((p + 1) % 3));
        assert!(miner.seal_entry(C, 4, p, b"ok").unwrap_err().contains("silent"));
        let flags = miner.flag(C, 4);
        assert!(flags[p].is_none() && flags[(p + 1) % 3].is_some());
        miner.silence((p + 1) % 3);
        miner.silence((p + 2) % 3);
        assert_eq!(miner.default_sealer(C, 4), None);
    }

    #[test]
    fn different_heads_are_an_equivocation() {
        let (mut miner, mut client, reg) = boot();
        let a = miner.seal_entry(C, 1, 0, b"ok move A").unwrap();
        client.verify_and_append(&a, &reg).unwrap();
        let b = miner.seal_entry(C, 1, 2, b"ok move B").unwrap();
        match client.observe(&b, &reg) {
            Ok(Observation::Equivocation(e)) => {
                assert_eq!(e.depth, 1);
                assert_eq!(e.member, 2);
                assert_eq!(e.first, a.header);
                assert_eq!(e.second, b.header);
            }
            other => panic!("expected equivocation, got {other:?}"),
        }
        assert_eq!(client.header_at(1), Some(&a.header), "the first head stays held");
        assert!(client.verify_and_append(&b, &reg).is_err());
    }

    #[test]
    fn seal_rejects_tampering() {
        let (mut miner, _client, reg) = boot();
        let mut block = miner.seal_entry(C, 1, 0, b"ok x").unwrap();
        block.header.0[95] ^= 1; // pad: only the seal reads it
        block.verify_content().unwrap();
        assert!(block.verify(&reg).is_err());
        let mut block = miner.seal_entry(C, 1, 0, b"ok x").unwrap();
        block.entry[3] ^= 1;
        assert!(block.verify_content().is_err());
        let block = miner.seal_entry(C, 1, 0, b"ok x").unwrap();
        let wrong = miner.table(C, 2).clone();
        assert!(block.verify_seal(&wrong).is_err());
    }
}
