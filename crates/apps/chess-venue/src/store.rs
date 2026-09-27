//! The shared directory: what the venue publishes and what the players
//! exchange. Everything is a JSON file; a reader polls.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Context, Result};
use bitcoin::secp256k1::SecretKey;
use lngap_channel::{PartyPubKeys, Role};
use lngap_ec_wots::Attestation;
use lngap_factchain::Header;
use lngap_pos::instance::PosKeyOffer;
use lngap_pos::SealedBlock;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

/// The venue's roster: five members, majority three (D50 amended, D53).
pub const K: usize = 5;
pub const GAME_ID: u16 = 1;
pub const CONTRACT_ID: u32 = 1;
/// The pot (both stakes) and the pre-sign fee per hop (the chess pair
/// readout is ~37 kvB; the fee must clear the relay floor).
pub const POT_SAT: u64 = 1_000_000;
pub const FEE_SAT: u64 = 60_000;
/// The venue's content seed and the members' base seed (member `i` is
/// seeded `SEED[0] + i`): the venue's secrets, known to the venue process.
pub const VENUE_SEED: [u8; 32] = [0x77; 32];

pub struct Store {
    pub dir: PathBuf,
}

impl Store {
    pub fn new(dir: PathBuf) -> Store {
        Store { dir }
    }

    fn path(&self, rel: &str) -> PathBuf {
        self.dir.join(rel)
    }

    pub fn read<T: DeserializeOwned>(&self, rel: &str) -> Result<Option<T>> {
        let p = self.path(rel);
        if !p.exists() {
            return Ok(None);
        }
        let s = std::fs::read_to_string(&p).with_context(|| format!("reading {}", p.display()))?;
        // a writer may be mid-write; treat a parse failure as "not yet"
        Ok(serde_json::from_str(&s).ok())
    }

    pub fn write<T: Serialize>(&self, rel: &str, v: &T) -> Result<()> {
        let p = self.path(rel);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let tmp = p.with_extension("tmp");
        std::fs::write(&tmp, serde_json::to_vec_pretty(v)?)?;
        std::fs::rename(&tmp, &p).with_context(|| format!("writing {}", p.display()))?;
        Ok(())
    }

    pub fn exists(&self, rel: &str) -> bool {
        self.path(rel).exists()
    }

    pub fn list(&self, rel_dir: &str) -> Result<Vec<PathBuf>> {
        let d = self.path(rel_dir);
        if !d.exists() {
            return Ok(vec![]);
        }
        let mut v: Vec<PathBuf> = std::fs::read_dir(&d)?.filter_map(|e| e.ok().map(|e| e.path())).filter(|p| p.extension().is_some_and(|x| x == "json")).collect();
        v.sort();
        Ok(v)
    }

    pub fn remove(&self, p: &Path) {
        let _ = std::fs::remove_file(p);
    }

    // ----- paths -----
    pub fn node() -> &'static str {
        "node.json"
    }
    pub fn params() -> &'static str {
        "venue/params.json"
    }
    pub fn registry() -> &'static str {
        "venue/registry.json"
    }
    /// Member `member`'s seal of depth `d` (D55: keyed by depth, sealed on
    /// submission; two members may seal the same entry).
    pub fn seal(d: u32, member: usize) -> String {
        format!("venue/seals/{d:04}-{member}.json")
    }
    pub fn seals_dir() -> &'static str {
        "venue/seals"
    }
    pub fn flags(d: u32) -> String {
        format!("venue/flags/{d:04}.json")
    }
    /// Submissions an honest member would not seal, held for the venue
    /// page's misbehaviour controls: after the due time (`late`), or not
    /// signed by the mover (`refused`).
    pub fn late_dir() -> &'static str {
        "venue/late"
    }
    pub fn refused_dir() -> &'static str {
        "venue/refused"
    }
    pub fn web(r: Role) -> String {
        format!("players/{}/web.json", r.name())
    }
    pub fn inbox_dir() -> &'static str {
        "venue/inbox"
    }
    pub fn offer(r: Role) -> String {
        format!("players/{}/offer.json", r.name())
    }
    pub fn sigs(r: Role) -> String {
        format!("players/{}/sigs.json", r.name())
    }
    pub fn contract() -> &'static str {
        "players/contract.json"
    }
    pub fn ready(r: Role) -> String {
        format!("players/{}/ready.json", r.name())
    }
    pub fn funded() -> &'static str {
        "players/funded.json"
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct NodeInfo {
    pub datadir: String,
}

/// The venue's parameters (D55): the clock and the members' rules; the
/// game's own timetable (t0) is fixed by the contract.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct VenueParams {
    /// Seconds between Bitcoin blocks (independent of the venue).
    pub block_secs: u64,
    pub n: usize,
    pub threshold: u32,
    pub max_depth: u32,
    /// Seconds per move (`ell`).
    pub ell: u32,
    /// The mover's fallback: resubmit to the next member after this many
    /// seconds without a seal.
    pub backoff: u32,
    /// The claim margin `m` past a move's due time (median-time-past).
    pub margin: u32,
    /// Seconds from the contract proposal to move 0's time `t0` (setup:
    /// the graph is built and signed in between).
    pub start_secs: u32,
}

/// A seal, as the venue publishes it: the attestation, the proposer
/// reveal, when it was made, and whether an honest member would have made
/// it (`late`: after the due time; `rogue`: an entry the mover did not
/// sign) — the last two only by the venue page's misbehaviour controls.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct BlockJson {
    pub depth: u32,
    pub header: String,
    pub entry: String,
    pub secrets: Vec<String>,
    pub proposer: usize,
    pub proposer_secret: String,
    pub sealed_at: u32,
    #[serde(default)]
    pub late: bool,
    #[serde(default)]
    pub rogue: bool,
}

impl BlockJson {
    pub fn from_block(b: &SealedBlock, sealed_at: u32, late: bool, rogue: bool) -> BlockJson {
        BlockJson {
            depth: b.header.height(),
            header: hex::encode(b.header.as_bytes()),
            entry: hex::encode(&b.entry),
            secrets: b.attestation.secrets.iter().map(|s| hex::encode(s.secret_bytes())).collect(),
            proposer: b.proposer,
            proposer_secret: hex::encode(b.proposer_secret.secret_bytes()),
            sealed_at,
            late,
            rogue,
        }
    }

    pub fn to_block(&self) -> Result<SealedBlock> {
        let hb: [u8; 96] = hex::decode(&self.header)?.try_into().map_err(|_| anyhow!("header is 96 bytes"))?;
        let secrets = self.secrets.iter().map(|s| Ok(SecretKey::from_slice(&hex::decode(s)?)?)).collect::<Result<Vec<_>>>()?;
        Ok(SealedBlock {
            contract: CONTRACT_ID,
            header: Header(hb),
            entry: hex::decode(&self.entry)?,
            attestation: Attestation { secrets },
            proposer: self.proposer,
            proposer_secret: SecretKey::from_slice(&hex::decode(&self.proposer_secret)?)?,
        })
    }
}

/// The members' flag scalars for a depth (index member; `None` = silent).
pub type FlagsJson = Vec<Option<String>>;

pub fn flags_to_json(f: &[Option<SecretKey>]) -> FlagsJson {
    f.iter().map(|s| s.as_ref().map(|k| hex::encode(k.secret_bytes()))).collect()
}

pub fn flags_from_json(f: &FlagsJson) -> Result<Vec<Option<SecretKey>>> {
    f.iter().map(|s| s.as_ref().map(|h| Ok(SecretKey::from_slice(&hex::decode(h)?)?)).transpose()).collect()
}

/// A submitted entry for depth `depth`, addressed to member `to` (the
/// designated sealer, or the mover's fallback), at unix time `at`.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct InboxEntry {
    pub from: String,
    pub depth: u32,
    pub to: usize,
    pub entry: String,
    pub at: u32,
}

/// Now, in unix seconds.
pub fn unix_now() -> u32 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() as u32).unwrap_or(0)
}

/// A player's public offer: its channel keys and its per-depth contract
/// keys.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Offer {
    pub pubs: PartyPubKeys,
    pub keys: Vec<(u32, PosKeyOffer)>,
}

/// The contract the user proposes: its output, and its timetable (D55:
/// move `d` is due at `t0 + d·ell`; claims from the due time plus
/// `margin`; `settle` from `deadline`, all unix times).
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ContractJson {
    pub spk: String,
    pub value: u64,
    pub deadline: u32,
    pub t0: u32,
    pub ell: u32,
    pub margin: u32,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct FundedJson {
    pub txid: String,
    pub vout: u32,
    pub value: u64,
    pub spk: String,
    pub height: u32,
}

/// A player's signatures on every pre-signed transaction, by label.
pub type SigsJson = BTreeMap<String, String>;
