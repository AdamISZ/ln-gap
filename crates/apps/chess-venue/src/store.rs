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
    pub fn block(slot: u32) -> String {
        format!("venue/blocks/{slot:04}.json")
    }
    pub fn flags(slot: u32) -> String {
        format!("venue/flags/{slot:04}.json")
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

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct VenueParams {
    /// The Bitcoin height the slot count starts from: slot `s` seals at
    /// `b0 + s`; set once the contract is funded.
    pub b0: u32,
    pub max_slot: u32,
    pub block_secs: u64,
    pub n: usize,
    pub threshold: u32,
    pub max_depth: u32,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct BlockJson {
    pub slot: u32,
    pub header: String,
    pub entry: String,
    pub secrets: Vec<String>,
    pub proposer: usize,
    pub proposer_secret: String,
}

impl BlockJson {
    pub fn from_block(b: &SealedBlock) -> BlockJson {
        BlockJson {
            slot: b.header.height(),
            header: hex::encode(b.header.as_bytes()),
            entry: hex::encode(&b.entry),
            secrets: b.attestation.secrets.iter().map(|s| hex::encode(s.secret_bytes())).collect(),
            proposer: b.proposer,
            proposer_secret: hex::encode(b.proposer_secret.secret_bytes()),
        }
    }

    pub fn to_block(&self) -> Result<SealedBlock> {
        let hb: [u8; 96] = hex::decode(&self.header)?.try_into().map_err(|_| anyhow!("header is 96 bytes"))?;
        let secrets = self.secrets.iter().map(|s| Ok(SecretKey::from_slice(&hex::decode(s)?)?)).collect::<Result<Vec<_>>>()?;
        Ok(SealedBlock {
            header: Header(hb),
            entry: hex::decode(&self.entry)?,
            attestation: Attestation { secrets },
            proposer: self.proposer,
            proposer_secret: SecretKey::from_slice(&hex::decode(&self.proposer_secret)?)?,
        })
    }
}

/// The members' flag scalars for a slot (index member; `None` = silent).
pub type FlagsJson = Vec<Option<String>>;

pub fn flags_to_json(f: &[Option<SecretKey>]) -> FlagsJson {
    f.iter().map(|s| s.as_ref().map(|k| hex::encode(k.secret_bytes()))).collect()
}

pub fn flags_from_json(f: &FlagsJson) -> Result<Vec<Option<SecretKey>>> {
    f.iter().map(|s| s.as_ref().map(|h| Ok(SecretKey::from_slice(&hex::decode(h)?)?)).transpose()).collect()
}

/// A submitted entry, queued for the next slot.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct InboxEntry {
    pub from: String,
    pub entry: String,
}

/// A player's public offer: its channel keys and its per-depth contract
/// keys.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Offer {
    pub pubs: PartyPubKeys,
    pub keys: Vec<(u32, PosKeyOffer)>,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ContractJson {
    pub spk: String,
    pub value: u64,
    pub deadline: u32,
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
