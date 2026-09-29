//! The shared directory: what the venue publishes and what the two parties
//! exchange. Everything is a JSON file; a reader polls.
//!
//! - `node.json`, `venue/params.json`: the node and the venue's rules;
//! - `channel/`: the channel's opening (each party's offer: channel keys,
//!   first revocation hashes, funding contribution; the funding witnesses;
//!   `funded.json`) and its message bus (`channel/bus/<to>/`, one file per
//!   wire envelope);
//! - `hands/<h>/`: hand `h` (contract id `h`): the player's request, the
//!   venue's registry for it, each party's offer (per-hand keys and share
//!   commitments), the contract terms, the venue's registration, and the
//!   venue's seals, flags and held submissions for the hand.

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

/// The venue's roster: five members, majority three.
pub const K: usize = 5;
pub const GAME_ID: u16 = 1;
/// Each side's stake per hand (the pot is both), and each side's share of
/// the channel.
pub const STAKE_SAT: u64 = 500_000;
pub const CHANNEL_SIDE_SAT: u64 = 3_000_000;
/// The pre-sign fee per hop (the pair readout is ~37 kvB).
pub const FEE_SAT: u64 = 60_000;
pub const VENUE_SEED: [u8; 32] = [0x66; 32];

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

    /// The hand ids with a directory, ascending.
    pub fn hands(&self) -> Vec<u32> {
        let d = self.path("hands");
        let mut v: Vec<u32> = std::fs::read_dir(&d).map(|r| r.filter_map(|e| e.ok()?.file_name().to_str()?.parse().ok()).collect()).unwrap_or_default();
        v.sort();
        v
    }

    // ----- paths -----
    pub fn node() -> &'static str {
        "node.json"
    }
    pub fn params() -> &'static str {
        "venue/params.json"
    }
    pub fn web(r: Role) -> String {
        format!("players/{}/web.json", r.name())
    }
    // the channel
    pub fn chan_offer(r: Role) -> String {
        format!("channel/offer-{}.json", r.name())
    }
    pub fn funding_wit(r: Role) -> String {
        format!("channel/funding-wit-{}.json", r.name())
    }
    pub fn funded() -> &'static str {
        "channel/funded.json"
    }
    pub fn bus(r: Role) -> String {
        format!("channel/bus/{}", r.name())
    }
    // a hand
    fn hand(h: u32, rel: &str) -> String {
        format!("hands/{h:04}/{rel}")
    }
    pub fn request(h: u32) -> String {
        Store::hand(h, "request.json")
    }
    pub fn registry(h: u32) -> String {
        Store::hand(h, "registry.json")
    }
    pub fn offer(h: u32, r: Role) -> String {
        Store::hand(h, &format!("offer-{}.json", r.name()))
    }
    pub fn contract(h: u32) -> String {
        Store::hand(h, "contract.json")
    }
    pub fn registered(h: u32) -> String {
        Store::hand(h, "registered.json")
    }
    pub fn seal(h: u32, d: u32, member: usize) -> String {
        Store::hand(h, &format!("venue/seals/{d:04}-{member}.json"))
    }
    pub fn seals_dir(h: u32) -> String {
        Store::hand(h, "venue/seals")
    }
    pub fn flags(h: u32, d: u32) -> String {
        Store::hand(h, &format!("venue/flags/{d:04}.json"))
    }
    pub fn late_dir(h: u32) -> String {
        Store::hand(h, "venue/late")
    }
    pub fn refused_dir(h: u32) -> String {
        Store::hand(h, "venue/refused")
    }
    pub fn inbox_dir(h: u32) -> String {
        Store::hand(h, "venue/inbox")
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct NodeInfo {
    pub datadir: String,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct VenueParams {
    pub block_secs: u64,
    pub n: usize,
    pub threshold: u32,
    pub max_depth: u32,
    pub ell: u32,
    pub backoff: u32,
    pub margin: u32,
    pub start_secs: u32,
    #[serde(default)]
    pub deposit: u64,
    /// When the venue started (unix seconds): a party refuses files older
    /// than this (a stale directory).
    #[serde(default)]
    pub started: u32,
}

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

    pub fn to_block(&self, contract: u32) -> Result<SealedBlock> {
        let hb: [u8; 96] = hex::decode(&self.header)?.try_into().map_err(|_| anyhow!("header is 96 bytes"))?;
        let secrets = self.secrets.iter().map(|s| Ok(SecretKey::from_slice(&hex::decode(s)?)?)).collect::<Result<Vec<_>>>()?;
        Ok(SealedBlock {
            contract,
            header: Header(hb),
            entry: hex::decode(&self.entry)?,
            attestation: Attestation { secrets },
            proposer: self.proposer,
            proposer_secret: SecretKey::from_slice(&hex::decode(&self.proposer_secret)?)?,
        })
    }
}

pub type FlagsJson = Vec<Option<String>>;

pub fn flags_to_json(f: &[Option<SecretKey>]) -> FlagsJson {
    f.iter().map(|s| s.as_ref().map(|k| hex::encode(k.secret_bytes()))).collect()
}

pub fn flags_from_json(f: &FlagsJson) -> Result<Vec<Option<SecretKey>>> {
    f.iter().map(|s| s.as_ref().map(|h| Ok(SecretKey::from_slice(&hex::decode(h)?)?)).transpose()).collect()
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct InboxEntry {
    pub from: String,
    pub depth: u32,
    pub to: usize,
    pub entry: String,
    pub at: u32,
}

pub fn side(r: Role) -> &'static str {
    match r {
        Role::User => "Player",
        Role::Hub => "House",
    }
}

pub fn ui(s: &str) -> String {
    s.replace("UserWins", "PlayerWins").replace("HubWins", "HouseWins")
}

pub fn unix_now() -> u32 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() as u32).unwrap_or(0)
}

/// A party's channel offer: its channel keys, its revocation hashes for
/// states 0 and 1, and its funding contribution (a coin at its payout
/// script).
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ChanOffer {
    pub pubs: PartyPubKeys,
    pub rev: [String; 2],
    pub contrib_txid: String,
    pub contrib_vout: u32,
    pub contrib_value: u64,
    pub contrib_spk: String,
}

/// A party's offer for hand `h`: its per-hand contract keys and its sixteen
/// share commitments.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Offer {
    pub keys: Vec<(u32, PosKeyOffer)>,
    pub commits: Vec<String>,
}

pub fn commitments(user: &Offer, hub: &Offer) -> Result<lngap_blackjack::Commitments> {
    let arr = |o: &Offer| -> Result<[[u8; 32]; lngap_blackjack::K]> {
        let v: Vec<[u8; 32]> = o.commits.iter().map(|h| hex::decode(h).ok().and_then(|b| b.try_into().ok()).ok_or_else(|| anyhow!("a commitment is 32 bytes"))).collect::<Result<_>>()?;
        v.try_into().map_err(|_| anyhow!("sixteen commitments"))
    };
    Ok(lngap_blackjack::Commitments { player: arr(user)?, house: arr(hub)? })
}

/// Hand `h`'s terms, proposed by the player (D55's clock: move `d` due at
/// `t0 + d·ell`; claims from the due time plus `margin`).
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct ContractJson {
    pub value: u64,
    pub deadline: u32,
    pub t0: u32,
    pub ell: u32,
    pub margin: u32,
    pub deposit: u64,
}

pub type SigsJson = BTreeMap<String, String>;
