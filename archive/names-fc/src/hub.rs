//! The registry hub on the fact chain.
//!
//! Replaces `lngap_names::hub::NamesHub`. The hub no longer anchors via
//! Bitcoin transactions. Instead it:
//! 1. Receives a request (event) from the user.
//! 2. Promises: "this entry will be in a fact-chain block at height <= h_max."
//! 3. Submits the entry to the miner M (via a shared queue).
//! 4. Watches the fact chain for confirmation.
//! 5. Serves proof data (headers + entry) once the block is mined.

use std::collections::BTreeMap;

use anyhow::{anyhow, ensure, Result};
use lngap_factchain::{ChainClient, FactData, FactShape};
use lngap_n4bit::{hash, Digest};
use lngap_names::registry::{Event, Hash32};
use serde::{Deserialize, Serialize};
use tracing::info;

/// The hub's promise: the entry will be in a fact-chain block at height <= h_max,
/// provable from the checkpoint.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FcPromise {
    pub req_id: u32,
    /// The entry will be in a block at or below this fact-chain height.
    pub h_max: u32,
    /// The fact-chain checkpoint (tip when the promise was made).
    pub checkpoint: Digest,
    pub checkpoint_height: u32,
    /// The canonical 64-byte entry the bond is about.
    #[serde(with = "serde_bytes64")]
    pub entry: [u8; 64],
}

mod serde_bytes64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(v: &[u8; 64], s: S) -> Result<S::Ok, S::Error> {
        hex::encode(v).serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 64], D::Error> {
        let h = <String as Deserialize>::deserialize(d)?;
        let b = hex::decode(h).map_err(serde::de::Error::custom)?;
        b.try_into().map_err(|_| serde::de::Error::custom("64 bytes"))
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct HubFaults {
    /// Stop submitting to the miner altogether.
    pub no_submit: bool,
    /// Promise this request but never submit it.
    pub omit_req: Option<u32>,
}

pub struct FcHub {
    pub ledger: lngap_names::registry::Ledger,
    pub promises: BTreeMap<u32, FcPromise>,
    /// Entries waiting to be submitted to the miner.
    pending_submit: Vec<(u32, [u8; 64])>,
    /// Request IDs that have been confirmed (included in a fact-chain block).
    confirmed: BTreeMap<u32, u32>, // req_id -> fact-chain height
    next_req: u32,
    pub faults: HubFaults,
    pub log: Vec<String>,
}

impl FcHub {
    pub fn new() -> FcHub {
        FcHub {
            ledger: lngap_names::registry::Ledger::default(),
            promises: BTreeMap::new(),
            pending_submit: Vec::new(),
            confirmed: BTreeMap::new(),
            next_req: 1,
            faults: HubFaults::default(),
            log: Vec::new(),
        }
    }

    fn say(&mut self, s: String) {
        info!(hub = "fc-registry", "{s}");
        self.log.push(format!("[fc-registry] {s}"));
    }

    /// Answer a request: promise inclusion by h_max, queue the entry for the miner.
    pub fn promise(
        &mut self,
        event: Event,
        h_max: u32,
        checkpoint: Digest,
        checkpoint_height: u32,
    ) -> Result<FcPromise> {
        if let Event::Reveal { name, .. } | Event::Transfer { name, .. } = &event {
            ensure!(
                name.len() <= lngap_names::registry::MAX_NAME && name.is_ascii(),
                "bad name"
            );
        }
        let req_id = self.next_req;
        self.next_req += 1;
        let entry = event.entry();

        let promise = FcPromise {
            req_id,
            h_max,
            checkpoint,
            checkpoint_height,
            entry,
        };
        self.promises.insert(req_id, promise.clone());

        if self.faults.no_submit || self.faults.omit_req == Some(req_id) {
            self.say(format!(
                "promised request {req_id} ({}) for fact-chain height <= {h_max} — and will NOT submit it",
                event.describe()
            ));
        } else {
            self.say(format!(
                "promised request {req_id} ({}) for fact-chain height <= {h_max}",
                event.describe()
            ));
            self.pending_submit.push((req_id, entry));
        }
        Ok(promise)
    }

    pub fn issued(&self, req_id: u32) -> bool {
        self.promises.contains_key(&req_id)
    }

    /// Drain pending entries that should be submitted to the miner.
    pub fn drain_pending(&mut self) -> Vec<(u32, [u8; 64])> {
        std::mem::take(&mut self.pending_submit)
    }

    /// Called when a fact-chain block is confirmed. Checks which promised
    /// entries are included.
    pub fn on_block(&mut self, height: u32, entry: &[u8]) {
        let newly_confirmed: Vec<u32> = self
            .promises
            .iter()
            .filter(|(req_id, _)| !self.confirmed.contains_key(req_id))
            .filter(|(_, p)| p.entry.as_slice() == entry)
            .map(|(req_id, _)| *req_id)
            .collect();
        for req_id in &newly_confirmed {
            self.confirmed.insert(*req_id, height);
            self.say(format!("request {req_id} confirmed at fact-chain height {height}"));
        }
    }
    pub fn set_ledger(&mut self, ledger: lngap_names::registry::Ledger) {
        self.ledger = ledger;
    }

    pub fn is_confirmed(&self, req_id: u32) -> bool {
        self.confirmed.contains_key(&req_id)
    }

    pub fn confirmed_height(&self, req_id: u32) -> Option<u32> {
        self.confirmed.get(&req_id).copied()
    }

    /// Build the proof data for a confirmed request.
    pub fn inclusion_data(
        &self,
        req_id: u32,
        client: &ChainClient,
    ) -> Result<(FactShape, FactData)> {
        let p = self
            .promises
            .get(&req_id)
            .ok_or_else(|| anyhow!("no promise {req_id}"))?;
        let h = self
            .confirmed_height(req_id)
            .ok_or_else(|| anyhow!("request {req_id} not confirmed"))?;
        let n_headers = (h - p.checkpoint_height) as usize;
        let shape = FactShape {
            checkpoint: p.checkpoint,
            difficulty_bits: lngap_factchain::DIFFICULTY_BITS,
            n_headers,
        };
        let data = shape.build_data(client, &p.entry);
        Ok((shape, data))
    }

    /// Build heavier-chain refutation data: one more header from the same checkpoint.
    pub fn refutation_data(
        &self,
        req_id: u32,
        client: &ChainClient,
    ) -> Result<(FactShape, FactData)> {
        let p = self
            .promises
            .get(&req_id)
            .ok_or_else(|| anyhow!("no promise {req_id}"))?;
        let h = self
            .confirmed_height(req_id)
            .ok_or_else(|| anyhow!("request {req_id} not confirmed"))?;
        let n_headers = (h - p.checkpoint_height) as usize + 1;
        let shape = FactShape {
            checkpoint: p.checkpoint,
            difficulty_bits: lngap_factchain::DIFFICULTY_BITS,
            n_headers,
        };
        // For the refutation, we need the real chain (one header longer).
        // The entry might be different (or absent) on the real chain.
        // For the PoC, the world provides the real chain.
        let data = shape.build_data(client, &p.entry);
        Ok((shape, data))
    }

    pub fn resolve(&self, name: &str) -> Option<bitcoin::key::XOnlyPublicKey> {
        self.ledger.resolve(name)
    }
}

/// Compatibility: the existing names code uses Hash32 = [u8; 32].
/// The fact chain uses Digest = [u8; 20]. This converts.
pub fn hash32_to_digest(h: &Hash32) -> Digest {
    h[..20].try_into().unwrap()
}

/// Hash an entry with n4bit (replaces SHA-256 for the fact chain).
pub fn entry_hash(entry: &[u8; 64]) -> Digest {
    hash(entry)
}
