//! The registry operator: receipts requests with a promised anchor height,
//! builds anchors for the world to mine, serves the ledger, and can be told
//! to misbehave in the ways the scenarios need. It hands out no attestations:
//! every fact about the registry is proven from the chain.

use std::collections::BTreeMap;

use anyhow::{anyhow, ensure, Result};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::{xonly, Seed};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::{PublicKey, Reveal};
use lngap_spv::chain::{anchor_bytes, RawHeader};
use lngap_spv::{AnchorData, AnchorShape, HeaderShape};
use tracing::{info, warn};

use crate::anchor::{anchor_spk, build_anchor_tx};
use crate::registry::{Anchored, Event, Hash32, Ledger};
use crate::statements::{receipt_label, receipt_value, STATEMENT_BITS};

/// What the user gets back for a request.
#[derive(Clone, Debug)]
pub struct Receipt {
    pub req_id: u32,
    /// The hub promises the event is in the anchor confirming at this height.
    pub promised_height: u32,
    pub pk: PublicKey,
    /// The hub's Lamport signature: preimages for `receipt_value(req_id)`.
    pub reveal: Reveal,
    /// The constants of the inclusion proof the hub will owe.
    pub shape: AnchorShape,
}

#[derive(Clone, Debug)]
pub struct ReceiptRecord {
    pub event: Event,
    pub promised_height: u32,
    pub anchored_at: Option<u32>,
    pub shape: AnchorShape,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct HubFaults {
    /// Stop anchoring altogether.
    pub no_anchor: bool,
    /// Accept and receipt this request but leave it out of every anchor.
    pub omit_req: Option<u32>,
    /// Anchor a root that does not match the published ledger.
    pub corrupt_root: bool,
}

/// An anchor the hub built: confirmation height, its outpoint (the change
/// output the next anchor spends), root, transaction.
#[derive(Clone, Debug)]
pub struct AnchorRecord {
    pub height: u32,
    pub outpoint: OutPoint,
    pub root: Hash32,
    pub tx: Option<Transaction>,
}

pub struct NamesHub {
    anchor_key: Keypair,
    keystore: KeyStore,
    /// Published ledger: anchored events with their heights.
    pub ledger: Ledger,
    pending: Vec<(u32, Event)>,
    pub receipts: BTreeMap<u32, ReceiptRecord>,
    next_req: u32,
    tip: Option<(OutPoint, TxOut)>,
    /// Confirmation height of the next anchor (the one pending requests go in).
    scheduled: Option<u32>,
    in_flight: Option<(Transaction, Vec<(u32, Event)>, Hash32, u32)>,
    pub interval: u32,
    last_anchor: u32,
    pub anchors: Vec<AnchorRecord>,
    pub faults: HubFaults,
    pub log: Vec<String>,
}

impl NamesHub {
    pub fn new(seed: &Seed) -> NamesHub {
        NamesHub {
            anchor_key: seed.keypair("anchor"),
            keystore: KeyStore::new(seed.child("statements")),
            ledger: Ledger::default(),
            pending: Vec::new(),
            receipts: BTreeMap::new(),
            next_req: 1,
            tip: None,
            scheduled: None,
            in_flight: None,
            interval: 3,
            last_anchor: 0,
            anchors: Vec::new(),
            faults: HubFaults::default(),
            log: Vec::new(),
        }
    }

    fn say(&mut self, s: String) {
        info!(hub = "registry", "{s}");
        self.log.push(format!("[registry] {s}"));
    }

    pub fn anchor_pubkey(&self) -> XOnlyPublicKey {
        xonly(&self.anchor_key)
    }
    /// The genesis anchor: a plain output of the anchor key.
    pub fn genesis_spk(&self) -> ScriptBuf {
        anchor_spk(&self.anchor_key)
    }
    pub fn set_genesis(&mut self, op: OutPoint, txout: TxOut, height: u32) {
        self.tip = Some((op, txout));
        self.last_anchor = height;
        self.anchors.push(AnchorRecord { height, outpoint: op, root: Ledger::default().root(), tx: None });
    }
    pub fn tip_outpoint(&self) -> Option<OutPoint> {
        self.tip.as_ref().map(|t| t.0)
    }
    /// The outpoint the next anchor will spend (after any in-flight one).
    fn next_prev(&self) -> Option<OutPoint> {
        match &self.in_flight {
            Some((tx, ..)) => Some(OutPoint { txid: tx.compute_txid(), vout: 1 }),
            None => self.tip_outpoint(),
        }
    }

    // ----- statement keys -----

    pub fn receipt_pk(&mut self, req_id: u32) -> PublicKey {
        self.keystore.generate(&receipt_label(req_id), STATEMENT_BITS).expect("fresh label")
    }
    pub fn statement_pk(&self, label: &str) -> Option<PublicKey> {
        self.keystore.public(label).ok()
    }

    // ----- requests -----

    /// Receipt `event` at `height`, whose block is `checkpoint` (digest,
    /// nBits). The hub promises the event in the next anchor it schedules.
    pub fn receipt(&mut self, event: Event, height: u32, checkpoint: Hash32, nbits: u32) -> Result<Receipt> {
        if let Event::Reveal { name, .. } | Event::Transfer { name, .. } = &event {
            ensure!(name.len() <= crate::registry::MAX_NAME && name.is_ascii(), "bad name");
        }
        let req_id = self.next_req;
        self.next_req += 1;
        let latest = self.in_flight.as_ref().map(|f| f.3).unwrap_or(self.last_anchor);
        let promised = *self.scheduled.get_or_insert((latest + self.interval).max(height + 2));
        let prev_anchor = self.next_prev().ok_or_else(|| anyhow!("no genesis anchor"))?;
        let shape = AnchorShape {
            chain: HeaderShape { checkpoint, nbits, n_headers: (promised - height) as usize },
            prev_anchor,
            entry: event.entry(),
            key: event.key(),
            merkle_sides: vec![true],
        };
        let pk = self.receipt_pk(req_id);
        let reveal = self.keystore.reveal_uint(&receipt_label(req_id), receipt_value(req_id))?;
        self.receipts.insert(req_id, ReceiptRecord { event: event.clone(), promised_height: promised, anchored_at: None, shape: shape.clone() });
        if self.faults.omit_req == Some(req_id) {
            warn!("registry: FAULT omitting receipted request {req_id}");
            self.say(format!("receipted request {req_id} ({}) for the anchor at {promised} — and will OMIT it", event.describe()));
        } else {
            self.say(format!("receipted request {req_id} ({}) for the anchor at {promised}", event.describe()));
            self.pending.push((req_id, event));
        }
        Ok(Receipt { req_id, promised_height: promised, pk, reveal, shape })
    }
    pub fn issued(&self, req_id: u32) -> bool {
        self.receipts.contains_key(&req_id)
    }

    // ----- clock -----

    /// See a block. Returns the anchor transaction to mine in the *next*
    /// block, if one is due, and the request ids an anchor just confirmed.
    pub fn on_block(&mut self, height: u32, txs: &[Transaction]) -> Result<(Option<Transaction>, Vec<u32>)> {
        let mut confirmed = Vec::new();
        if let Some((tx, events, root, expected)) = self.in_flight.clone() {
            if txs.iter().any(|t| t.compute_txid() == tx.compute_txid()) {
                ensure!(height == expected, "anchor confirmed at {height}, promised {expected}");
                for (req_id, e) in events {
                    self.ledger.events.push(Anchored { event: e, height });
                    if let Some(r) = self.receipts.get_mut(&req_id) {
                        r.anchored_at = Some(height);
                    }
                    confirmed.push(req_id);
                }
                ensure!(self.faults.corrupt_root || self.ledger.root() == root, "root mismatch at {height}");
                let op = OutPoint { txid: tx.compute_txid(), vout: 1 };
                self.tip = Some((op, tx.output[1].clone()));
                self.anchors.push(AnchorRecord { height, outpoint: op, root, tx: Some(tx) });
                self.in_flight = None;
                self.last_anchor = height;
                self.say(format!("anchor confirmed at {height} carrying requests {confirmed:?}; root {}", hex::encode(&root[..8])));
            }
        }
        let mut next = None;
        if self.scheduled == Some(height + 1) {
            if self.faults.no_anchor {
                self.say(format!("FAULT: not anchoring (an anchor was promised at {})", height + 1));
                self.scheduled = None;
            } else if self.in_flight.is_none() {
                next = Some(self.anchor(height + 1)?);
            }
        }
        Ok((next, confirmed))
    }

    fn anchor(&mut self, confirm_at: u32) -> Result<Transaction> {
        let (prev_op, prev_out) = self.tip.clone().ok_or_else(|| anyhow!("no genesis anchor"))?;
        let events = std::mem::take(&mut self.pending);
        let mut next = self.ledger.clone();
        for (_, e) in &events {
            next.events.push(Anchored { event: e.clone(), height: confirm_at });
        }
        let mut root = next.root();
        if self.faults.corrupt_root {
            let mut bogus = next.clone();
            bogus.events.push(Anchored { event: Event::Commit { c: [0xEE; 32] }, height: confirm_at });
            root = bogus.root();
            self.say("FAULT: anchoring a root that does not match the published ledger".into());
        }
        let tx = build_anchor_tx(&self.anchor_key, (prev_op, prev_out), &root, Amount::from_sat(1_000))?;
        let ids: Vec<u32> = events.iter().map(|e| e.0).collect();
        self.say(format!("built anchor {} for requests {ids:?}, root {}, to confirm at {confirm_at}", tx.compute_txid(), hex::encode(&root[..8])));
        self.in_flight = Some((tx.clone(), events, root, confirm_at));
        self.scheduled = None;
        Ok(tx)
    }

    /// The hub's inclusion-proof data for a receipted request, given the
    /// headers from the receipt's block to the anchor's block and the
    /// anchor transaction's Merkle siblings. The ledger path is taken from
    /// the ledger as of the anchor (so an omitted entry yields a
    /// non-inclusion path and a corrupt root a path to the wrong root).
    pub fn inclusion_data(&self, req_id: u32, headers: Vec<RawHeader>, merkle_siblings: Vec<[u8; 32]>) -> Result<AnchorData> {
        let r = self.receipts.get(&req_id).ok_or_else(|| anyhow!("no receipt {req_id}"))?;
        let h = r.anchored_at.unwrap_or(r.promised_height);
        let a = self.anchors.iter().find(|a| a.height == h).ok_or_else(|| anyhow!("no anchor at {h}"))?;
        let tx = a.tx.as_ref().ok_or_else(|| anyhow!("genesis has no transaction"))?;
        let path = self.ledger.as_of(h).path(r.shape.key);
        Ok(AnchorData { headers, anchor_tx: anchor_bytes(tx), merkle_siblings, ledger_siblings: path.siblings })
    }
}
