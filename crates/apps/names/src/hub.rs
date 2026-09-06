//! The registry operator: receipts requests, anchors the ledger on an
//! interval, attests anchored facts with Lamport statements, and can be
//! told to misbehave in the ways the scenarios need.

use std::collections::{BTreeMap, HashSet};

use anyhow::{anyhow, ensure, Result};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut, Txid};
use lngap_btc::keys::{xonly, Seed};
use lngap_channel::chain::Chain;
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::{PublicKey, Reveal};
use tracing::{info, warn};

use crate::anchor::{anchor_spk, build_anchor_tx};
use crate::registry::{Anchored, Event, Hash32, Ledger};
use crate::statements::{attest_label, attest_value, receipt_label, receipt_value, STATEMENT_BITS};

/// What the user gets back for a request.
#[derive(Clone, Debug)]
pub struct Receipt {
    pub req_id: u32,
    /// The hub promises the event is anchored by this height.
    pub deadline: u32,
    pub pk: PublicKey,
    /// The hub's Lamport signature: preimages for `receipt_value(req_id)`.
    pub reveal: Reveal,
}

#[derive(Clone, Debug)]
pub struct ReceiptRecord {
    pub event: Event,
    pub deadline: u32,
    pub anchored_at: Option<u32>,
}

/// A statement the hub hands out: `(label, value, reveal)`.
pub type Statement = (String, u32, Reveal);

#[derive(Clone, Copy, Debug, Default)]
pub struct HubFaults {
    /// Stop anchoring altogether.
    pub no_anchor: bool,
    /// Never hand out attestations (still anchors).
    pub no_attest: bool,
    /// Accept and receipt this request but leave it out of every anchor.
    pub omit_req: Option<u32>,
    /// Anchor a root that does not match the published ledger.
    pub corrupt_root: bool,
}

pub struct NamesHub {
    anchor_key: Keypair,
    keystore: KeyStore,
    /// Published ledger: anchored events with their heights.
    pub ledger: Ledger,
    pending: Vec<(u32, Event)>,
    pub receipts: BTreeMap<u32, ReceiptRecord>,
    next_req: u32,
    tip: Option<(OutPoint, TxOut, Hash32)>,
    in_flight: Option<(Txid, Vec<(u32, Event)>, Hash32)>,
    pub interval: u32,
    pub receipt_window: u32,
    last_anchor: u32,
    attested: HashSet<String>,
    /// Every anchor the hub broadcast: (height it expected, outpoint, root).
    pub anchors: Vec<(u32, OutPoint, Hash32)>,
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
            in_flight: None,
            interval: 3,
            receipt_window: 10,
            last_anchor: 0,
            attested: HashSet::new(),
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
    /// The genesis anchor commits the empty ledger.
    pub fn genesis_spk(&self) -> ScriptBuf {
        anchor_spk(&self.anchor_pubkey(), &Ledger::default().root())
    }
    pub fn set_genesis(&mut self, op: OutPoint, txout: TxOut, height: u32) {
        let root = Ledger::default().root();
        self.tip = Some((op, txout, root));
        self.last_anchor = height;
        self.anchors.push((height, op, root));
    }
    pub fn tip_outpoint(&self) -> Option<OutPoint> {
        self.tip.as_ref().map(|t| t.0)
    }

    // ----- statement keys -----

    pub fn receipt_pk(&mut self, req_id: u32) -> PublicKey {
        self.keystore.generate(&receipt_label(req_id), STATEMENT_BITS).expect("fresh label")
    }
    pub fn statement_pk(&self, label: &str) -> Option<PublicKey> {
        self.keystore.public(label).ok()
    }
    pub fn attest_pk(&mut self, name: &str, owner: &XOnlyPublicKey) -> PublicKey {
        self.keystore.generate(&attest_label(name, owner), STATEMENT_BITS).expect("fresh label")
    }
    /// The attestation for `(name, owner)` if the anchored ledger shows it.
    pub fn attestation(&mut self, name: &str, owner: &XOnlyPublicKey) -> Option<Statement> {
        if self.ledger.resolve(name)? != *owner {
            return None;
        }
        let label = attest_label(name, owner);
        let value = attest_value(name, owner);
        self.keystore.generate(&label, STATEMENT_BITS).ok()?;
        let r = self.keystore.reveal_uint(&label, value).ok()?;
        Some((label, value, r))
    }

    // ----- requests -----

    pub fn receipt(&mut self, event: Event, height: u32) -> Result<Receipt> {
        if let Event::Reveal { name, .. } | Event::Transfer { name, .. } = &event {
            ensure!(name.len() <= crate::registry::MAX_NAME && name.is_ascii(), "bad name");
        }
        let req_id = self.next_req;
        self.next_req += 1;
        let deadline = height + self.receipt_window;
        let pk = self.receipt_pk(req_id);
        let reveal = self.keystore.reveal_uint(&receipt_label(req_id), receipt_value(req_id))?;
        self.receipts.insert(req_id, ReceiptRecord { event: event.clone(), deadline, anchored_at: None });
        if self.faults.omit_req == Some(req_id) {
            warn!("registry: FAULT omitting receipted request {req_id}");
            self.say(format!("receipted request {req_id} ({}) by {deadline} — and will OMIT it", event.describe()));
        } else {
            self.say(format!("receipted request {req_id} ({}) by {deadline}", event.describe()));
            self.pending.push((req_id, event));
        }
        Ok(Receipt { req_id, deadline, pk, reveal })
    }
    pub fn issued(&self, req_id: u32) -> bool {
        self.receipts.contains_key(&req_id)
    }

    // ----- clock -----

    /// See a block; anchor if due. Returns new attestations to hand out.
    pub fn on_block(&mut self, height: u32, txs: &[Transaction], chain: &dyn Chain) -> Result<Vec<Statement>> {
        let mut out = Vec::new();
        // did our in-flight anchor confirm?
        if let Some((txid, events, root)) = self.in_flight.clone() {
            if txs.iter().any(|t| t.compute_txid() == txid) {
                let ids: Vec<u32> = events.iter().map(|e| e.0).collect();
                for (req_id, e) in events {
                    self.ledger.events.push(Anchored { event: e, height });
                    if let Some(r) = self.receipts.get_mut(&req_id) {
                        r.anchored_at = Some(height);
                    }
                }
                ensure!(self.faults.corrupt_root || self.ledger.root() == root, "anchor at {height} confirmed at an unexpected height; root mismatch");
                self.in_flight = None;
                self.last_anchor = height;
                self.say(format!("anchor confirmed at {height} carrying requests {ids:?}; root {}", hex::encode(&root[..8])));
                out.extend(self.attest_new(height));
            }
        }
        if self.in_flight.is_none() && !self.faults.no_anchor && height >= self.last_anchor + self.interval && !self.pending.is_empty() {
            self.anchor(height, chain)?;
        }
        Ok(out)
    }

    fn anchor(&mut self, height: u32, chain: &dyn Chain) -> Result<()> {
        let (prev_op, prev_out, prev_root) = self.tip.clone().ok_or_else(|| anyhow!("no genesis anchor"))?;
        let events = std::mem::take(&mut self.pending);
        let confirm_at = height + 1;
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
        let tx = build_anchor_tx(&self.anchor_key, (prev_op, prev_out), &prev_root, &root, Amount::from_sat(1_000))?;
        let txid = chain.broadcast(&tx)?;
        let ids: Vec<u32> = events.iter().map(|e| e.0).collect();
        self.say(format!("broadcast anchor {txid} for requests {ids:?}, root {}", hex::encode(&root[..8])));
        self.tip = Some((OutPoint { txid, vout: 0 }, tx.output[0].clone(), root));
        self.anchors.push((confirm_at, OutPoint { txid, vout: 0 }, root));
        self.in_flight = Some((txid, events, root));
        Ok(())
    }

    /// Attest every name whose anchored owner is new.
    fn attest_new(&mut self, _height: u32) -> Vec<Statement> {
        let mut out = Vec::new();
        if self.faults.no_attest {
            return out;
        }
        let names: Vec<String> = self.ledger.events.iter().filter_map(|a| a.event.name().map(str::to_string)).collect();
        for n in names {
            if let Some(owner) = self.ledger.resolve(&n) {
                let label = attest_label(&n, &owner);
                if self.attested.insert(label.clone()) {
                    let value = attest_value(&n, &owner);
                    self.keystore.generate(&label, STATEMENT_BITS).expect("key");
                    let r = self.keystore.reveal_uint(&label, value).expect("reveal");
                    self.say(format!("attesting {label}"));
                    out.push((label, value, r));
                }
            }
        }
        out
    }
}
