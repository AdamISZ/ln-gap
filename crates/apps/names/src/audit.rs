//! Off-chain auditor: checks the anchor chain against the hub's published
//! ledger and receipts. Findings are reported; the contracts enforce the
//! same facts on-chain through the inclusion proofs.

use bitcoin::{OutPoint, Transaction};

use crate::anchor::root_of;
use crate::hub::ReceiptRecord;
use crate::registry::Ledger;

/// `anchors`: (confirmation height, tx, anchor outpoint) in chain order, the first after genesis.
pub fn audit(genesis: OutPoint, anchors: &[(u32, Transaction, OutPoint)], ledger: &Ledger, receipts: &[(u32, ReceiptRecord)]) -> Vec<String> {
    let mut findings = Vec::new();
    let mut prev = genesis;
    for (h, tx, op) in anchors {
        if tx.input.len() != 1 || tx.input[0].previous_output != prev {
            findings.push(format!("anchor at {h} does not spend the previous anchor: chain broken"));
        }
        prev = *op;
        match root_of(tx) {
            Ok(root) if root == ledger.as_of(*h).root() => {}
            Ok(_) => findings.push(format!("anchor at {h} commits a root that is not the published ledger as of {h}: equivocation or hidden entries")),
            Err(e) => findings.push(format!("anchor at {h} has a bad shape ({e}): the chain is ambiguous from here")),
        }
    }
    // the same walk a user performs before trusting a receipt's tip
    let txs: Vec<Transaction> = anchors.iter().map(|a| a.1.clone()).collect();
    if let Err(e) = crate::anchor::verify_anchor_chain(genesis, &txs) {
        findings.push(format!("anchor chain walk from genesis fails: {e}"));
    }
    for (req_id, r) in receipts {
        let present = ledger.events.iter().any(|a| a.event == r.event && a.height <= r.promised_height);
        if !present {
            findings.push(format!("receipt {req_id} ({}) promised inclusion at {} but the ledger anchored by then omits it", r.event.describe(), r.promised_height));
        }
    }
    findings
}
