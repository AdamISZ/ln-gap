//! Off-chain auditor (N8): checks the anchor chain against the hub's
//! published ledger and receipts. Findings are reported, not enforced.

use bitcoin::key::XOnlyPublicKey;
use bitcoin::{OutPoint, Transaction};

use crate::anchor::verify_anchor_output;
use crate::hub::ReceiptRecord;
use crate::registry::Ledger;

/// `anchors`: (confirmation height, tx, anchor outpoint) in chain order, genesis first.
pub fn audit(hub_key: &XOnlyPublicKey, anchors: &[(u32, Transaction, OutPoint)], ledger: &Ledger, receipts: &[(u32, ReceiptRecord)]) -> Vec<String> {
    let mut findings = Vec::new();
    for (i, (h, tx, op)) in anchors.iter().enumerate() {
        if i > 0 {
            let prev = &anchors[i - 1].2;
            if tx.input.len() != 1 || tx.input[0].previous_output != *prev {
                findings.push(format!("anchor at {h} does not spend the previous anchor: chain broken"));
            }
        }
        let root = ledger.as_of(*h).root();
        if !verify_anchor_output(&tx.output[op.vout as usize].script_pubkey, hub_key, &root) {
            findings.push(format!("anchor at {h} commits a root that is not the published ledger as of {h}: equivocation or hidden entries"));
        }
    }
    for (req_id, r) in receipts {
        let present = ledger.events.iter().any(|a| a.event == r.event && a.height <= r.deadline);
        if !present {
            findings.push(format!("receipt {req_id} ({}) promised inclusion by {} but the ledger anchored by then omits it", r.event.describe(), r.deadline));
        }
    }
    findings
}
