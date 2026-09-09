//! Hub receipts as 32-bit Lamport slots. A receipt's *label* names the
//! key; its *value* is the request id. Revealing the preimages for that
//! value under that key is the hub saying "request r is accepted and will
//! be anchored at the promised height".

pub const STATEMENT_BITS: usize = 32;

pub fn receipt_label(req_id: u32) -> String {
    format!("receipt/{req_id}")
}
/// A receipt says the request id itself.
pub fn receipt_value(req_id: u32) -> u32 {
    req_id
}
