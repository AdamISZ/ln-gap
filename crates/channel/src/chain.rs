//! What a party needs from the chain: broadcast and the current height.
//! Blocks are *pushed* to parties by whoever drives the clock (the harness).

use std::sync::Arc;

use anyhow::Result;
use bitcoin::{Transaction, Txid};
use lngap_btc::regtest::Regtest;

pub trait Chain: Send + Sync {
    fn broadcast(&self, tx: &Transaction) -> Result<Txid>;
    fn height(&self) -> Result<u32>;
}

impl Chain for Regtest {
    fn broadcast(&self, tx: &Transaction) -> Result<Txid> {
        self.send_raw(tx)
    }
    fn height(&self) -> Result<u32> {
        Regtest::height(self)
    }
}

impl<T: Chain + ?Sized> Chain for Arc<T> {
    fn broadcast(&self, tx: &Transaction) -> Result<Txid> {
        (**self).broadcast(tx)
    }
    fn height(&self) -> Result<u32> {
        (**self).height()
    }
}

/// A broadcast the party made, for the harness log.
#[derive(Clone, Debug)]
pub struct Broadcast {
    pub txid: Txid,
    pub role: String,
    pub by: crate::Role,
}
