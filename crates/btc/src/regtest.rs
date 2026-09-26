//! A throwaway regtest `bitcoind` for tests and the scenario harness.
//!
//! Spawns `bitcoind -regtest -txindex=1 -acceptnonstdtxn=1 -fallbackfee=0.0001`
//! on a free port with its own datadir, creates a wallet, and mines to it.
//! Set `LNGAP_BITCOIND` to pick the binary and `LNGAP_KEEP_DATADIR=1` to keep
//! the datadir after the run (its path is logged).

use std::net::TcpListener;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{anyhow, bail, Context, Result};
use bitcoin::consensus::encode::serialize_hex;
use bitcoin::{Address, Amount, BlockHash, Network, OutPoint, Script, Transaction, TxOut, Txid};
use bitcoincore_rpc::{Auth, Client, RpcApi};
use tracing::{debug, info};

pub struct Regtest {
    /// `None` when attached to a node someone else runs ([`Regtest::attach`]).
    child: Option<Child>,
    pub rpc: Client,
    datadir: PathBuf,
    keep: bool,
    _tmp: Option<tempfile::TempDir>,
    mine_to: Address,
}

/// If `tools/explorer.sh` left a node running on this datadir (it records
/// its RPC port in `<datadir>/rpcport`), stop it and wait for it to exit.
fn stop_node_serving(datadir: &std::path::Path) {
    let Ok(port) = std::fs::read_to_string(datadir.join("rpcport")) else { return };
    let port = port.trim();
    let bin = std::env::var("LNGAP_BITCOIN_CLI").unwrap_or_else(|_| "bitcoin-cli".into());
    let ok = Command::new(&bin)
        .args(["-regtest", &format!("-datadir={}", datadir.display()), &format!("-rpcport={port}"), "stop"])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
    if ok {
        info!(datadir = %datadir.display(), port, "stopped the node still serving the old chain");
        let lock = datadir.join("regtest").join(".lock");
        for _ in 0..100 {
            // bitcoind removes nothing on exit, but the lock becomes acquirable; poll the RPC instead
            let alive = Command::new(&bin)
                .args(["-regtest", &format!("-datadir={}", datadir.display()), &format!("-rpcport={port}"), "getblockcount"])
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
            if !alive {
                break;
            }
            std::thread::sleep(Duration::from_millis(100));
        }
        let _ = lock;
        std::thread::sleep(Duration::from_millis(500));
    }
}

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

impl Regtest {
    /// Start a node and mine `initial_blocks` (coinbase maturity needs > 100).
    pub fn start() -> Result<Regtest> {
        Regtest::start_with(201)
    }

    pub fn start_with(initial_blocks: u64) -> Result<Regtest> {
        Regtest::start_inner(initial_blocks, None)
    }

    /// Start a node on a FIXED datadir (wiped first, kept afterwards): the
    /// interactive demo's node, which other processes [`attach`] to. The
    /// RPC port is recorded in `<datadir>/rpcport`.
    ///
    /// [`attach`]: Regtest::attach
    pub fn start_in(datadir: PathBuf, initial_blocks: u64) -> Result<Regtest> {
        Regtest::start_inner(initial_blocks, Some(datadir))
    }

    /// Attach to a running node started with [`Regtest::start_in`] (or by
    /// `tools/explorer.sh`): the RPC port from `<datadir>/rpcport`, the
    /// cookie from the datadir, the `harness` wallet. Dropping an attached
    /// handle does not stop the node.
    pub fn attach(datadir: &std::path::Path) -> Result<Regtest> {
        let port = std::fs::read_to_string(datadir.join("rpcport")).with_context(|| format!("no rpcport file in {}", datadir.display()))?;
        let rpc_port: u16 = port.trim().parse().context("rpcport")?;
        let cookie = datadir.join("regtest").join(".cookie");
        let url = format!("http://127.0.0.1:{rpc_port}");
        let rpc = Client::new(&format!("{url}/wallet/harness"), Auth::CookieFile(cookie))?;
        rpc.get_block_count().with_context(|| format!("no node answering on port {rpc_port}"))?;
        let mine_to = rpc
            .get_new_address(None, Some(bitcoincore_rpc::json::AddressType::Bech32m))?
            .require_network(Network::Regtest)?;
        Ok(Regtest { child: None, rpc, datadir: datadir.to_path_buf(), keep: true, _tmp: None, mine_to })
    }

    fn start_inner(initial_blocks: u64, fixed: Option<PathBuf>) -> Result<Regtest> {
        let bin = std::env::var("LNGAP_BITCOIND").unwrap_or_else(|_| "bitcoind".into());
        let keep = fixed.is_some() || std::env::var("LNGAP_KEEP_DATADIR").map(|v| v == "1").unwrap_or(false);
        let (datadir, tmp) = if let Some(d) = fixed {
            stop_node_serving(&d);
            if d.exists() {
                std::fs::remove_dir_all(&d).with_context(|| format!("wiping {}", d.display()))?;
            }
            std::fs::create_dir_all(&d)?;
            (d, None)
        } else if keep {
            let label = std::env::var("LNGAP_RUN_LABEL").unwrap_or_default();
            let base = std::env::current_dir()?.join("regtest-data");
            let d = if label.is_empty() {
                // ad-hoc (e.g. tests): a unique directory per node
                static N: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
                let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                base.join(format!("run-{}-{n}", std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_millis()))
            } else {
                // one fixed directory per scenario, wiped every run: a run is
                // throwaway and reproducible in seconds
                let d = base.join(&label);
                stop_node_serving(&d);
                if d.exists() {
                    std::fs::remove_dir_all(&d).with_context(|| format!("wiping {}", d.display()))?;
                }
                d
            };
            std::fs::create_dir_all(&d)?;
            (d, None)
        } else {
            let t = tempfile::Builder::new().prefix("lngap-regtest-").tempdir()?;
            (t.path().to_path_buf(), Some(t))
        };
        let rpc_port = free_port();
        let p2p_port = free_port();
        let child = Command::new(&bin)
            .args([
                "-regtest",
                "-server=1",
                "-listen=0",
                "-txindex=1",
                "-acceptnonstdtxn=1",
                "-fallbackfee=0.0001",
                "-debuglogfile=debug.log",
                &format!("-datadir={}", datadir.display()),
                &format!("-rpcport={rpc_port}"),
                &format!("-port={p2p_port}"),
                "-rpcbind=127.0.0.1",
                "-rpcallowip=127.0.0.1",
            ])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .with_context(|| format!("spawning {bin}"))?;
        info!(datadir = %datadir.display(), rpc_port, "started bitcoind");
        if keep {
            std::fs::write(datadir.join("rpcport"), rpc_port.to_string())?;
        }

        let cookie = datadir.join("regtest").join(".cookie");
        let url = format!("http://127.0.0.1:{rpc_port}");
        let deadline = Instant::now() + Duration::from_secs(60);
        let rpc = loop {
            if cookie.exists() {
                if let Ok(c) = Client::new(&url, Auth::CookieFile(cookie.clone())) {
                    if c.get_block_count().is_ok() {
                        break c;
                    }
                }
            }
            if Instant::now() > deadline {
                bail!("bitcoind did not come up within 60s (datadir {})", datadir.display());
            }
            std::thread::sleep(Duration::from_millis(100));
        };
        rpc.create_wallet("harness", None, None, None, None)?;
        let rpc = Client::new(&format!("{url}/wallet/harness"), Auth::CookieFile(cookie))?;
        let mine_to = rpc
            .get_new_address(None, Some(bitcoincore_rpc::json::AddressType::Bech32m))?
            .require_network(Network::Regtest)?;
        let rt = Regtest { child: Some(child), rpc, datadir, keep, _tmp: tmp, mine_to };
        rt.mine(initial_blocks)?;
        Ok(rt)
    }

    pub fn datadir(&self) -> &PathBuf {
        &self.datadir
    }

    pub fn height(&self) -> Result<u32> {
        Ok(self.rpc.get_block_count()? as u32)
    }

    /// Mine `n` blocks to the harness wallet; returns their hashes.
    pub fn mine(&self, n: u64) -> Result<Vec<BlockHash>> {
        let hashes = self.rpc.generate_to_address(n, &self.mine_to)?;
        debug!(n, height = self.height()?, "mined");
        Ok(hashes)
    }

    /// Mine until the chain reaches `height`.
    pub fn mine_to_height(&self, height: u32) -> Result<()> {
        let h = self.height()?;
        if height > h {
            self.mine(u64::from(height - h))?;
        }
        Ok(())
    }

    /// Pay `amount` to `spk` from the harness wallet and confirm it in one block.
    pub fn fund(&self, spk: &Script, amount: Amount) -> Result<(OutPoint, TxOut)> {
        let addr = Address::from_script(spk, Network::Regtest)?;
        let txid = self.rpc.send_to_address(&addr, amount, None, None, None, None, None, None)?;
        self.mine(1)?;
        let tx = self.get_tx(&txid)?;
        let vout = tx
            .output
            .iter()
            .position(|o| o.script_pubkey.as_bytes() == spk.as_bytes())
            .ok_or_else(|| anyhow!("funding output not found"))?;
        Ok((OutPoint { txid, vout: vout as u32 }, tx.output[vout].clone()))
    }

    pub fn send_raw(&self, tx: &Transaction) -> Result<Txid> {
        let txid = self
            .rpc
            .send_raw_transaction(serialize_hex(tx))
            .with_context(|| format!("sendrawtransaction of {}", tx.compute_txid()))?;
        Ok(txid)
    }

    /// `sendrawtransaction` with `maxfeerate` 0: the node's "absurdly high
    /// fee" refusal is a wallet-protection policy at the RPC layer, and a
    /// transaction that deliberately pays its whole value to fee (the bond
    /// burn race, D46) trips it. Miners have no such limit.
    pub fn send_raw_any_fee(&self, tx: &Transaction) -> Result<Txid> {
        let v: serde_json::Value = self
            .rpc
            .call("sendrawtransaction", &[serde_json::Value::String(serialize_hex(tx)), serde_json::json!(0)])
            .with_context(|| format!("sendrawtransaction (maxfeerate 0) of {}", tx.compute_txid()))?;
        Ok(v.as_str().ok_or_else(|| anyhow!("sendrawtransaction: no txid"))?.parse()?)
    }

    /// Run the transaction through `testmempoolaccept`: `Ok(vsize)` if the
    /// node would accept it, `Err(reject-reason)` otherwise. The real script
    /// interpreter with full consensus flags; policy is relaxed by
    /// `-acceptnonstdtxn`.
    pub fn test_accept(&self, tx: &Transaction) -> std::result::Result<u64, String> {
        let res = self
            .rpc
            .test_mempool_accept(&[serialize_hex(tx)])
            .map_err(|e| format!("rpc: {e}"))?;
        let r = res.into_iter().next().ok_or_else(|| "empty result".to_string())?;
        if r.allowed {
            Ok(r.vsize.unwrap_or(0))
        } else {
            Err(r.reject_reason.unwrap_or_else(|| "rejected".into()))
        }
    }

    /// Broadcast and mine one block; error if the tx is not in that block.
    pub fn send_and_confirm(&self, tx: &Transaction) -> Result<(Txid, u32)> {
        let txid = self.send_raw(tx)?;
        self.mine(1)?;
        let h = self.confirmations(&txid)?.ok_or_else(|| anyhow!("{txid} not confirmed after mining"))?;
        Ok((txid, h))
    }

    pub fn get_tx(&self, txid: &Txid) -> Result<Transaction> {
        Ok(self.rpc.get_raw_transaction(txid, None)?)
    }

    /// Block height the tx confirmed at, if any.
    pub fn confirmations(&self, txid: &Txid) -> Result<Option<u32>> {
        let v: serde_json::Value = self
            .rpc
            .call("getrawtransaction", &[serde_json::Value::String(txid.to_string()), true.into()])?;
        match v.get("blockhash").and_then(|b| b.as_str()) {
            Some(bh) => {
                let bh: BlockHash = bh.parse()?;
                let info: serde_json::Value =
                    self.rpc.call("getblockheader", &[serde_json::Value::String(bh.to_string())])?;
                Ok(info.get("height").and_then(|h| h.as_u64()).map(|h| h as u32))
            }
            None => Ok(None),
        }
    }

    /// Is this outpoint still unspent (confirmed view)?
    pub fn is_unspent(&self, op: &OutPoint) -> Result<bool> {
        Ok(self.rpc.get_tx_out(&op.txid, op.vout, Some(false))?.is_some())
    }

    /// Txids in the block at `height`.
    pub fn block_txids(&self, height: u32) -> Result<Vec<Txid>> {
        let bh = self.rpc.get_block_hash(u64::from(height))?;
        Ok(self.rpc.get_block(&bh)?.txdata.iter().map(|t| t.compute_txid()).collect())
    }

    /// Full transactions in the block at `height`.
    pub fn block_txs(&self, height: u32) -> Result<Vec<Transaction>> {
        let bh = self.rpc.get_block_hash(u64::from(height))?;
        Ok(self.rpc.get_block(&bh)?.txdata)
    }

    pub fn mempool(&self) -> Result<Vec<Txid>> {
        Ok(self.rpc.get_raw_mempool()?)
    }
}

impl Drop for Regtest {
    fn drop(&mut self) {
        let Some(child) = self.child.as_mut() else { return };
        let _ = self.rpc.stop();
        let deadline = Instant::now() + Duration::from_secs(10);
        while Instant::now() < deadline {
            if let Ok(Some(_)) = child.try_wait() {
                break;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
        let _ = child.kill();
        let _ = child.wait();
        if self.keep {
            info!(datadir = %self.datadir.display(), "kept regtest datadir");
        }
    }
}

impl Regtest {
    /// Confirmed balance held by `spk` (via `scantxoutset`).
    pub fn balance_of(&self, spk: &Script) -> Result<Amount> {
        let desc = format!("raw({})", hex::encode(spk.as_bytes()));
        let v: serde_json::Value = self.rpc.call(
            "scantxoutset",
            &[serde_json::Value::String("start".into()), serde_json::json!([desc])],
        )?;
        let btc = v.get("total_amount").and_then(|a| a.as_f64()).unwrap_or(0.0);
        Ok(Amount::from_btc(btc)?)
    }
}

impl Regtest {
    /// Mine one block containing exactly `txs` (plus the coinbase), bypassing
    /// the mempool: the regtest stand-in for a miner including a transaction
    /// directly. Consensus rules still apply; an invalid tx makes the call
    /// fail with the validation error. Returns the block height.
    pub fn mine_with(&self, txs: &[Transaction]) -> Result<u32> {
        let raw: Vec<serde_json::Value> = txs.iter().map(|t| serde_json::Value::String(serialize_hex(t))).collect();
        let v: serde_json::Value = self
            .rpc
            .call("generateblock", &[serde_json::Value::String(self.mine_to.to_string()), serde_json::Value::Array(raw)])
            .context("generateblock")?;
        let bh: BlockHash = v.get("hash").and_then(|h| h.as_str()).ok_or_else(|| anyhow!("generateblock: no hash"))?.parse()?;
        let info: serde_json::Value = self.rpc.call("getblockheader", &[serde_json::Value::String(bh.to_string())])?;
        Ok(info.get("height").and_then(|h| h.as_u64()).map(|h| h as u32).ok_or_else(|| anyhow!("no height"))?)
    }

    /// Consensus-check a transaction by attempting to mine it into a block
    /// on a throwaway basis is not possible without side effects, so this
    /// simply reports whether `generateblock` accepts it (and mines it if so).
    pub fn mine_with_check(&self, tx: &Transaction) -> std::result::Result<u32, String> {
        self.mine_with(std::slice::from_ref(tx)).map_err(|e| format!("{e:#}"))
    }
}
