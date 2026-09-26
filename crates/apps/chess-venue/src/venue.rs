//! The venue process: the regtest node, the roster, the clock. Mines one
//! block every `block_secs`, seals one venue slot per block from the
//! inbox, publishes blocks and deadline flags, funds the contract. With
//! `--web` it also serves its page: the slot timeline and the
//! misbehaviour controls (silence a member; seal a past empty slot LATE).

use std::collections::BTreeSet;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use bitcoin::{Amount, ScriptBuf};
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_ec_wots::Attester;
use lngap_factchain::{entry_head, entry_root, Header};
use lngap_pos::{genesis, Member, PosMiner, SealedBlock};
use tiny_http::{Method, Response, Server};

use crate::store::*;
use crate::web::{body, html, json, DASHBOARD_HTML, VENUE_HTML};

fn members() -> Vec<Member> {
    (0..K as u8).map(|i| Member::new([VENUE_SEED[0] + i; 32])).collect()
}

#[derive(serde::Serialize)]
struct BlockView {
    slot: u32,
    height: u32,
    proposer: usize,
    entry: String,
    flags: Option<usize>,
    late: bool,
}

#[derive(serde::Serialize)]
struct VenueState {
    height: u32,
    b0: u32,
    next_slot: u32,
    block_secs: u64,
    next_tick_secs: u64,
    ready: bool,
    n: usize,
    threshold: u32,
    silent: Vec<usize>,
    blocks: Vec<BlockView>,
    inbox: Vec<String>,
}

#[derive(serde::Deserialize)]
struct Cmd {
    cmd: String,
}

#[derive(serde::Serialize)]
struct CmdResult {
    ok: bool,
    output: String,
}

struct Venue {
    store: Store,
    rt: Regtest,
    miner: PosMiner,
    b0: u32,
    max_slot: u32,
    block_secs: u64,
    ready: bool,
    next: Instant,
    /// Slots sealed late by the misbehaviour control.
    late: BTreeSet<u32>,
}

impl Venue {
    fn height(&self) -> u32 {
        self.rt.height().unwrap_or(0)
    }

    fn next_slot(&self) -> u32 {
        self.height() + 1 - self.b0
    }

    fn state(&self) -> VenueState {
        let h = self.height();
        let mut blocks = Vec::new();
        for s in 1..=self.next_slot().saturating_sub(1) {
            let Ok(Some(b)) = self.store.read::<BlockJson>(&Store::block(s)) else { continue };
            let late = self.store.read::<BlockJson>(&Store::late_block(s)).ok().flatten();
            let flags = self.store.read::<FlagsJson>(&Store::flags(s)).ok().flatten().map(|f| f.iter().filter(|x| x.is_some()).count());
            let describe = |b: &BlockJson| if b.entry.is_empty() { "empty".to_string() } else { format!("an entry of {} bytes", b.entry.len() / 2) };
            blocks.push(BlockView { slot: s, height: self.b0 + s, proposer: b.proposer, entry: describe(&b), flags, late: false });
            if let Some(l) = late {
                blocks.push(BlockView { slot: s, height: h, proposer: l.proposer, entry: describe(&l), flags, late: true });
            }
        }
        let inbox = self.store.list(Store::inbox_dir()).unwrap_or_default().iter().filter_map(|p| std::fs::read_to_string(p).ok()).filter_map(|s| serde_json::from_str::<InboxEntry>(&s).ok()).map(|e| e.from).collect();
        VenueState {
            height: h,
            b0: self.b0,
            next_slot: self.next_slot(),
            block_secs: self.block_secs,
            next_tick_secs: self.next.saturating_duration_since(Instant::now()).as_secs(),
            ready: self.ready,
            n: self.miner.n(),
            threshold: lngap_pos::Roster::majority(self.miner.n()),
            silent: (0..self.miner.n()).filter(|i| self.miner.is_silent(*i)).collect(),
            blocks,
            inbox,
        }
    }

    /// One tick: a block, a slot, the deadlines.
    fn tick(&mut self) -> Result<()> {
        self.rt.mine(1)?;
        let h = self.height();
        let slot = h - self.b0;
        if slot > self.max_slot {
            println!("venue: height {h}: beyond the registry (slot {slot} > {}); mining on without sealing", self.max_slot);
            return Ok(());
        }
        let mut from = None;
        if let Some(e) = self.take_inbox()? {
            self.miner.submit(hex::decode(&e.entry)?);
            from = Some(e.from);
        }
        match self.miner.seal_next(slot) {
            Ok((block, _table)) => {
                self.store.write(&Store::block(slot), &BlockJson::from_block(&block))?;
                match from {
                    Some(f) => println!("venue: height {h}: slot {slot} sealed by member {} with {f}'s entry ({} bytes)", block.proposer, block.entry.len()),
                    None => println!("venue: height {h}: slot {slot} sealed EMPTY by member {}", block.proposer),
                }
            }
            Err(e) => println!("venue: height {h}: slot {slot} NOT sealed: {e}"),
        }
        self.deadlines(slot, h)?;
        Ok(())
    }

    fn take_inbox(&self) -> Result<Option<InboxEntry>> {
        let inbox = self.store.list(Store::inbox_dir())?;
        let Some(p) = inbox.first() else { return Ok(None) };
        let e = serde_json::from_str::<InboxEntry>(&std::fs::read_to_string(p)?).ok();
        self.store.remove(p);
        Ok(e)
    }

    fn deadlines(&mut self, slot: u32, h: u32) -> Result<()> {
        for s in 1..slot {
            if self.store.exists(&Store::flags(s)) {
                continue;
            }
            let empty = self.store.read::<BlockJson>(&Store::block(s))?.map(|b| b.entry.is_empty()).unwrap_or(true);
            if empty {
                let f = self.miner.flag(s);
                self.store.write(&Store::flags(s), &flags_to_json(&f))?;
                println!("venue: height {h}: slot {s} passed its deadline empty — {} of {} members flag it", f.iter().filter(|x| x.is_some()).count(), self.miner.n());
            }
        }
        Ok(())
    }

    /// The misbehaviour control: seal a past EMPTY slot again, late, with
    /// the queued entry, tagged by member `by` — a second block at the
    /// slot on the same parent (the D50 fixture).
    fn seal_late(&mut self, slot: u32, by: usize) -> Result<String> {
        anyhow::ensure!(slot >= 1 && slot < self.next_slot(), "slot {slot} has not been sealed yet");
        anyhow::ensure!(by < self.miner.n(), "no member {by}");
        let on_time = self.store.read::<BlockJson>(&Store::block(slot))?.ok_or_else(|| anyhow!("no block at slot {slot}"))?.to_block()?;
        anyhow::ensure!(on_time.entry.is_empty(), "slot {slot} was not empty on time");
        let e = self.take_inbox()?.ok_or_else(|| anyhow!("nothing queued in the inbox to seal late"))?;
        let entry = hex::decode(&e.entry)?;
        let header = Header::new(&on_time.header.prev(), &entry_root(&entry), &entry_head(&entry), slot);
        let table = self.miner.table(slot).clone();
        let attestation = self.miner.content().attest(&table, header.as_bytes());
        let late = SealedBlock { header, entry, attestation, proposer: by, proposer_secret: self.miner.proposer_secret(by, slot) };
        self.store.write(&Store::late_block(slot), &BlockJson::from_block(&late))?;
        self.late.insert(slot);
        let msg = format!("slot {slot} sealed AGAIN, LATE, by member {by} with {}'s queued entry (the on-time block was empty; the flags for it stand)", e.from);
        println!("venue: {msg}");
        Ok(msg)
    }

    fn exec(&mut self, cmd: &str) -> Result<String> {
        let parts: Vec<&str> = cmd.split_whitespace().collect();
        match parts.as_slice() {
            ["silence", i] => {
                let i: usize = i.parse()?;
                anyhow::ensure!(i < self.miner.n(), "no member {i}");
                self.miner.silence(i);
                Ok(format!("member {i} is silent: it seals nothing and flags nothing"))
            }
            ["wake", i] => {
                let i: usize = i.parse()?;
                self.miner.wake(i);
                Ok(format!("member {i} is back"))
            }
            ["late", s, by] => self.seal_late(s.parse()?, by.parse()?),
            ["late", s] => self.seal_late(s.parse()?, 1),
            ["mine"] => {
                self.next = Instant::now();
                Ok("mining at once".into())
            }
            _ => Err(anyhow!("unknown command (silence <i> | wake <i> | late <slot> [member] | mine)")),
        }
    }
}

pub fn run(dir: PathBuf, block_secs: u64, max_depth: u32, web: Option<u16>) -> Result<()> {
    let store = Store::new(dir.clone());
    std::fs::create_dir_all(&dir)?;
    for stale in ["venue", "players", "node.json"] {
        let p = dir.join(stale);
        if p.is_dir() {
            std::fs::remove_dir_all(&p)?;
        } else if p.is_file() {
            std::fs::remove_file(&p)?;
        }
    }
    println!("venue: starting a regtest node in {}", dir.join("node").display());
    let rt = Regtest::start_in(dir.join("node"), 201).context("starting bitcoind (set LNGAP_BITCOIND if it is not on PATH)")?;
    store.write(Store::node(), &NodeInfo { datadir: rt.datadir().display().to_string() })?;

    let max_slot = max_depth + 120;
    let members = members();
    let (gen, _t0) = genesis(&Attester::new(VENUE_SEED), &members[0], 0);
    let mut miner = PosMiner::new(VENUE_SEED, members, gen.header.digest(), 0);
    print!("venue: computing the content registry for slots 0..={max_slot} ({} tables)... ", max_slot + 1);
    let t = Instant::now();
    let registry = miner.registry(max_slot)?;
    println!("{:.1}s", t.elapsed().as_secs_f64());
    store.write(Store::registry(), &registry)?;
    let n = registry.n();
    let threshold = registry.threshold;
    println!("venue: {n} members sharing one content key, flag threshold {threshold} of {n} (the majority); any member seals any slot");

    let b0 = rt.height()? + 1;
    store.write(Store::params(), &VenueParams { b0, max_slot, block_secs, n, threshold, max_depth })?;
    println!("venue: the contract will be funded at height {b0}; slot s seals at height {b0} + s");
    let server = match web {
        Some(port) => {
            let s = Server::http(("127.0.0.1", port)).map_err(|e| anyhow!("binding 127.0.0.1:{port}: {e}"))?;
            println!("venue: browse http://127.0.0.1:{port} (the dashboard at /dashboard once the players are up)");
            Some(s)
        }
        None => None,
    };
    let mut v = Venue { store, rt, miner, b0, max_slot, block_secs, ready: false, next: Instant::now(), late: BTreeSet::new() };
    println!("venue: waiting for the players' contract (both `play` processes must be up)...");

    // phase 1: fund the contract when proposed; phase 2: wait for both
    // players to be ready; phase 3: tick. Requests are served throughout.
    let mut funded = false;
    loop {
        if !funded {
            if let Some(c) = v.store.read::<ContractJson>(Store::contract())? {
                let spk = ScriptBuf::from_bytes(hex::decode(&c.spk)?);
                let (op, prev) = v.rt.fund(&spk, Amount::from_sat(c.value))?;
                let h = v.rt.height()?;
                anyhow::ensure!(h == b0, "funding landed at height {h} instead of {b0}");
                v.store.write(Store::funded(), &FundedJson { txid: op.txid.to_string(), vout: op.vout, value: prev.value.to_sat(), spk: c.spk.clone(), height: h })?;
                println!("venue: funded the contract output {}:{} with {} sat at height {h}; waiting for both players to finish signing...", op.txid, op.vout, c.value);
                funded = true;
            }
        } else if !v.ready {
            if v.store.exists(&Store::ready(Role::User)) && v.store.exists(&Store::ready(Role::Hub)) {
                v.ready = true;
                v.next = Instant::now() + Duration::from_secs(block_secs);
                println!("venue: both ready. Slot 1 seals at height {} in {block_secs}s; one block every {block_secs}s. Ctrl-C stops the node.", b0 + 1);
            }
        } else if Instant::now() >= v.next {
            v.next += Duration::from_secs(block_secs);
            if v.next < Instant::now() {
                v.next = Instant::now() + Duration::from_secs(block_secs);
            }
            v.tick()?;
        }
        // requests, or a short sleep
        match &server {
            Some(s) => {
                if let Some(mut req) = s.recv_timeout(Duration::from_millis(250))? {
                    let url = req.url().to_string();
                    let path = url.split('?').next().unwrap_or("").to_string();
                    let _ = match (req.method(), path.as_str()) {
                        (Method::Get, "/") => req.respond(html(VENUE_HTML)),
                        (Method::Get, "/dashboard") => req.respond(html(DASHBOARD_HTML)),
                        (Method::Get, "/ports") => {
                            let port = |r: Role| v.store.read::<serde_json::Value>(&Store::web(r)).ok().flatten().and_then(|j| j.get("port").and_then(|p| p.as_u64()));
                            req.respond(json(&serde_json::json!({ "user": port(Role::User), "hub": port(Role::Hub) })))
                        }
                        (Method::Get, "/state") => req.respond(json(&v.state())),
                        (Method::Post, "/cmd") => {
                            let b = body(&mut req);
                            let cmd: Cmd = serde_json::from_str(&b).unwrap_or(Cmd { cmd: String::new() });
                            let r = match v.exec(&cmd.cmd) {
                                Ok(output) => CmdResult { ok: true, output },
                                Err(e) => CmdResult { ok: false, output: format!("{e:#}") },
                            };
                            req.respond(json(&r))
                        }
                        _ => req.respond(Response::from_string("not found").with_status_code(404)),
                    };
                }
            }
            None => std::thread::sleep(Duration::from_millis(250)),
        }
    }
}
