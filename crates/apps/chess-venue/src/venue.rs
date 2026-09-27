//! The venue process: the regtest node, the roster, the clock (D55). Mines
//! a Bitcoin block every `block_secs`, independently of the game. Seals
//! each submitted entry on arrival, by the member it is addressed to (the
//! designated sealer, or the mover's fallback), if that member is live and
//! an honest member would seal it: the mover signed it and its due time
//! has not passed. Flags every depth whose due time passes with no signed,
//! timely seal. Funds the contract and registers it (its authorship check,
//! from both players' offers). With `--web` it also serves its page: the
//! depth timeline and the misbehaviour controls (silence a member; seal a
//! late submission; seal an unsigned one as a rogue).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use bitcoin::{Amount, ScriptBuf};
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_pos::instance::{self, Game, GameClock, PosInstance};
use lngap_pos::{Member, PosMiner, Registry};
use tiny_http::{Method, Response, Server};

use crate::store::*;
use crate::web::{body, html, json, DASHBOARD_HTML, VENUE_HTML};

fn members() -> Vec<Member> {
    (0..K as u8).map(|i| Member::new([VENUE_SEED[0] + i; 32])).collect()
}

#[derive(serde::Serialize)]
struct SealView {
    proposer: usize,
    entry: String,
    /// Seconds after t0.
    sealed_at: i64,
    late: bool,
    rogue: bool,
}

#[derive(serde::Serialize)]
struct DepthView {
    depth: u32,
    mover: String,
    /// Seconds after t0.
    due: i64,
    designated: usize,
    seals: Vec<SealView>,
    flags: Option<usize>,
}

#[derive(serde::Serialize)]
struct VenueState {
    height: u32,
    mtp: u32,
    /// Seconds since t0 (negative before move 0's time).
    clock: Option<i64>,
    t0: Option<u32>,
    ell: u32,
    backoff: u32,
    margin: u32,
    block_secs: u64,
    next_block_secs: u64,
    ready: bool,
    n: usize,
    threshold: u32,
    silent: Vec<usize>,
    depths: Vec<DepthView>,
    inbox: Vec<String>,
    late: Vec<String>,
    refused: Vec<String>,
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
    registry: Registry,
    params: VenueParams,
    /// The registered game's clock, once the contract is funded.
    clock: Option<GameClock>,
    ready: bool,
    next_block: Instant,
}

impl Venue {
    fn height(&self) -> u32 {
        self.rt.height().unwrap_or(0)
    }

    /// The seals published for depth `d`, by member.
    fn seals(&self, d: u32) -> BTreeMap<usize, BlockJson> {
        (0..self.miner.n()).filter_map(|i| self.store.read::<BlockJson>(&Store::seal(d, i)).ok().flatten().map(|b| (i, b))).collect()
    }

    /// Whether depth `d` holds a seal an honest member made: signed, timely.
    fn has_honest_seal(&self, d: u32) -> bool {
        self.seals(d).values().any(|b| !b.late && !b.rogue)
    }

    fn state(&self) -> VenueState {
        let now = unix_now();
        let t0 = self.clock.map(|c| c.t0);
        let rel = |t: u32| t0.map(|z| i64::from(t) - i64::from(z)).unwrap_or(0);
        let mut depths = Vec::new();
        if let Some(c) = self.clock {
            for d in 1..=self.params.max_depth {
                let seals = self.seals(d);
                let flags = self.store.read::<FlagsJson>(&Store::flags(d)).ok().flatten().map(|f| f.iter().filter(|x| x.is_some()).count());
                // the timeline runs to the first move neither sealed, flagged
                // nor yet due
                if seals.is_empty() && flags.is_none() && c.t0 + d * c.ell > now && d > 1 && self.seals(d - 1).is_empty() {
                    break;
                }
                let describe = |b: &BlockJson| format!("an entry of {} bytes (head {}…)", b.entry.len() / 2, &b.header[80..96]);
                depths.push(DepthView {
                    depth: d,
                    mover: instance::mover_at(d).name().into(),
                    due: rel(c.t0 + d * c.ell),
                    designated: lngap_pos::rotation(CONTRACT_ID, d, self.miner.n()),
                    seals: seals.values().map(|b| SealView { proposer: b.proposer, entry: describe(b), sealed_at: rel(b.sealed_at), late: b.late, rogue: b.rogue }).collect(),
                    flags,
                });
            }
        }
        let names = |dir: &str| -> Vec<String> {
            self.store.list(dir).unwrap_or_default().iter().filter_map(|p| std::fs::read_to_string(p).ok()).filter_map(|s| serde_json::from_str::<InboxEntry>(&s).ok()).map(|e| format!("{}'s move {} (to member {})", e.from, e.depth, e.to)).collect()
        };
        VenueState {
            height: self.height(),
            mtp: self.rt.mtp().unwrap_or(0),
            clock: t0.map(|z| i64::from(now) - i64::from(z)),
            t0,
            ell: self.params.ell,
            backoff: self.params.backoff,
            margin: self.params.margin,
            block_secs: self.params.block_secs,
            next_block_secs: self.next_block.saturating_duration_since(Instant::now()).as_secs(),
            ready: self.ready,
            n: self.miner.n(),
            threshold: self.registry.threshold,
            silent: (0..self.miner.n()).filter(|i| self.miner.is_silent(*i)).collect(),
            depths,
            inbox: names(Store::inbox_dir()),
            late: names(Store::late_dir()),
            refused: names(Store::refused_dir()),
        }
    }

    /// Move a submission file into `dir` (a queue for the misbehaviour
    /// controls).
    fn park(&self, p: &Path, dir: &str) -> Result<()> {
        let dest = self.store.dir.join(dir);
        std::fs::create_dir_all(&dest)?;
        std::fs::rename(p, dest.join(p.file_name().ok_or_else(|| anyhow!("no file name"))?))?;
        Ok(())
    }

    /// Every submission in the inbox: the addressed member seals it if it
    /// is live and an honest member would (signed, timely); a late one is
    /// held for the late control, an unsigned one for the rogue control.
    fn process_inbox(&mut self) -> Result<()> {
        let Some(clock) = self.clock else { return Ok(()) };
        for p in self.store.list(Store::inbox_dir())? {
            let Some(e) = std::fs::read_to_string(&p).ok().and_then(|s| serde_json::from_str::<InboxEntry>(&s).ok()) else {
                continue;
            };
            let d = e.depth;
            if self.miner.is_silent(e.to) {
                println!("venue: {}'s move {d} was sent to member {}, which is SILENT: no seal (the mover falls back after the backoff)", e.from, e.to);
                self.store.remove(&p);
                continue;
            }
            let now = unix_now();
            let due = clock.t0 + d * clock.ell;
            if now > due {
                println!("venue: {}'s move {d} reached member {} at t+{}s, after its due time t+{}s: an honest member does not seal it (held for the LATE control)", e.from, e.to, i64::from(now) - i64::from(clock.t0), due - clock.t0);
                self.park(&p, Store::late_dir())?;
                continue;
            }
            let entry = hex::decode(&e.entry)?;
            match self.miner.seal_entry(CONTRACT_ID, d, e.to, &entry) {
                Ok(block) => {
                    let already = self.seals(d).values().any(|b| b.header == BlockJson::from_block(&block, now, false, false).header);
                    self.store.write(&Store::seal(d, e.to), &BlockJson::from_block(&block, now, false, false))?;
                    println!("venue: t+{}s: member {} seals {}'s move {d} on submission{}", i64::from(now) - i64::from(clock.t0), e.to, e.from, if already { " (the same head another member already sealed: the same attestation)" } else { "" });
                    self.store.remove(&p);
                }
                Err(err) => {
                    println!("venue: member {} refuses {}'s move {d}: {err} (held for the ROGUE control)", e.to, e.from);
                    self.park(&p, Store::refused_dir())?;
                }
            }
        }
        Ok(())
    }

    /// Flag every owed depth whose due time has passed with no honest seal
    /// (owed: the depth after the deepest honestly sealed one, and below).
    fn deadlines(&mut self) -> Result<()> {
        let Some(clock) = self.clock else { return Ok(()) };
        let now = unix_now();
        let deepest = (1..=self.params.max_depth).filter(|d| self.has_honest_seal(*d)).max().unwrap_or(0);
        for d in 1..=(deepest + 1).min(self.params.max_depth) {
            if self.store.exists(&Store::flags(d)) || now <= clock.t0 + d * clock.ell || self.has_honest_seal(d) {
                continue;
            }
            let f = self.miner.flag(CONTRACT_ID, d);
            self.store.write(&Store::flags(d), &flags_to_json(&f))?;
            println!("venue: t+{}s: move {d} (due t+{}s) has no signed seal — {} of {} members flag it", i64::from(now) - i64::from(clock.t0), d * clock.ell, f.iter().filter(|x| x.is_some()).count(), self.miner.n());
        }
        Ok(())
    }

    /// Take a held submission for depth `d` (any depth if `None`) from
    /// `dir`.
    fn take_held(&self, dir: &str, d: Option<u32>) -> Result<InboxEntry> {
        for p in self.store.list(dir)? {
            if let Some(e) = std::fs::read_to_string(&p).ok().and_then(|s| serde_json::from_str::<InboxEntry>(&s).ok()) {
                if d.is_none_or(|d| d == e.depth) {
                    self.store.remove(&p);
                    return Ok(e);
                }
            }
        }
        Err(anyhow!("no held submission{} in {dir}", d.map(|d| format!(" for move {d}")).unwrap_or_default()))
    }

    /// The misbehaviour control: member `by` seals a LATE submission (a
    /// signed move that arrived after its due time) — the D50 fixture.
    fn seal_late(&mut self, d: Option<u32>, by: usize) -> Result<String> {
        anyhow::ensure!(by < self.miner.n(), "no member {by}");
        let e = self.take_held(Store::late_dir(), d)?;
        let block = self.miner.seal_entry(CONTRACT_ID, e.depth, by, &hex::decode(&e.entry)?).map_err(|err| anyhow!(err))?;
        let now = unix_now();
        self.store.write(&Store::seal(e.depth, by), &BlockJson::from_block(&block, now, true, false))?;
        let msg = format!("member {by} seals {}'s move {} LATE (after its due time; the members' flags stand)", e.from, e.depth);
        println!("venue: {msg}");
        Ok(msg)
    }

    /// The misbehaviour control: member `by` seals an entry honest members
    /// refused (not signed by the mover) — provable misbehaviour, inert in
    /// the contract.
    fn seal_rogue(&mut self, d: Option<u32>, by: usize) -> Result<String> {
        anyhow::ensure!(by < self.miner.n(), "no member {by}");
        let e = self.take_held(Store::refused_dir(), d)?;
        let block = self.miner.seal_unchecked(CONTRACT_ID, e.depth, by, &hex::decode(&e.entry)?).map_err(|err| anyhow!(err))?;
        let now = unix_now();
        self.store.write(&Store::seal(e.depth, by), &BlockJson::from_block(&block, now, false, true))?;
        let msg = format!("member {by} (ROGUE) seals {}'s unsigned entry for move {}: attested, provably not the mover's", e.from, e.depth);
        println!("venue: {msg}");
        Ok(msg)
    }

    fn exec(&mut self, cmd: &str) -> Result<String> {
        let parts: Vec<&str> = cmd.split_whitespace().collect();
        let depth = |s: Option<&&str>| -> Result<Option<u32>> { s.filter(|x| **x != "any").map(|x| x.parse::<u32>().map_err(|e| anyhow!("{e}"))).transpose() };
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
            ["late", rest @ ..] => self.seal_late(depth(rest.first())?, rest.get(1).map(|b| b.parse()).transpose()?.unwrap_or(1)),
            ["rogue", rest @ ..] => self.seal_rogue(depth(rest.first())?, rest.get(1).map(|b| b.parse()).transpose()?.unwrap_or(1)),
            ["mine"] => {
                self.next_block = Instant::now();
                Ok("mining at once".into())
            }
            _ => Err(anyhow!("unknown command (silence <i> | wake <i> | late [d|any] [member] | rogue [d|any] [member] | mine)")),
        }
    }

    /// Register the funded contract: its clock, and its authorship check
    /// from both players' offers (the movers' per-depth state keys).
    fn register(&mut self, c: &ContractJson) -> Result<()> {
        let user: Offer = self.store.read(&Store::offer(Role::User))?.ok_or_else(|| anyhow!("no user offer"))?;
        let hub: Offer = self.store.read(&Store::offer(Role::Hub))?.ok_or_else(|| anyhow!("no hub offer"))?;
        let keys = instance::collect_keys(&user.keys, &hub.keys, self.params.max_depth)?;
        let clock = GameClock { t0: c.t0, ell: c.ell, margin: c.margin };
        let inst = PosInstance::new(CONTRACT_ID, Amount::from_sat(c.value), c.deadline, GAME_ID, Game::Chess, clock, keys, self.registry.clone())?;
        self.miner.register(CONTRACT_ID, self.params.max_depth, inst.authorship()).map_err(|e| anyhow!(e))?;
        self.clock = Some(clock);
        Ok(())
    }
}

pub fn run(dir: PathBuf, block_secs: u64, max_depth: u32, web: Option<u16>, timing: crate::Timing) -> Result<()> {
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

    let mut miner = PosMiner::new(VENUE_SEED, members());
    print!("venue: computing the contract's content registry for depths 0..={max_depth} ({} tables)... ", max_depth + 1);
    let t = Instant::now();
    let registry = miner.registry(CONTRACT_ID, max_depth)?;
    println!("{:.1}s", t.elapsed().as_secs_f64());
    store.write(Store::registry(), &registry)?;
    let n = registry.n();
    let threshold = registry.threshold;
    println!("venue: {n} members sharing one content key, flag threshold {threshold} of {n} (the majority); the designated sealer of a move is the rotation, any member may seal");
    let params = VenueParams { block_secs, n, threshold, max_depth, ell: timing.ell, backoff: timing.backoff, margin: timing.margin, start_secs: timing.start_secs };
    store.write(Store::params(), &params)?;
    println!("venue: a move every {}s (the mover falls back after {}s); claims {}s after a move's due time; Bitcoin blocks every {block_secs}s, independently", timing.ell, timing.backoff, timing.margin);
    let server = match web {
        Some(port) => {
            let s = Server::http(("127.0.0.1", port)).map_err(|e| anyhow!("binding 127.0.0.1:{port}: {e}"))?;
            println!("venue: browse http://127.0.0.1:{port} (the dashboard at /dashboard once the players are up)");
            Some(s)
        }
        None => None,
    };
    let mut v = Venue { store, rt, miner, registry, params, clock: None, ready: false, next_block: Instant::now() + Duration::from_secs(block_secs) };
    println!("venue: waiting for the players' contract (both `play` processes must be up)...");

    // phase 1: fund and register the contract when proposed; phase 2: wait
    // for both players to be ready; throughout: mine on the block clock,
    // seal submissions, flag deadlines, serve requests.
    let mut funded = false;
    loop {
        if !funded {
            if let Some(c) = v.store.read::<ContractJson>(Store::contract())? {
                let spk = ScriptBuf::from_bytes(hex::decode(&c.spk)?);
                let (op, prev) = v.rt.fund(&spk, Amount::from_sat(c.value))?;
                let h = v.rt.height()?;
                v.store.write(Store::funded(), &FundedJson { txid: op.txid.to_string(), vout: op.vout, value: prev.value.to_sat(), spk: c.spk.clone(), height: h })?;
                v.register(&c)?;
                println!("venue: funded the contract output {}:{} with {} sat at height {h}; registered it (move 1 due {}s from now); waiting for both players to finish signing...", op.txid, op.vout, c.value, i64::from(c.t0 + c.ell) - i64::from(unix_now()));
                funded = true;
            }
        } else if !v.ready && v.store.exists(&Store::ready(Role::User)) && v.store.exists(&Store::ready(Role::Hub)) {
            v.ready = true;
            println!("venue: both ready. Ctrl-C stops the node.");
        }
        if funded {
            v.process_inbox()?;
            v.deadlines()?;
        }
        if Instant::now() >= v.next_block {
            v.next_block = Instant::now() + Duration::from_secs(block_secs);
            v.rt.mine(1)?;
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
