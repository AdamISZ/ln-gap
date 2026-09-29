//! The venue process: the regtest node, the roster, the clock (D55). Mines
//! a Bitcoin block every `block_secs`, independently of the game. For each
//! hand the player requests, computes the venue's registry (the hand is a
//! contract of its own, with its own tables), then registers the hand's
//! check (the movers' state keys and both sides' share commitments, D57)
//! once both offers and the terms are in. Seals each submitted entry on
//! arrival by the member it is addressed to, if an honest member would;
//! flags every due move with no valid seal. Its page shows the latest
//! hand's timeline and the misbehaviour controls. The channel is the
//! parties' own: the venue neither funds nor sees it.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use bitcoin::Amount;
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_pos::instance::{self, Game, GameClock, PosInstance};
use lngap_pos::{Member, PosMiner};
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
    sealed_at: i64,
    late: bool,
    rogue: bool,
}

#[derive(serde::Serialize)]
struct DepthView {
    depth: u32,
    mover: String,
    due: i64,
    designated: usize,
    seals: Vec<SealView>,
    flags: Option<usize>,
}

#[derive(serde::Serialize)]
struct VenueState {
    height: u32,
    mtp: u32,
    clock: Option<i64>,
    t0: Option<u32>,
    hand: Option<u32>,
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
    params: VenueParams,
    /// Registered hands' clocks.
    clocks: BTreeMap<u32, GameClock>,
    next_block: Instant,
}

impl Venue {
    fn height(&self) -> u32 {
        self.rt.height().unwrap_or(0)
    }

    fn latest(&self) -> Option<u32> {
        self.clocks.keys().next_back().copied()
    }

    fn seals(&self, h: u32, d: u32) -> BTreeMap<usize, BlockJson> {
        (0..self.miner.n()).filter_map(|i| self.store.read::<BlockJson>(&Store::seal(h, d, i)).ok().flatten().map(|b| (i, b))).collect()
    }

    fn has_honest_seal(&self, h: u32, d: u32) -> bool {
        self.seals(h, d).values().any(|b| !b.late && !b.rogue)
    }

    fn state(&self) -> VenueState {
        let now = unix_now();
        let hand = self.latest();
        let clock = hand.and_then(|h| self.clocks.get(&h).copied());
        let t0 = clock.map(|c| c.t0);
        let rel = |t: u32| t0.map(|z| i64::from(t) - i64::from(z)).unwrap_or(0);
        let mut depths = Vec::new();
        if let (Some(h), Some(c)) = (hand, clock) {
            for d in 1..=self.params.max_depth {
                let seals = self.seals(h, d);
                let flags = self.store.read::<FlagsJson>(&Store::flags(h, d)).ok().flatten().map(|f| f.iter().filter(|x| x.is_some()).count());
                if seals.is_empty() && flags.is_none() && c.t0 + d * c.ell > now && d > 1 && self.seals(h, d - 1).is_empty() {
                    break;
                }
                depths.push(DepthView {
                    depth: d,
                    mover: side(instance::mover_at(d)).into(),
                    due: rel(c.t0 + d * c.ell),
                    designated: lngap_pos::rotation(h, d, self.miner.n()),
                    seals: seals.values().map(|b| SealView { proposer: b.proposer, entry: format!("an entry of {} bytes", b.entry.len() / 2), sealed_at: rel(b.sealed_at), late: b.late, rogue: b.rogue }).collect(),
                    flags,
                });
            }
        }
        let names = |dir: String| -> Vec<String> {
            self.store.list(&dir).unwrap_or_default().iter().filter_map(|p| std::fs::read_to_string(p).ok()).filter_map(|s| serde_json::from_str::<InboxEntry>(&s).ok()).map(|e| format!("{}'s move {} (to member {})", e.from, e.depth, e.to)).collect()
        };
        VenueState {
            height: self.height(),
            mtp: self.rt.mtp().unwrap_or(0),
            clock: t0.map(|z| i64::from(now) - i64::from(z)),
            t0,
            hand,
            ell: self.params.ell,
            backoff: self.params.backoff,
            margin: self.params.margin,
            block_secs: self.params.block_secs,
            next_block_secs: self.next_block.saturating_duration_since(Instant::now()).as_secs(),
            ready: hand.is_some(),
            n: self.miner.n(),
            threshold: self.params.threshold,
            silent: (0..self.miner.n()).filter(|i| self.miner.is_silent(*i)).collect(),
            depths,
            inbox: hand.map(|h| names(Store::inbox_dir(h))).unwrap_or_default(),
            late: hand.map(|h| names(Store::late_dir(h))).unwrap_or_default(),
            refused: hand.map(|h| names(Store::refused_dir(h))).unwrap_or_default(),
        }
    }

    fn park(&self, p: &Path, dir: &str) -> Result<()> {
        let dest = self.store.dir.join(dir);
        std::fs::create_dir_all(&dest)?;
        std::fs::rename(p, dest.join(p.file_name().ok_or_else(|| anyhow!("no file name"))?))?;
        Ok(())
    }

    /// New hands: the registry on request; the registration once the
    /// offers and the terms are in.
    fn hands(&mut self) -> Result<()> {
        for h in self.store.hands() {
            if self.store.exists(&Store::request(h)) && !self.store.exists(&Store::registry(h)) {
                let t = Instant::now();
                let registry = self.miner.registry(h, self.params.max_depth)?;
                self.store.write(&Store::registry(h), &registry)?;
                println!("venue: hand {h}: its registry ({} tables) in {:.1}s", self.params.max_depth + 1, t.elapsed().as_secs_f64());
            }
            if self.clocks.contains_key(&h) || !self.store.exists(&Store::registry(h)) {
                continue;
            }
            let (Some(user), Some(hub), Some(c)) = (self.store.read::<Offer>(&Store::offer(h, Role::User))?, self.store.read::<Offer>(&Store::offer(h, Role::Hub))?, self.store.read::<ContractJson>(&Store::contract(h))?) else { continue };
            let registry = self.store.read(&Store::registry(h))?.ok_or_else(|| anyhow!("registry"))?;
            let keys = instance::collect_keys(&user.keys, &hub.keys, self.params.max_depth)?;
            let clock = GameClock { t0: c.t0, ell: c.ell, margin: c.margin };
            let inst = PosInstance::new(h, Amount::from_sat(c.value), c.deadline, GAME_ID, Game::Blackjack, clock, keys, registry)?.with_commitments(commitments(&user, &hub)?)?;
            self.miner.register(h, self.params.max_depth, inst.authorship()).map_err(|e| anyhow!(e))?;
            self.clocks.insert(h, clock);
            self.store.write(&Store::registered(h), &serde_json::json!({ "hand": h }))?;
            println!("venue: hand {h} registered (move 1 due {}s from now)", i64::from(c.t0 + c.ell) - i64::from(unix_now()));
        }
        Ok(())
    }

    fn process_inbox(&mut self) -> Result<()> {
        let hands: Vec<(u32, GameClock)> = self.clocks.iter().map(|(h, c)| (*h, *c)).collect();
        for (h, clock) in hands {
            for p in self.store.list(&Store::inbox_dir(h))? {
                let Some(e) = std::fs::read_to_string(&p).ok().and_then(|s| serde_json::from_str::<InboxEntry>(&s).ok()) else { continue };
                let d = e.depth;
                if self.miner.is_silent(e.to) {
                    println!("venue: hand {h}: {}'s move {d} was sent to member {}, which is SILENT", e.from, e.to);
                    self.store.remove(&p);
                    continue;
                }
                let now = unix_now();
                let due = clock.t0 + d * clock.ell;
                if now > due {
                    println!("venue: hand {h}: {}'s move {d} arrived after its due time: held for the LATE control", e.from);
                    self.park(&p, &Store::late_dir(h))?;
                    continue;
                }
                match self.miner.seal_entry(h, d, e.to, &hex::decode(&e.entry)?) {
                    Ok(block) => {
                        self.store.write(&Store::seal(h, d, e.to), &BlockJson::from_block(&block, now, false, false))?;
                        println!("venue: hand {h}: t+{}s: member {} seals {}'s move {d}", i64::from(now) - i64::from(clock.t0), e.to, e.from);
                        self.store.remove(&p);
                    }
                    Err(err) => {
                        println!("venue: hand {h}: member {} refuses {}'s move {d}: not signed, or a declared share does not open (held for the ROGUE control) [{err}]", e.to, e.from);
                        self.park(&p, &Store::refused_dir(h))?;
                    }
                }
            }
        }
        Ok(())
    }

    fn deadlines(&mut self) -> Result<()> {
        let now = unix_now();
        let hands: Vec<(u32, GameClock)> = self.clocks.iter().map(|(h, c)| (*h, *c)).collect();
        for (h, clock) in hands {
            let deepest = (1..=self.params.max_depth).filter(|d| self.has_honest_seal(h, *d)).max().unwrap_or(0);
            for d in 1..=(deepest + 1).min(self.params.max_depth) {
                if self.store.exists(&Store::flags(h, d)) || now <= clock.t0 + d * clock.ell || self.has_honest_seal(h, d) {
                    continue;
                }
                let f = self.miner.flag(h, d);
                self.store.write(&Store::flags(h, d), &flags_to_json(&f))?;
                println!("venue: hand {h}: move {d} has no valid seal at its due time — {} of {} members flag it", f.iter().filter(|x| x.is_some()).count(), self.miner.n());
            }
        }
        Ok(())
    }

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

    fn seal_late(&mut self, d: Option<u32>, by: usize) -> Result<String> {
        let h = self.latest().ok_or_else(|| anyhow!("no hand"))?;
        anyhow::ensure!(by < self.miner.n(), "no member {by}");
        let e = self.take_held(&Store::late_dir(h), d)?;
        let block = self.miner.seal_entry(h, e.depth, by, &hex::decode(&e.entry)?).map_err(|err| anyhow!(err))?;
        self.store.write(&Store::seal(h, e.depth, by), &BlockJson::from_block(&block, unix_now(), true, false))?;
        Ok(format!("member {by} seals {}'s move {} LATE (the members' flags stand)", e.from, e.depth))
    }

    fn seal_rogue(&mut self, d: Option<u32>, by: usize) -> Result<String> {
        let h = self.latest().ok_or_else(|| anyhow!("no hand"))?;
        anyhow::ensure!(by < self.miner.n(), "no member {by}");
        let e = self.take_held(&Store::refused_dir(h), d)?;
        let block = self.miner.seal_unchecked(h, e.depth, by, &hex::decode(&e.entry)?).map_err(|err| anyhow!(err))?;
        self.store.write(&Store::seal(h, e.depth, by), &BlockJson::from_block(&block, unix_now(), false, true))?;
        Ok(format!("member {by} (ROGUE) seals {}'s refused entry for move {}: attested, provably not a valid move", e.from, e.depth))
    }

    fn exec(&mut self, cmd: &str) -> Result<String> {
        let parts: Vec<&str> = cmd.split_whitespace().collect();
        let depth = |s: Option<&&str>| -> Result<Option<u32>> { s.filter(|x| **x != "any").map(|x| x.parse::<u32>().map_err(|e| anyhow!("{e}"))).transpose() };
        match parts.as_slice() {
            ["silence", i] => {
                let i: usize = i.parse()?;
                anyhow::ensure!(i < self.miner.n(), "no member {i}");
                self.miner.silence(i);
                Ok(format!("member {i} is silent"))
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
}

pub fn run(dir: PathBuf, block_secs: u64, max_depth: u32, web: Option<u16>, timing: crate::Timing) -> Result<()> {
    let store = Store::new(dir.clone());
    std::fs::create_dir_all(&dir)?;
    for stale in ["venue", "players", "channel", "hands", "node.json"] {
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
    let miner = PosMiner::new(VENUE_SEED, members());
    let n = miner.n();
    let threshold = (n as u32) / 2 + 1;
    let params = VenueParams { block_secs, n, threshold, max_depth, ell: timing.ell, backoff: timing.backoff, margin: timing.margin, start_secs: timing.start_secs, deposit: timing.deposit, started: unix_now() };
    store.write(Store::params(), &params)?;
    println!("venue: {n} members sharing one content key, flag threshold {threshold}; a move every {}s (fallback after {}s); claims {}s past a due time; Bitcoin blocks every {block_secs}s", timing.ell, timing.backoff, timing.margin);
    let server = match web {
        Some(port) => {
            let s = Server::http(("127.0.0.1", port)).map_err(|e| anyhow!("binding 127.0.0.1:{port}: {e}"))?;
            println!("venue: browse http://127.0.0.1:{port} (the dashboard at /dashboard once the parties are up)");
            Some(s)
        }
        None => None,
    };
    let mut v = Venue { store, rt, miner, params, clocks: BTreeMap::new(), next_block: Instant::now() + Duration::from_secs(block_secs) };
    println!("venue: waiting for hands (the parties open their channel themselves)...");
    loop {
        v.hands()?;
        v.process_inbox()?;
        v.deadlines()?;
        if Instant::now() >= v.next_block {
            v.next_block = Instant::now() + Duration::from_secs(block_secs);
            v.rt.mine(1)?;
        }
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
