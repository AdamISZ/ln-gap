//! The venue process: the regtest node, the roster, the clock. Mines one
//! block every `block_secs`, seals one venue slot per block from the
//! inbox, publishes blocks and deadline flags, funds the contract.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use bitcoin::{Amount, ScriptBuf};
use lngap_btc::regtest::Regtest;
use lngap_ec_wots::Attester;
use lngap_pos::{genesis, Member, PosMiner};

use crate::store::*;

fn members() -> Vec<Member> {
    (0..K as u8).map(|i| Member::new([VENUE_SEED[0] + i; 32])).collect()
}

pub fn run(dir: PathBuf, block_secs: u64, max_depth: u32) -> Result<()> {
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

    // the roster and its registry: enough slots for the game and its
    // disputes (a chess dispute waits tens of blocks)
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
    // the slot clock is announced BEFORE funding: the contract's claim
    // leaves commit to it (their CLTVs), so the players need it to build
    // the output; funding mines exactly one block, at height b0
    let b0 = rt.height()? + 1;
    store.write(Store::params(), &VenueParams { b0, max_slot, block_secs, n, threshold, max_depth })?;
    println!("venue: the contract will be funded at height {b0}; slot s seals at height {b0} + s");
    println!("venue: waiting for the players' contract (both `play` processes must be up)...");

    // the contract: funded once the players agree it
    let funded = loop {
        if let Some(c) = store.read::<ContractJson>(Store::contract())? {
            let spk = ScriptBuf::from_bytes(hex::decode(&c.spk)?);
            let (op, prev) = rt.fund(&spk, Amount::from_sat(c.value))?;
            let h = rt.height()?;
            let f = FundedJson { txid: op.txid.to_string(), vout: op.vout, value: prev.value.to_sat(), spk: c.spk.clone(), height: h };
            store.write(Store::funded(), &f)?;
            println!("venue: funded the contract output {}:{} with {} sat at height {h}", op.txid, op.vout, c.value);
            break f;
        }
        std::thread::sleep(Duration::from_millis(500));
    };
    anyhow::ensure!(funded.height == b0, "funding landed at height {} instead of {b0}", funded.height);
    println!("venue: waiting for both players to finish signing the graph...");
    while !(store.exists(&Store::ready(lngap_channel::Role::User)) && store.exists(&Store::ready(lngap_channel::Role::Hub))) {
        std::thread::sleep(Duration::from_millis(500));
    }
    println!("venue: both ready. Slot 1 seals at height {} in {block_secs}s; one block every {block_secs}s. Ctrl-C stops the node.", b0 + 1);

    // the clock: one block per tick, one slot per block
    let mut next = Instant::now() + Duration::from_secs(block_secs);
    loop {
        // pick up entries as they arrive, so a player's move is in the
        // queue when the tick comes
        let now = Instant::now();
        if now < next {
            std::thread::sleep((next - now).min(Duration::from_millis(250)));
            continue;
        }
        next += Duration::from_secs(block_secs);
        rt.mine(1)?;
        let h = rt.height()?;
        let slot = h - b0;
        if slot > max_slot {
            println!("venue: height {h}: beyond the registry (slot {slot} > {max_slot}); mining on without sealing");
            continue;
        }
        // the inbox: the oldest entry seals in this slot (one per block)
        let inbox = store.list(Store::inbox_dir())?;
        let mut from = None;
        if let Some(p) = inbox.first() {
            if let Ok(e) = serde_json::from_str::<InboxEntry>(&std::fs::read_to_string(p)?) {
                miner.submit(hex::decode(&e.entry)?);
                from = Some(e.from);
            }
            store.remove(p);
        }
        let (block, _table) = miner.seal_next(slot).map_err(|e| anyhow!(e))?;
        store.write(&Store::block(slot), &BlockJson::from_block(&block))?;
        match from {
            Some(f) => println!("venue: height {h}: slot {slot} sealed by member {} with {f}'s entry ({} bytes)", block.proposer, block.entry.len()),
            None => println!("venue: height {h}: slot {slot} sealed EMPTY by member {}", block.proposer),
        }
        // deadlines: every slot whose deadline (height > b0 + s) has now
        // passed with no entry is flagged by every member
        for s in 1..slot {
            if store.exists(&Store::flags(s)) {
                continue;
            }
            let empty = store.read::<BlockJson>(&Store::block(s))?.map(|b| b.entry.is_empty()).unwrap_or(true);
            if empty {
                let f = miner.flag(s);
                store.write(&Store::flags(s), &flags_to_json(&f))?;
                println!("venue: height {h}: slot {s} passed its deadline empty — {} of {n} members flag it", f.iter().filter(|x| x.is_some()).count());
            }
        }
    }
}
