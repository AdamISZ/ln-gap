//! Decode an LN-GAP transaction from a kept regtest chain: role (from the
//! datadir's SCENARIO.md), values and fee, and for each script-path input
//! the leaf script with LN-GAP gadgets recognised and every Lamport
//! preimage resolved to the bit it commits to.
//!
//! Usage: cargo run -p lngap-harness --bin decode -- <datadir> <txid> [--rpcport N]

use std::collections::HashMap;
use std::path::PathBuf;

use anyhow::{anyhow, Context, Result};
use bitcoin::opcodes::all::*;
use bitcoin::script::Instruction;
use bitcoin::{Amount, Script, Transaction, Txid};
use bitcoincore_rpc::{Auth, Client, RpcApi};
use lngap_btc::hash160;

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut port = 18555u16;
    let mut pos = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--rpcport" {
            port = args.get(i + 1).ok_or_else(|| anyhow!("--rpcport needs a value"))?.parse()?;
            i += 2;
        } else {
            pos.push(args[i].clone());
            i += 1;
        }
    }
    let [datadir, txid]: [String; 2] = pos.try_into().map_err(|_| anyhow!("usage: decode <datadir> <txid> [--rpcport N]"))?;
    let datadir = PathBuf::from(datadir);
    let cookie = datadir.join("regtest").join(".cookie");
    let rpc = Client::new(&format!("http://127.0.0.1:{port}"), Auth::CookieFile(cookie)).context("rpc client")?;
    let txid: Txid = txid.parse()?;
    let tx: Transaction = rpc.get_raw_transaction(&txid, None).context("getrawtransaction (is the node up on this port?)")?;
    let roles = scenario_roles(&datadir);

    println!("tx {txid}");
    if let Some(r) = roles.get(&txid.to_string()) {
        println!("role: {r}");
    }
    let mut in_sum = Amount::ZERO;
    for (n, input) in tx.input.iter().enumerate() {
        let prev = rpc.get_raw_transaction(&input.previous_output.txid, None)?;
        let prevout = &prev.output[input.previous_output.vout as usize];
        in_sum += prevout.value;
        let prole = roles.get(&input.previous_output.txid.to_string()).map(|r| format!(" ({r})")).unwrap_or_default();
        println!("\ninput {n}: {}:{}{} worth {} sat, nSequence {:#x}", input.previous_output.txid, input.previous_output.vout, prole, prevout.value.to_sat(), input.sequence.0);
        decode_witness(&input.witness);
    }
    let out_sum: Amount = tx.output.iter().map(|o| o.value).sum();
    println!();
    for (n, o) in tx.output.iter().enumerate() {
        println!("output {n}: {} sat to {}", o.value.to_sat(), bitcoin::Address::from_script(&o.script_pubkey, bitcoin::Network::Regtest).map(|a| a.to_string()).unwrap_or_else(|_| o.script_pubkey.to_hex_string()));
    }
    println!("fee {} sat, nLockTime {}", (in_sum - out_sum).to_sat(), tx.lock_time);
    Ok(())
}

fn scenario_roles(datadir: &std::path::Path) -> HashMap<String, String> {
    let mut m = HashMap::new();
    if let Ok(s) = std::fs::read_to_string(datadir.join("SCENARIO.md")) {
        for line in s.lines().filter(|l| l.starts_with("| ")) {
            let cells: Vec<&str> = line.split('|').map(str::trim).collect();
            if cells.len() >= 5 {
                let role = cells[2].trim_matches('`');
                let txid = cells[4].trim_matches('`');
                if txid.len() == 64 {
                    m.insert(txid.to_string(), format!("{}{}", role, cells[3].is_empty().then_some("").unwrap_or(&format!(" by {}", cells[3]))));
                }
            }
        }
    }
    m
}

/// A recognised piece of an LN-GAP leaf.
enum Gadget {
    BitDecode { h0: [u8; 20], h1: [u8; 20], dropped: bool },
    ExpectBit { h: [u8; 20] },
    Other(String),
}

fn decode_witness(w: &bitcoin::Witness) {
    let items: Vec<&[u8]> = w.iter().collect();
    let Some(ls) = w.taproot_leaf_script() else {
        if items.len() == 1 && items[0].len() == 64 {
            println!("  key-path spend: signature {}", hex::encode(items[0]));
        } else {
            for (i, it) in items.iter().enumerate() {
                println!("  #{i} {} bytes: {}", it.len(), hex::encode(it));
            }
        }
        return;
    };
    let script: &Script = ls.script;
    let control = w.taproot_control_block().unwrap_or(&[]);
    let n_args = items.len() - 2;
    println!("  script path: leaf {} bytes, control block {} bytes (depth {}), {n_args} witness args", script.len(), control.len(), (control.len().saturating_sub(33)) / 32);
    let gadgets = parse_gadgets(script);
    println!("  leaf:");
    for g in &gadgets {
        match g {
            Gadget::BitDecode { h0, h1, dropped } => println!("    bit_decode(h0={}.., h1={}..){}", hex::encode(&h0[..4]), hex::encode(&h1[..4]), if *dropped { " DROP" } else { "" }),
            Gadget::ExpectBit { h } => println!("    expect_bit({}..)", hex::encode(&h[..4])),
            Gadget::Other(s) => println!("    {s}"),
        }
    }
    // resolve every 20-byte arg against the leaf's hashes; args are consumed top (last) first
    let mut by_hash: HashMap<[u8; 20], (usize, bool)> = HashMap::new();
    let mut k = 0;
    for g in &gadgets {
        match g {
            Gadget::BitDecode { h0, h1, .. } => {
                by_hash.insert(*h0, (k, false));
                by_hash.insert(*h1, (k, true));
                k += 1;
            }
            Gadget::ExpectBit { h } => {
                by_hash.insert(*h, (k, true));
                k += 1;
            }
            _ => {}
        }
    }
    println!("  witness args (consumption order, i.e. top of stack first):");
    let mut bits: Vec<(usize, bool)> = Vec::new();
    for (pos, it) in items[..n_args].iter().enumerate().rev() {
        let idx = n_args - 1 - pos;
        if it.len() == 64 {
            println!("    [{idx}] signature {}..", hex::encode(&it[..8]));
        } else if it.len() == 20 {
            match by_hash.get(&hash160(it)) {
                Some((g, bit)) => {
                    println!("    [{idx}] preimage {}.. -> gadget {g} bit {}", hex::encode(&it[..4]), u8::from(*bit));
                    bits.push((*g, *bit));
                }
                None => println!("    [{idx}] 20 bytes {}.. (matches no hash in this leaf)", hex::encode(&it[..4])),
            }
        } else if it.len() == 32 {
            println!("    [{idx}] 32 bytes {}.. (a revocation secret?)", hex::encode(&it[..4]));
        } else {
            println!("    [{idx}] {} bytes {}", it.len(), hex::encode(it));
        }
    }
    if !bits.is_empty() {
        // group consecutive gadgets of the same kind into runs; bits are msb-first
        let kinds: Vec<bool> = gadgets.iter().filter_map(|g| match g {
            Gadget::BitDecode { .. } => Some(true),
            Gadget::ExpectBit { .. } => Some(false),
            _ => None,
        }).collect();
        bits.sort_by_key(|b| b.0);
        let mut runs: Vec<(bool, Vec<bool>)> = Vec::new();
        let mut last: Option<usize> = None;
        for (g, b) in bits {
            if last.is_some_and(|l| l + 1 == g) && runs.last().is_some_and(|r| r.0 == kinds[g]) {
                runs.last_mut().unwrap().1.push(b);
            } else {
                runs.push((kinds[g], vec![b]));
            }
            last = Some(g);
        }
        println!("  decoded commitments (runs of consecutive gadgets, msb first):");
        for (decoded, r) in runs {
            if decoded {
                let s: String = r.iter().map(|b| if *b { '1' } else { '0' }).collect();
                let v = r.iter().fold(0u64, |a, b| (a << 1) | u64::from(*b));
                println!("    {} bits revealed by the prover: {s} = {v}", r.len());
            } else {
                println!("    {} preimages of a fixed statement (expect_bit: a Lamport-signed hub statement), all present", r.len());
            }
        }
    }
}

fn parse_gadgets(script: &Script) -> Vec<Gadget> {
    let ins: Vec<Instruction> = script.instructions().filter_map(Result::ok).collect();
    let mut out = Vec::new();
    let mut i = 0;
    let push20 = |x: &Instruction| -> Option<[u8; 20]> {
        if let Instruction::PushBytes(p) = x {
            if p.len() == 20 {
                let mut a = [0u8; 20];
                a.copy_from_slice(p.as_bytes());
                return Some(a);
            }
        }
        None
    };
    let is_op = |x: &Instruction, op: bitcoin::opcodes::Opcode| matches!(x, Instruction::Op(o) if *o == op);
    while i < ins.len() {
        // OP_HASH160 OP_DUP <h1> OP_EQUAL OP_IF OP_DROP 1 OP_ELSE <h0> OP_EQUALVERIFY 0 OP_ENDIF [OP_DROP]
        if i + 11 < ins.len()
            && is_op(&ins[i], OP_HASH160)
            && is_op(&ins[i + 1], OP_DUP)
            && push20(&ins[i + 2]).is_some()
            && is_op(&ins[i + 3], OP_EQUAL)
            && is_op(&ins[i + 4], OP_IF)
            && is_op(&ins[i + 5], OP_DROP)
            && is_op(&ins[i + 7], OP_ELSE)
            && push20(&ins[i + 8]).is_some()
            && is_op(&ins[i + 9], OP_EQUALVERIFY)
            && is_op(&ins[i + 11], OP_ENDIF)
        {
            let dropped = i + 12 < ins.len() && is_op(&ins[i + 12], OP_DROP);
            out.push(Gadget::BitDecode { h0: push20(&ins[i + 8]).unwrap(), h1: push20(&ins[i + 2]).unwrap(), dropped });
            i += if dropped { 13 } else { 12 };
            continue;
        }
        // OP_HASH160 <h> OP_EQUALVERIFY
        if i + 2 < ins.len() && is_op(&ins[i], OP_HASH160) && push20(&ins[i + 1]).is_some() && is_op(&ins[i + 2], OP_EQUALVERIFY) {
            out.push(Gadget::ExpectBit { h: push20(&ins[i + 1]).unwrap() });
            i += 3;
            continue;
        }
        // <n> OP_CSV OP_DROP / <h> OP_CLTV OP_DROP
        if i + 2 < ins.len() && (is_op(&ins[i + 1], OP_CSV) || is_op(&ins[i + 1], OP_CLTV)) && is_op(&ins[i + 2], OP_DROP) {
            let n = match &ins[i] {
                Instruction::PushBytes(p) => bitcoin::script::read_scriptint(p.as_bytes()).unwrap_or(-1),
                Instruction::Op(o) => match o.classify(bitcoin::opcodes::ClassifyContext::TapScript) {
                    bitcoin::opcodes::Class::PushNum(n) => i64::from(n),
                    _ => -1,
                },
            };
            out.push(Gadget::Other(format!("{} {n}", if is_op(&ins[i + 1], OP_CSV) { "CSV (relative)" } else { "CLTV (absolute height)" })));
            i += 3;
            continue;
        }
        // <A> OP_CHECKSIG <B> OP_CHECKSIGADD 2 OP_NUMEQUAL[VERIFY]
        if i + 5 < ins.len() && matches!(&ins[i], Instruction::PushBytes(p) if p.len() == 32) && is_op(&ins[i + 1], OP_CHECKSIG) && is_op(&ins[i + 3], OP_CHECKSIGADD) {
            let verify = is_op(&ins[i + 5], OP_NUMEQUALVERIFY);
            out.push(Gadget::Other(format!("2-of-2 (user.payment, hub.payment){}", if verify { " VERIFY" } else { "" })));
            i += 6;
            continue;
        }
        // <key> OP_CHECKSIG[VERIFY]
        if i + 1 < ins.len() && matches!(&ins[i], Instruction::PushBytes(p) if p.len() == 32) && (is_op(&ins[i + 1], OP_CHECKSIG) || is_op(&ins[i + 1], OP_CHECKSIGVERIFY)) {
            let Instruction::PushBytes(p) = &ins[i] else { unreachable!() };
            out.push(Gadget::Other(format!("{} <{}..>", if is_op(&ins[i + 1], OP_CHECKSIG) { "CHECKSIG" } else { "CHECKSIGVERIFY" }, hex::encode(&p.as_bytes()[..4]))));
            i += 2;
            continue;
        }
        out.push(Gadget::Other(match &ins[i] {
            Instruction::Op(o) => format!("{o:?}"),
            Instruction::PushBytes(p) => {
                if p.is_empty() { "0".into() } else if p.len() <= 4 { format!("{}", bitcoin::script::read_scriptint(p.as_bytes()).unwrap_or(0)) } else { format!("<{} bytes {}..>", p.len(), hex::encode(&p.as_bytes()[..4.min(p.len())])) }
            }
        }));
        i += 1;
    }
    out
}
