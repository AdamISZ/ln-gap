//! Decode an LN-GAP transaction from a kept regtest chain: role (from the
//! datadir's SCENARIO.md), values and fee, and for each script-path input
//! the leaf script with LN-GAP gadgets recognised — including the D43 PoS
//! forms: the plain and tied WOTS verifies per digit, the checksum finale,
//! the equiv leaf's digitwise differ, the EC-OTS tied readout chunks, and
//! the park/unpark runs — and every 20-byte witness arg resolved by
//! forward-hashing (0..=15 steps) to the leaf's WOTS public-key digits,
//! printing the digit index and value; Lamport preimages resolve to their
//! bits as before.
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
    Timelock(String),
    TwoOfTwo { verify: bool },
    Checksig { verify: bool, key4: String },
    /// One WOTS digit's chain verification (49 opcodes). `tied`: Some(true)
    /// for a message digit (its value PICKed off the register file),
    /// Some(false) for a checksum digit (declared value ROLLed up with the
    /// hash); None for the plain form (both ride the witness).
    WotsStep { pk: [u8; 20], tied: Option<bool> },
    /// The checksum finale closing a verify block.
    WotsFinale { msg: usize, ck: usize },
    /// The equiv leaf's digitwise differ (D43): OP_VERIFY that some digit
    /// differs, then the two vectors dropped.
    Differ { m: usize },
    /// An EC-OTS tied-readout chunk: the parked digit off the altstack, the
    /// 16 anticipation points, the 15-v select, CHECKSIGVERIFY.
    ReadoutChunk { point4: String },
    Park { n: usize },
    Unpark { n: usize },
    DropRun { n: usize },
    Drop2Run { pairs: usize },
    Other(String),
}

/// The parsed leaf: the gadget stream and the WOTS verify blocks (a run of
/// per-digit steps closed by a checksum finale), each block carrying its pk
/// digits in SCRIPT order (the verify checks the last digit first, so block
/// digits are descending) — the witness resolver indexes into these.
struct Parsed {
    gadgets: Vec<Gadget>,
    /// (message digits, checksum digits, pk digits in script order)
    blocks: Vec<(usize, usize, Vec<[u8; 20]>)>,
}

fn hex4(b: &[u8]) -> String {
    hex::encode(&b[..4.min(b.len())])
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
    let parsed = parse_gadgets(script);
    println!("  leaf:");
    for g in &parsed.gadgets {
        match g {
            Gadget::BitDecode { h0, h1, dropped } => println!("    bit_decode(h0={}.., h1={}..){}", hex::encode(&h0[..4]), hex::encode(&h1[..4]), if *dropped { " DROP" } else { "" }),
            Gadget::ExpectBit { h } => println!("    expect_bit({}..)", hex::encode(&h[..4])),
            Gadget::Timelock(s) => println!("    {s}"),
            Gadget::TwoOfTwo { verify } => println!("    2-of-2 (user.payment, hub.payment){}", if *verify { " VERIFY" } else { "" }),
            Gadget::Checksig { verify, key4 } => println!("    {} <{key4}..>", if *verify { "CHECKSIGVERIFY" } else { "CHECKSIG" }),
            Gadget::WotsStep { pk, tied } => {
                let form = match tied {
                    Some(true) => ", value PICKed off the register file",
                    Some(false) => ", checksum digit's declared value ROLLed up",
                    None => "",
                };
                println!("    wots digit verify{form} (chain to pk digit {}..)", hex::encode(&pk[..4]));
            }
            Gadget::WotsFinale { msg, ck } => println!("    wots checksum finale: {msg} message + {ck} checksum digits — the verify of a {}-digit key ends here", msg + ck),
            Gadget::Differ { m } => println!("    digitwise differ over {m} digit pairs; OP_VERIFY: some digit must differ; the two vectors dropped"),
            Gadget::ReadoutChunk { point4 } => println!("    EC-OTS readout chunk: parked digit off the altstack, 16 anticipation points ({point4}..), the 15-v select, CHECKSIGVERIFY"),
            Gadget::Park { n } => println!("    park {n} elements to the altstack"),
            Gadget::Unpark { n } => println!("    unpark {n} elements from the altstack"),
            Gadget::DropRun { n } => println!("    drop {n} elements"),
            Gadget::Drop2Run { pairs } => println!("    drop {} elements (2DROP x{pairs})", pairs * 2),
            Gadget::Other(s) => println!("    {s}"),
        }
    }
    if !parsed.blocks.is_empty() {
        println!("  wots verify blocks (script order; each verify's digits descend):");
        for (b, (msg, ck, digits)) in parsed.blocks.iter().enumerate() {
            println!("    block #{b}: {msg} message + {ck} checksum digits, pk {}.. ..{}", hex4(&digits[0]), hex::encode(&digits[digits.len() - 1][..4]));
        }
    }
    // resolve every 20-byte arg against the leaf's hashes: the Lamport
    // gadgets' bit commitments, and every WOTS pk digit by forward-hashing
    let mut by_hash: HashMap<[u8; 20], (usize, bool)> = HashMap::new();
    let mut k = 0;
    for g in &parsed.gadgets {
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
    let mut prev_small: Option<i64> = None;
    for (pos, it) in items[..n_args].iter().enumerate().rev() {
        let idx = n_args - 1 - pos;
        if it.len() == 64 {
            println!("    [{idx}] signature {}..", hex::encode(&it[..8]));
            prev_small = None;
        } else if it.len() == 20 {
            if let Some((g, bit)) = by_hash.get(&hash160(it)) {
                println!("    [{idx}] preimage {}.. -> gadget {g} bit {}", hex::encode(&it[..4]), u8::from(*bit));
                bits.push((*g, *bit));
            } else if let Some((b, digit, v)) = resolve_wots(&parsed.blocks, it) {
                let check = match prev_small {
                    Some(d) if d == v => format!(" (the declared digit beside it: {d} ✓)"),
                    Some(d) => format!(" (the declared digit beside it: {d} ✗ MISMATCH)"),
                    None => String::new(),
                };
                println!("    [{idx}] wots reveal {}.. -> block #{b} digit {digit} = {v}{check}", hex::encode(&it[..4]));
            } else {
                println!("    [{idx}] 20 bytes {}.. (opens no hash in this leaf)", hex::encode(&it[..4]));
            }
            prev_small = None;
        } else if it.len() <= 4 {
            let v = bitcoin::script::read_scriptint(it).unwrap_or(0);
            println!("    [{idx}] script number {v}");
            prev_small = Some(v);
        } else if it.len() == 32 {
            println!("    [{idx}] 32 bytes {}.. (a revocation secret?)", hex::encode(&it[..4]));
            prev_small = None;
        } else {
            println!("    [{idx}] {} bytes {}", it.len(), hex::encode(it));
            prev_small = None;
        }
    }
    if !bits.is_empty() {
        // group consecutive gadgets of the same kind into runs; bits are msb-first
        let kinds: Vec<bool> = parsed.gadgets.iter().filter_map(|g| match g {
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

/// Forward-hash a 20-byte witness element 0..=15 times; if it lands on a pk
/// digit of one of the leaf's verify blocks, return (block, digit index,
/// digit value). The chain for digit value v reaches the pk digit after
/// 15 - v hashes.
fn resolve_wots(blocks: &[(usize, usize, Vec<[u8; 20]>)], arg: &[u8]) -> Option<(usize, usize, i64)> {
    let mut h: [u8; 20] = arg.try_into().ok()?;
    for k in 0..=15i64 {
        for (b, (msg, ck, digits)) in blocks.iter().enumerate() {
            if let Some(j) = digits.iter().position(|d| *d == h) {
                return Some((b, msg + ck - 1 - j, 15 - k));
            }
        }
        h = hash160(&h);
    }
    None
}

fn parse_gadgets(script: &Script) -> Parsed {
    let ins: Vec<Instruction> = script.instructions().filter_map(Result::ok).collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < ins.len() {
        // the tied verify's per-digit preamble: `<file> ROLL <depth> PICK`
        // (a message digit's value PICKed off the file) or
        // `<file+1> ROLL <file+1> ROLL` (a checksum digit's pair pulled up),
        // then the wots step
        if i + 3 < ins.len()
            && push_num(&ins[i]).is_some()
            && is_op(&ins[i + 1], OP_ROLL)
            && push_num(&ins[i + 2]).is_some()
            && (is_op(&ins[i + 3], OP_PICK) || is_op(&ins[i + 3], OP_ROLL))
        {
            if let Some((n, pk)) = wots_step(&ins, i + 4) {
                out.push(Gadget::WotsStep { pk, tied: Some(is_op(&ins[i + 3], OP_PICK)) });
                i += 4 + n;
                continue;
            }
        }
        if let Some((n, pk)) = wots_step(&ins, i) {
            out.push(Gadget::WotsStep { pk, tied: None });
            i += n;
            continue;
        }
        if let Some((n, msg, ck)) = wots_finale(&ins, i) {
            out.push(Gadget::WotsFinale { msg, ck });
            i += n;
            continue;
        }
        // the equiv leaf's differ (D43): `<m-j> PICK <2m-j+1> PICK SUB
        // 0NOTEQUAL ADD` per digit pair, then OP_VERIFY, then both vectors
        // dropped, then a pushed 1
        if i + 6 < ins.len()
            && push_num(&ins[i]).is_some()
            && is_op(&ins[i + 1], OP_PICK)
            && push_num(&ins[i + 2]).is_some()
            && is_op(&ins[i + 3], OP_PICK)
            && is_op(&ins[i + 4], OP_SUB)
            && is_op(&ins[i + 5], OP_0NOTEQUAL)
            && is_op(&ins[i + 6], OP_ADD)
        {
            let mut m = 0;
            while i + 6 < ins.len()
                && push_num(&ins[i]).is_some()
                && is_op(&ins[i + 1], OP_PICK)
                && push_num(&ins[i + 2]).is_some()
                && is_op(&ins[i + 3], OP_PICK)
                && is_op(&ins[i + 4], OP_SUB)
                && is_op(&ins[i + 5], OP_0NOTEQUAL)
                && is_op(&ins[i + 6], OP_ADD)
            {
                m += 1;
                i += 7;
            }
            if m >= 3 && i < ins.len() && is_op(&ins[i], OP_VERIFY) {
                i += 1;
                let mut pairs = 0;
                while i < ins.len() && is_op(&ins[i], OP_2DROP) {
                    pairs += 1;
                    i += 1;
                }
                if pairs == m && i < ins.len() && push_num(&ins[i]) == Some(1) {
                    i += 1;
                }
                out.push(Gadget::Differ { m });
                continue;
            } else {
                // not the differ after all — re-examine the head as Other
                i -= m * 7;
                out.push(Gadget::Other(match &ins[i] {
                    Instruction::Op(o) => format!("{o:?}"),
                    Instruction::PushBytes(p) => push_label(p),
                    Instruction::Op(o) => format!("{o:?}"),
                }));
                i += 1;
                continue;
            }
        }
        // an EC-OTS tied-readout chunk (36 instructions)
        if i + 35 < ins.len()
            && is_op(&ins[i], OP_FROMALTSTACK)
            && (1..=16).all(|j| push32(&ins[i + j]))
            && is_op(&ins[i + 17], OP_PUSHNUM_16)
            && is_op(&ins[i + 18], OP_PICK)
            && is_op(&ins[i + 19], OP_PUSHNUM_15)
            && is_op(&ins[i + 20], OP_SWAP)
            && is_op(&ins[i + 21], OP_SUB)
            && is_op(&ins[i + 22], OP_PICK)
            && push_num(&ins[i + 23]) == Some(18)
            && is_op(&ins[i + 24], OP_ROLL)
            && is_op(&ins[i + 25], OP_SWAP)
            && is_op(&ins[i + 26], OP_CHECKSIGVERIFY)
            && (0..8).all(|j| is_op(&ins[i + 27 + j], OP_2DROP))
            && is_op(&ins[i + 35], OP_DROP)
        {
            let Instruction::PushBytes(p) = &ins[i + 1] else { unreachable!() };
            out.push(Gadget::ReadoutChunk { point4: hex::encode(&p.as_bytes()[..4]) });
            i += 36;
            continue;
        }
        // park/unpark/drop runs
        let run = |op: bitcoin::opcodes::Opcode| {
            let mut n = 0;
            while i + n < ins.len() && is_op(&ins[i + n], op) {
                n += 1;
            }
            n
        };
        let n = run(OP_TOALTSTACK);
        if n >= 3 {
            out.push(Gadget::Park { n });
            i += n;
            continue;
        }
        let n = run(OP_FROMALTSTACK);
        if n >= 3 {
            out.push(Gadget::Unpark { n });
            i += n;
            continue;
        }
        let n = run(OP_2DROP);
        if n >= 2 {
            out.push(Gadget::Drop2Run { pairs: n });
            i += n;
            continue;
        }
        let n = run(OP_DROP);
        if n >= 3 {
            out.push(Gadget::DropRun { n });
            i += n;
            continue;
        }
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
            let n = push_num(&ins[i]).unwrap_or(-1);
            out.push(Gadget::Timelock(format!("{} {n}", if is_op(&ins[i + 1], OP_CSV) { "CSV (relative)" } else { "CLTV (absolute height)" })));
            i += 3;
            continue;
        }
        // <A> OP_CHECKSIG <B> OP_CHECKSIGADD 2 OP_NUMEQUAL[VERIFY]
        if i + 5 < ins.len() && matches!(&ins[i], Instruction::PushBytes(p) if p.len() == 32) && is_op(&ins[i + 1], OP_CHECKSIG) && is_op(&ins[i + 3], OP_CHECKSIGADD) {
            let verify = is_op(&ins[i + 5], OP_NUMEQUALVERIFY);
            out.push(Gadget::TwoOfTwo { verify });
            i += 6;
            continue;
        }
        // <key> OP_CHECKSIG[VERIFY]
        if i + 1 < ins.len() && matches!(&ins[i], Instruction::PushBytes(p) if p.len() == 32) && (is_op(&ins[i + 1], OP_CHECKSIG) || is_op(&ins[i + 1], OP_CHECKSIGVERIFY)) {
            let Instruction::PushBytes(p) = &ins[i] else { unreachable!() };
            out.push(Gadget::Checksig { verify: is_op(&ins[i + 1], OP_CHECKSIGVERIFY), key4: hex::encode(&p.as_bytes()[..4]) });
            i += 2;
            continue;
        }
        out.push(Gadget::Other(match &ins[i] {
            Instruction::Op(o) => format!("{o:?}"),
            Instruction::PushBytes(p) => push_label(p),
            Instruction::Op(o) => format!("{o:?}"),
        }));
        i += 1;
    }
    // group per-digit steps into verify blocks, closed by their finale
    let mut blocks: Vec<(usize, usize, Vec<[u8; 20]>)> = Vec::new();
    let mut cur: Vec<[u8; 20]> = Vec::new();
    for g in &out {
        match g {
            Gadget::WotsStep { pk, .. } => cur.push(*pk),
            Gadget::WotsFinale { msg, ck } => {
                blocks.push((*msg, *ck, std::mem::take(&mut cur)));
            }
            _ => {}
        }
    }
    Parsed { gadgets: out, blocks }
}

/// One WOTS digit's chain verification (winternitz.rs's wots_step): 49
/// instructions consuming `[hash, digit]`. Returns (consumed, pk digit).
fn wots_step(ins: &[Instruction], i: usize) -> Option<(usize, [u8; 20])> {
    if i + 48 >= ins.len() {
        return None;
    }
    if !(is_op(&ins[i], OP_SWAP)
        && is_op(&ins[i + 1], OP_SIZE)
        && push_num(&ins[i + 2]) == Some(20)
        && is_op(&ins[i + 3], OP_EQUALVERIFY)
        && is_op(&ins[i + 4], OP_SWAP)
        && is_op(&ins[i + 5], OP_PUSHNUM_15)
        && is_op(&ins[i + 6], OP_MIN)
        && is_op(&ins[i + 7], OP_DUP)
        && is_op(&ins[i + 8], OP_TOALTSTACK)
        && is_op(&ins[i + 9], OP_PUSHNUM_8)
        && is_op(&ins[i + 10], OP_2DUP)
        && is_op(&ins[i + 11], OP_LESSTHAN)
        && is_op(&ins[i + 12], OP_IF)
        && is_op(&ins[i + 13], OP_DROP)
        && is_op(&ins[i + 14], OP_TOALTSTACK))
    {
        return None;
    }
    if !(0..8).all(|j| is_op(&ins[i + 15 + j], OP_HASH160)) {
        return None;
    }
    if !(is_op(&ins[i + 23], OP_ELSE) && is_op(&ins[i + 24], OP_SUB) && is_op(&ins[i + 25], OP_TOALTSTACK) && is_op(&ins[i + 26], OP_ENDIF)) {
        return None;
    }
    if !(0..7).all(|j| is_op(&ins[i + 27 + 2 * j], OP_DUP) && is_op(&ins[i + 28 + 2 * j], OP_HASH160)) {
        return None;
    }
    if !(is_op(&ins[i + 41], OP_FROMALTSTACK) && is_op(&ins[i + 42], OP_PICK)) {
        return None;
    }
    let pk = push20(&ins[i + 43])?;
    if !(is_op(&ins[i + 44], OP_EQUALVERIFY) && (0..4).all(|j| is_op(&ins[i + 45 + j], OP_2DROP))) {
        return None;
    }
    Some((49, pk))
}

/// The checksum finale (winternitz.rs's wots_checksum_finale). Returns
/// (consumed, message digits, checksum digits).
fn wots_finale(ins: &[Instruction], i: usize) -> Option<(usize, usize, usize)> {
    if !(i + 6 < ins.len() && is_op(&ins[i], OP_FROMALTSTACK) && is_op(&ins[i + 1], OP_DUP) && is_op(&ins[i + 2], OP_NEGATE)) {
        return None;
    }
    let mut j = i + 3;
    let mut k1 = 0;
    while j + 2 < ins.len() && is_op(&ins[j], OP_FROMALTSTACK) && is_op(&ins[j + 1], OP_TUCK) && is_op(&ins[j + 2], OP_SUB) {
        k1 += 1;
        j += 3;
    }
    let msg = k1 + 1;
    if !(j + 2 < ins.len() && push_num(&ins[j]) == Some(15 * msg as i64) && is_op(&ins[j + 1], OP_ADD) && is_op(&ins[j + 2], OP_FROMALTSTACK)) {
        return None;
    }
    j += 3;
    let mut k2 = 0;
    while j + 9 < ins.len()
        && (0..4).all(|t| is_op(&ins[j + 2 * t], OP_DUP) && is_op(&ins[j + 2 * t + 1], OP_ADD))
        && is_op(&ins[j + 8], OP_FROMALTSTACK)
        && is_op(&ins[j + 9], OP_ADD)
    {
        k2 += 1;
        j += 10;
    }
    if !(j < ins.len() && is_op(&ins[j], OP_EQUALVERIFY)) {
        return None;
    }
    Some((j + 1 - i, msg, k2 + 1))
}

fn push20(x: &Instruction) -> Option<[u8; 20]> {
    if let Instruction::PushBytes(p) = x {
        if p.len() == 20 {
            let mut a = [0u8; 20];
            a.copy_from_slice(p.as_bytes());
            return Some(a);
        }
    }
    None
}

fn push32(x: &Instruction) -> bool {
    matches!(x, Instruction::PushBytes(p) if p.len() == 32)
}

/// The script number of a small push (OP_PUSHNUM_N via classify, or the
/// ≤4-byte push).
fn push_num(x: &Instruction) -> Option<i64> {
    match x {
        Instruction::PushBytes(p) if p.len() <= 4 => bitcoin::script::read_scriptint(p.as_bytes()).ok(),
        Instruction::Op(o) => match o.classify(bitcoin::opcodes::ClassifyContext::TapScript) {
            bitcoin::opcodes::Class::PushNum(n) => Some(i64::from(n)),
            _ => None,
        },
        _ => None,
    }
}

fn push_label(p: &bitcoin::script::PushBytes) -> String {
    if p.is_empty() {
        "0".into()
    } else if p.len() <= 4 {
        format!("{}", bitcoin::script::read_scriptint(p.as_bytes()).unwrap_or(0))
    } else {
        format!("<{} bytes {}..>", p.len(), hex::encode(&p.as_bytes()[..4.min(p.len())]))
    }
}

fn is_op(x: &Instruction, op: bitcoin::opcodes::Opcode) -> bool {
    matches!(x, Instruction::Op(o) if *o == op)
}
