//! Dump the fact-chain block structure: headers, hashes, entries.
//! This shows exactly what's in each block for inspection.

use anyhow::Result;
use lngap_factchain::{ChainClient, Miner, DIFFICULTY_BITS, HEADER_BYTES};
use lngap_n4bit::{hash, DIGEST_BYTES};

#[test]
fn dump_fact_chain_blocks() -> Result<()> {
    let g = lngap_factchain::genesis();
    let mut miner = Miner::new(g.header.digest(), 0);
    let mut client = ChainClient::from_checkpoint(0, g.header.digest());

    // Mine 5 blocks with identifiable entries
    let entries: Vec<Vec<u8>> = (0..5u32)
        .map(|i| {
            let mut e = vec![0u8; 64];
            e[0..4].copy_from_slice(&(i + 1).to_le_bytes()); // entry ID
            e[4..8].copy_from_slice(&0xAABBCCDDu32.to_le_bytes()); // marker
            e
        })
        .collect();

    println!("\n{}", "=".repeat(72));
    println!("FACT CHAIN BLOCK DUMP (5 blocks + genesis)");
    println!("{}", "=".repeat(72));
    println!("Header format: {} bytes", HEADER_BYTES);
    println!("  prev:    {} bytes (160-bit n4bit digest of parent header)", DIGEST_BYTES);
    println!("  root:    {} bytes (160-bit n4bit hash of the entry)", DIGEST_BYTES);
    println!("  height:  4 bytes (u32 little-endian)");
    println!("  nonce:   4 bytes (u32 little-endian, PoW)");
    println!("Difficulty: {} leading zero bits (target: {})", DIFFICULTY_BITS, hex::encode(lngap_factchain::pow_target()));
    println!();

    // Genesis block
    println!("--- Genesis (height 0) ---");
    print_block(&g.header, &g.entry, Some("empty (genesis)"));

    // Mine 5 blocks
    for (i, entry) in entries.iter().enumerate() {
        miner.submit(entry.clone());
        let block = miner.mine_next().expect("mine");
        client.verify_and_append(&block).map_err(|e| anyhow::anyhow!(e))?;

        let entry_desc = match i {
            0 => "commit: alice commits to name 'alice'",
            1 => "reveal: alice reveals name + pubkey + salt",
            2 => "transfer: alice -> bob, valid until h_sale",
            3 => "commit: bob commits to name 'bob'",
            _ => "generic entry",
        };
        println!("--- Block {} (height {}) ---", i + 1, block.header.height());
        print_block(&block.header, &block.entry, Some(entry_desc));
    }

    // Verify the chain
    println!("\n--- Chain verification ---");
    println!("  genesis digest: {}", hex::encode(g.header.digest()));
    println!("  tip digest:     {}", hex::encode(client.tip()));
    println!("  tip height:     {}", client.tip_height());
    println!("  chain length:   {} headers (excluding checkpoint)", client.chain_length());

    // Show how a proof would reference these blocks
    println!("\n--- Inclusion proof example ---");
    let shape = lngap_factchain::FactShape {
        checkpoint: g.header.digest(),
        difficulty_bits: DIFFICULTY_BITS,
        n_headers: 3, // prove inclusion of entry at height 3
    };
    let data = shape.build_data(&client, &entries[2]);
    println!("  Claim: from checkpoint (height 0), 3 headers reach the block");
    println!("  containing the transfer entry");
    println!("  Headers in proof: {}", data.headers.len());
    for (i, h) in data.headers.iter().enumerate() {
        println!("    header[{}]: height={}, digest={}", i, h.height(), hex::encode(h.digest()));
    }
    println!("  Entry: {} bytes, hash={}", data.entry.len(), hex::encode(hash(&data.entry)));
    println!("  Last header root: {}", hex::encode(data.headers.last().unwrap().root()));
    println!("  Root == hash(entry)? {}", data.headers.last().unwrap().root() == hash(&data.entry));
    shape.verify_data(&data).map_err(|e| anyhow::anyhow!(e))?;
    println!("  Verification: PASS");

    println!("\n{}", "=".repeat(72));
    Ok(())
}

fn print_block(header: &lngap_factchain::Header, entry: &[u8], desc: Option<&str>) {
    let digest = header.digest();
    println!("  header ({} bytes): {}", HEADER_BYTES, hex::encode(header.as_bytes()));
    println!("    prev:    {} (20 bytes)", hex::encode(header.prev()));
    println!("    root:    {} (20 bytes)", hex::encode(header.root()));
    println!("    height:  {}", header.height());
    println!("    nonce:   {} (found by PoW search)", header.nonce());
    println!("    digest:  {} (n4bit hash of header)", hex::encode(digest));
    println!("    meets PoW: {} ({} <= target {})",
        header.meets_pow(),
        hex::encode(&digest[..3]),
        hex::encode(&lngap_factchain::pow_target()[..3]),
    );
    if entry.is_empty() {
        println!("  entry: (empty — genesis block)");
    } else {
        println!("  entry ({} bytes): {}", entry.len(), hex::encode(entry));
        println!("    entry hash: {} (n4bit hash of entry == root)", hex::encode(hash(entry)));
        if let Some(d) = desc {
            println!("    content: {}", d);
        }
        // Show the first 8 bytes as little-endian u32s for human inspection
        let id = u32::from_le_bytes(entry[0..4].try_into().unwrap());
        let marker = u32::from_le_bytes(entry[4..8].try_into().unwrap());
        println!("    entry[0..4] as u32: {} (entry ID)", id);
        println!("    entry[4..8] as u32: 0x{:08X} (marker)", marker);
    }
    println!();
}
