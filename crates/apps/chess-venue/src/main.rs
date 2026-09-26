//! `lngap-chess-venue`: an interactive chess game on the PoS venue, played from
//! two terminals against one regtest node, with the roster (five members
//! sharing one content key, majority flags — D50-D53) sealing the moves.
//!
//! Three processes share one directory (`--dir`, default `./chess-venue`):
//!
//! ```text
//!   lngap-chess-venue venue [--dir D] [--block-secs 30]   # the node, the roster, the clock
//!   lngap-chess-venue play user [--dir D]                 # white
//!   lngap-chess-venue play hub  [--dir D]                 # black
//! ```
//!
//! The venue starts a regtest node (datadir `D/node`, kept), mines one
//! block every `--block-secs` seconds, seals one venue slot per block
//! from the entries the players drop in its inbox, publishes every block
//! and every deadline's flags to `D/venue/`, and funds the contract
//! output once both players have agreed it. The players exchange their
//! key offers and their graph signatures through `D/players/` and then
//! drive the game — and its disputes — from a small REPL. Nothing else
//! connects them: a disprover reads the mover's reveal off the confirmed
//! refutation on the chain, as it would in deployment.

mod player;
mod store;
mod venue;

use std::path::PathBuf;

use anyhow::{bail, Result};
use lngap_channel::Role;

fn usage() -> ! {
    eprintln!("usage:\n  lngap-chess-venue venue [--dir D] [--block-secs N] [--max-depth M]\n  lngap-chess-venue play user|hub [--dir D] [--max-depth M]");
    std::process::exit(2)
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut dir = PathBuf::from("chess-venue");
    let mut block_secs = 30u64;
    let mut max_depth = 20u32;
    let mut positional = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--dir" => {
                dir = PathBuf::from(args.get(i + 1).unwrap_or_else(|| usage()));
                i += 2;
            }
            "--block-secs" => {
                block_secs = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or_else(|| usage());
                i += 2;
            }
            "--max-depth" => {
                max_depth = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or_else(|| usage());
                i += 2;
            }
            a if a.starts_with("--") => usage(),
            a => {
                positional.push(a.to_string());
                i += 1;
            }
        }
    }
    match positional.first().map(String::as_str) {
        Some("venue") => venue::run(dir, block_secs, max_depth),
        Some("play") => {
            let role = match positional.get(1).map(String::as_str) {
                Some("user") | Some("white") => Role::User,
                Some("hub") | Some("black") => Role::Hub,
                _ => usage(),
            };
            player::run(dir, role, max_depth)
        }
        Some(other) => bail!("unknown command {other}"),
        None => usage(),
    }
}
