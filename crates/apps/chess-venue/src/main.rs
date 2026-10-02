//! `lngap-chess-venue`: an interactive chess game on the PoS venue, played from
//! two terminals against one regtest node, with the roster (five members
//! sharing one content key, majority flags — D50-D53) sealing the moves.
//!
//! Three processes share one directory (`--dir`, default `./chess-venue`):
//!
//! ```text
//!   lngap-chess-venue venue [--dir D] [--block-secs 20] [--ell 90] [--web 8080]   # the node, the roster, the clock
//!   lngap-chess-venue play white [--dir D] [--web 8081]                # White
//!   lngap-chess-venue play black [--dir D] [--web 8082]                # Black
//! ```
//!
//! With `--web` a process serves a page on that port instead of (the
//! players) or beside (the venue) its terminal loop: the player's page
//! has the board, the cheat menu, the dispute buttons and the venue and
//! chain views; the venue's page has the slot timeline and the
//! misbehaviour controls, and `/dashboard` frames all three.
//!
//! The venue starts a regtest node (datadir `D/node`, kept) and mines a
//! block every `--block-secs` seconds, independently of the game (D55).
//! Move `d` is due at `t0 + d·ell` (`--ell` seconds per move; `t0` fixed
//! by the contract, `--start-secs` after it is proposed). The venue seals
//! each entry a player drops in its inbox on arrival, by the member it is
//! addressed to (the rotation; the mover falls back after `--backoff`
//! seconds), flags every move whose due time passes with no signed seal,
//! publishes both to `D/venue/`, and funds and registers the contract
//! once both players have agreed it. A claim waits for median-time-past
//! to pass the due time plus `--margin`. The players exchange their
//! key offers and their graph signatures through `D/players/` and then
//! drive the game — and its disputes — from a small REPL or page.
//!
//! The two players open a Poon-Dryja channel once (D58); each game is a
//! contract added to it by a channel update. A game is settled by the next
//! update: the winner settles a mate, a stalemate or an accepted draw
//! splits evenly, and a resignation concedes. A game with no agreed result
//! goes on chain by force-closing the channel. The session, the venue and
//! the dispute layer are shared with the blackjack demo (`lngap-demo`). Nothing else
//! connects them: a disprover reads the mover's reveal off the confirmed
//! refutation on the chain, as it would in deployment.

mod player;

use std::path::PathBuf;

use anyhow::{bail, Result};
use lngap_channel::Role;
use lngap_demo::venue::{Timing, VenueConfig};

fn usage() -> ! {
    eprintln!("usage:\n  lngap-chess-venue venue [--dir D] [--block-secs N] [--max-depth M] [--ell S] [--backoff S] [--margin S] [--start-secs S] [--deposit SAT] [--web PORT]\n  lngap-chess-venue play white|black [--dir D] [--max-depth M] [--web PORT]");
    std::process::exit(2)
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut dir = PathBuf::from("chess-venue");
    let mut block_secs = 20u64;
    // the deposit covers the longest dispute path at the demo's fixed
    // pre-sign fee: claim or counter, refutation, split (4 x 40k)
    let mut timing = Timing { ell: 90, backoff: 5, margin: 60, start_secs: 60, deposit: 170_000 };
    // the last move of a game, in plies (moves by either side): a game
    // that reaches it without a mate is a draw
    let mut max_depth = 50u32;
    let mut web: Option<u16> = None;
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
            "--ell" | "--backoff" | "--margin" | "--start-secs" => {
                let v: u32 = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or_else(|| usage());
                match args[i].as_str() {
                    "--ell" => timing.ell = v,
                    "--backoff" => timing.backoff = v,
                    "--margin" => timing.margin = v,
                    _ => timing.start_secs = v,
                }
                i += 2;
            }
            "--deposit" => {
                timing.deposit = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or_else(|| usage());
                i += 2;
            }
            "--web" => {
                web = Some(args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or_else(|| usage()));
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
        Some("venue") => {
            let cfg = VenueConfig {
                build: Box::new(|inst, _, _| Ok(inst)),
                game: lngap_pos::instance::Game::Chess,
                dashboard_html: player::DASHBOARD_HTML,
                names: player::side,
            };
            lngap_demo::venue::run(dir, block_secs, max_depth, web, timing, cfg)
        }
        Some("play") => {
            let role = match positional.get(1).map(String::as_str) {
                Some("user") | Some("white") => Role::User,
                Some("hub") | Some("black") => Role::Hub,
                _ => usage(),
            };
            player::run(dir, role, web)
        }
        Some(other) => bail!("unknown command {other}"),
        None => usage(),
    }
}
