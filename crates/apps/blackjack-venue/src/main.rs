//! `lngap-blackjack-venue`: one hand of blackjack on the PoS venue (D57),
//! the player in a browser, the house an automatic party.
//!
//! Three processes share one directory (`--dir`, default `./blackjack-venue`):
//!
//! ```text
//!   lngap-blackjack-venue venue [--dir D] [--web 8080]    # the node, the roster, the clock
//!   lngap-blackjack-venue play player [--dir D] [--web 8081]
//!   lngap-blackjack-venue play house [--dir D] [--web 8082]
//! ```
//!
//! The player deals, hits, stands and (after a win or a push) acknowledges
//! from its page; every dispute button is there too. The house plays
//! itself: it reveals its share of each card as soon as the player's move
//! is sealed, plays the dealer's hand by the rule, and answers disputes
//! honestly, unless its page (the presenter's console) sets a cheat: a
//! wrong card, drawing at 17, standing on 16, or withholding a reveal. The
//! venue's page is the chess demo's; `/dashboard` frames all three.
//!
//! Each side commits at open to sixteen shares, one per card position
//! (SHA256 of a string of 32 + v random bytes); card `k` is the two shares'
//! sum mod 13. A share is revealed in the entry body of the move that
//! reveals it, and the members seal only entries whose declared reveals
//! open (D57).

mod player;

use std::path::PathBuf;

use anyhow::{bail, Result};
use lngap_channel::Role;
use lngap_demo::venue::{Timing, VenueConfig};

fn usage() -> ! {
    eprintln!("usage:\n  lngap-blackjack-venue venue [--dir D] [--block-secs N] [--max-depth M] [--ell S] [--backoff S] [--margin S] [--start-secs S (default 15)] [--deposit SAT] [--web PORT]\n  lngap-blackjack-venue play player|house [--dir D] [--max-depth M] [--web PORT]");
    std::process::exit(2)
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut dir = PathBuf::from("blackjack-venue");
    let mut block_secs = 20u64;
    // the deposit covers the longest dispute path at the demo's fixed
    // pre-sign fee: claim or counter, refutation, split (4 x 40k)
    let mut timing = Timing { ell: 60, backoff: 5, margin: 60, start_secs: 15, deposit: 170_000 };
    // a long hand: deal, reveal, 8 hits and their cards, stand, the dealer,
    // an ack, and the depth after it (the claim that ends the hand)
    let mut max_depth = 24u32;
    let mut web: Option<u16> = None;
    let mut positional = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let val = |i: usize| args.get(i + 1).cloned().unwrap_or_else(|| usage());
        match args[i].as_str() {
            "--dir" => dir = PathBuf::from(val(i)),
            "--block-secs" => block_secs = val(i).parse().unwrap_or_else(|_| usage()),
            "--max-depth" => max_depth = val(i).parse().unwrap_or_else(|_| usage()),
            "--ell" => timing.ell = val(i).parse().unwrap_or_else(|_| usage()),
            "--backoff" => timing.backoff = val(i).parse().unwrap_or_else(|_| usage()),
            "--margin" => timing.margin = val(i).parse().unwrap_or_else(|_| usage()),
            "--start-secs" => timing.start_secs = val(i).parse().unwrap_or_else(|_| usage()),
            "--deposit" => timing.deposit = val(i).parse().unwrap_or_else(|_| usage()),
            "--web" => web = Some(val(i).parse().unwrap_or_else(|_| usage())),
            a if a.starts_with("--") => usage(),
            a => {
                positional.push(a.to_string());
                i += 1;
                continue;
            }
        }
        i += 2;
    }
    match positional.first().map(String::as_str) {
        Some("venue") => {
            let cfg = VenueConfig {
                build: Box::new(|inst, user, hub| inst.with_commitments(player::commitments(&user.extra, &hub.extra)?)),
                game: lngap_pos::instance::Game::Blackjack,
                dashboard_html: player::DASHBOARD_HTML,
                names: player::side,
            };
            lngap_demo::venue::run(dir, block_secs, max_depth, web, timing, cfg)
        }
        Some("play") => {
            let role = match positional.get(1).map(String::as_str) {
                Some("player") | Some("user") => Role::User,
                Some("house") | Some("hub") => Role::Hub,
                _ => usage(),
            };
            let _ = max_depth;
            player::run(dir, role, web)
        }
        Some(other) => bail!("unknown command {other}"),
        None => usage(),
    }
}
