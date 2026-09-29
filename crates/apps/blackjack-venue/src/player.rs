//! One party of the blackjack session, on the shared demo layer
//! (`lngap-demo`, D58): the channel and its hands, the venue view and the
//! disputes are the crate's; this module is blackjack's rules (shares,
//! judging an entry, the disprove predicates, R), the player's moves, the
//! house's reveals and cheats, and the pages' view.
//!
//! The house's autopilot plays its own moves (the reveals, the dealer's
//! forced draws) and settles hands it won; every dispute step is the
//! presenter's click unless automatic disputes is on.

use std::collections::BTreeMap;
use std::io::{BufRead, Write};
use std::path::PathBuf;

use anyhow::{anyhow, bail, ensure, Result};
use lngap_blackjack as bj;
use lngap_blackjack::{action, phase, status, Commitments, Share, State, K as POSITIONS};
use lngap_channel::Role;
use lngap_contract::Payout;
use lngap_demo::hand::{ActionView, Hand, Phase, Rules};
use lngap_demo::session::Session;
use lngap_demo::store::*;
use lngap_demo::web::Page;
use lngap_pos::blackjack;
use lngap_pos::instance::{self, Game, PosInstance};
use rand::SeedableRng;
use serde::Serialize;

pub const PLAYER_HTML: &str = include_str!("player.html");
pub const HOUSE_HTML: &str = include_str!("house.html");
pub const DASHBOARD_HTML: &str = include_str!("dashboard.html");

pub fn side(r: Role) -> &'static str {
    match r {
        Role::User => "Player",
        Role::Hub => "House",
    }
}

pub fn ui(s: &str) -> String {
    s.replace("UserWins", "PlayerWins").replace("HubWins", "HouseWins")
}

fn status_ui(st: u8) -> &'static str {
    match st {
        status::PLAYER => "the Player wins",
        status::HOUSE => "the House wins",
        status::PUSH => "push",
        _ => "open",
    }
}

fn action_ui(a: u8) -> &'static str {
    match a {
        action::DEAL => "DEAL",
        action::REVEAL => "REVEAL",
        action::HIT => "HIT",
        action::STAND => "STAND",
        action::ACK => "ACK",
        _ => "?",
    }
}

fn whose(r: Role) -> u8 {
    r.idx() as u8
}

/// Both offers' commitments (each offer's `extra` is `{"commits": [hex; 16]}`).
pub fn commitments(user: &serde_json::Value, hub: &serde_json::Value) -> Result<Commitments> {
    let arr = |o: &serde_json::Value| -> Result<[[u8; 32]; POSITIONS]> {
        let v: Vec<[u8; 32]> = o["commits"].as_array().ok_or_else(|| anyhow!("no commitments"))?.iter().map(|h| h.as_str().and_then(|h| hex::decode(h).ok()).and_then(|b| b.try_into().ok()).ok_or_else(|| anyhow!("a commitment is 32 bytes"))).collect::<Result<_>>()?;
        v.try_into().map_err(|_| anyhow!("sixteen commitments"))
    };
    Ok(Commitments { player: arr(user)?, house: arr(hub)? })
}

/// Blackjack's rules for the session.
pub struct BjRules {
    me: Role,
    shares: Vec<Share>,
    /// The counterparty's revealed strings, by (whose, position).
    strings: BTreeMap<(u8, usize), Vec<u8>>,
    commits: Option<Commitments>,
    /// The hand after the last valid move.
    pub state: State,
}

impl BjRules {
    fn string(&self, who: u8, k: usize) -> Option<Vec<u8>> {
        if who == whose(self.me) {
            self.shares.get(k).map(|s| s.string.clone())
        } else {
            self.strings.get(&(who, k)).cloned()
        }
    }

    /// The predicates that fire on (prior, new) at `slot`, with witnesses.
    fn predicates(&self, h: &Hand, slot: u32, prior: &State, new_head: &[u8; 48]) -> Vec<(String, Vec<Vec<u8>>)> {
        let n = State::from_head(new_head);
        let pl = instance::mover_at(slot) == Role::User;
        let mut out: Vec<(String, Vec<Vec<u8>>)> = Vec::new();
        let word0_ok = new_head[0..4] == bj::word0(GAME_ID, slot, whose(instance::mover_at(slot))).to_be_bytes();
        let prior_ok = slot == 1 || h.blocks.get(&(slot - 1)).is_some_and(|b| b.header.head()[0..4] == bj::word0(GAME_ID, slot - 1, whose(instance::mover_at(slot - 1))).to_be_bytes());
        if !word0_ok || !prior_ok {
            out.push(("wrong_slot".into(), vec![]));
        }
        for (name, f) in [
            ("bj_malformed", bj::head_malformed(new_head)),
            ("bj_transition", bj::transition_fires(prior, &n, pl)),
            ("bj_counters", bj::counters_fires(prior, &n)),
            ("bj_cards_kept", bj::cards_kept_fires(prior, &n)),
            ("bj_status", bj::status_fires(prior, &n)),
            ("bj_dealer", !pl && bj::dealer_fires(prior, &n)),
        ] {
            if f {
                out.push((name.into(), vec![]));
            }
        }
        let mover = whose(instance::mover_at(slot));
        for k in 0..POSITIONS {
            if let Some(s) = self.string(mover, k) {
                if bj::share_fires(&n, k, bj::open(&s)) {
                    out.push((format!("bj_share_{k}"), vec![s]));
                }
            }
            if !pl {
                if let (Some(a), Some(b)) = (self.string(0, k), self.string(1, k)) {
                    if bj::card_fires(prior, &n, k, bj::open(&a), bj::open(&b)) {
                        out.push((format!("bj_card_{k}"), vec![a, b]));
                    }
                }
            }
        }
        out
    }

    fn describe(&self) -> String {
        let s = &self.state;
        let cards = |ps: &[usize]| ps.iter().filter(|k| s.dealt(**k)).map(|k| bj::rank_name(s.cards[*k])).collect::<Vec<_>>().join(" ");
        match s.action {
            action::DEAL => "DEAL: the player's shares of the first three cards".into(),
            action::HIT => format!("HIT: the player's share of card {}", s.np),
            action::STAND => format!("STAND on {}: the player's shares of the hole and every draw", s.player_total()),
            action::ACK => format!("ACK: {}", status_ui(s.status)),
            action::REVEAL => {
                let mut t = format!("REVEAL: player {} ({})", cards(&s.player_positions()), s.player_total());
                if s.dealt(bj::HOLE) {
                    t += &format!(", dealer {} ({})", cards(&s.dealer_positions()), s.dealer_total());
                } else if s.dealt(bj::UP) {
                    t += &format!(", dealer shows {}", bj::rank_name(s.cards[bj::UP]));
                }
                if s.is_terminal() {
                    t += &format!(" — {}", status_ui(s.status));
                }
                t
            }
            _ => "?".into(),
        }
    }
}

impl Rules for BjRules {
    fn game(&self) -> Game {
        Game::Blackjack
    }

    fn auth_message(&self, head: &[u8; 48]) -> Vec<u8> {
        blackjack::auth_message(head)
    }

    fn begin(&mut self, _id: u32) -> serde_json::Value {
        let mut rng = rand::rngs::StdRng::from_entropy();
        self.shares = (0..POSITIONS).map(|_| Share::random(&mut rng)).collect();
        self.strings.clear();
        self.commits = None;
        self.state = State::initial();
        serde_json::json!({ "commits": self.shares.iter().map(|s| hex::encode(s.commitment())).collect::<Vec<_>>() })
    }

    fn instance(&self, inst: PosInstance, user: &serde_json::Value, hub: &serde_json::Value) -> Result<PosInstance> {
        inst.with_commitments(commitments(user, hub)?)
    }

    fn judge(&mut self, h: &Hand, slot: u32, head: &[u8; 48], tail: &[u8]) -> std::result::Result<String, String> {
        if self.commits.is_none() {
            let (u, hb) = h.extras.as_ref().ok_or("no offers")?;
            self.commits = Some(commitments(u, hb).map_err(|e| e.to_string())?);
        }
        let commits = self.commits.clone().ok_or("no commitments")?;
        let mover = instance::mover_at(slot);
        let n = State::from_head(head);
        let strings = bj::decode_shares(tail).unwrap_or_default();
        let range: Vec<usize> = bj::revealed(&n).filter(|k| *k < POSITIONS).collect();
        let mut opened = strings.len() == range.len();
        for (k, s) in range.iter().zip(strings.iter()) {
            opened &= bj::open(s) >= 0 && bj::commit(s) == *commits.of(mover == Role::User, *k);
            if mover != self.me {
                self.strings.insert((whose(mover), *k), s.clone());
            }
        }
        if !opened {
            return Err("a declared share does not open its commitment".into());
        }
        let firing = self.predicates(h, slot, &self.state, head);
        if !firing.is_empty() {
            return Err(firing.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>().join(", "));
        }
        self.state = n;
        Ok(self.describe())
    }

    fn firing(&self, h: &Hand, d: u32) -> Vec<(String, Vec<Vec<u8>>)> {
        let Some(new) = h.blocks.get(&d) else { return vec![] };
        let prior = if d >= 2 {
            match h.blocks.get(&(d - 1)) {
                Some(b) => State::from_head(&b.header.head()),
                None => return vec![],
            }
        } else {
            State::initial()
        };
        self.predicates(h, d, &prior, &new.header.head())
    }

    fn resolution(&self, head: &[u8; 48], d: u32) -> u8 {
        bj::resolution(&State::from_head(head), whose(instance::mover_at(d)))
    }

    fn result(&self) -> Option<Payout> {
        match self.state.status {
            status::PLAYER => Some(Payout::UserAll),
            status::HOUSE => Some(Payout::HubAll),
            status::PUSH => Some(Payout::Even),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Mode {
    Honest,
    WrongCard,
    DrawAt17,
    StandOn16,
    Withhold,
}

impl Mode {
    fn parse(s: &str) -> Option<Mode> {
        Some(match s {
            "honest" => Mode::Honest,
            "wrongcard" => Mode::WrongCard,
            "drawat17" => Mode::DrawAt17,
            "standon16" => Mode::StandOn16,
            "withhold" => Mode::Withhold,
            _ => return None,
        })
    }
}

pub struct Player {
    s: Session,
    h: Hand,
    r: BjRules,
    mode: Mode,
    autopilot: bool,
    auto_disputes: bool,
    done: std::collections::BTreeSet<String>,
    failed: BTreeMap<String, u32>,
}

impl Player {
    pub fn open(dir: PathBuf, me: Role) -> Result<Player> {
        let s = Session::open(dir, me, "blackjack-venue", side, ui)?;
        Ok(Player {
            s,
            h: Hand::default(),
            r: BjRules { me, shares: vec![], strings: BTreeMap::new(), commits: None, state: State::initial() },
            mode: Mode::Honest,
            autopilot: me == Role::Hub,
            auto_disputes: false,
            done: Default::default(),
            failed: BTreeMap::new(),
        })
    }

    fn me(&self) -> Role {
        self.s.me
    }

    /// The winner proposes the settlement: the player for a win or push,
    /// the house for its wins.
    fn my_win(&self) -> bool {
        self.r.state.is_terminal()
            && match self.r.state.status {
                status::PLAYER | status::PUSH => self.me() == Role::User,
                status::HOUSE => self.me() == Role::Hub,
                _ => false,
            }
    }

    pub fn sync(&mut self) -> Result<()> {
        // the venue before the bus: a settle proposal must find the final
        // seal already read (my policy judges it against my view)
        self.h.venue(&mut self.s, &mut self.r)?;
        if self.h.playing() {
            if let Some(p) = self.r.result() {
                let _ = self.h.agree(&self.s, p);
            }
        }
        self.s.bus()?;
        if let Err(e) = self.h.negotiate(&mut self.s, &mut self.r, "hand") {
            self.s.say(format!("hand {}: {e:#}", self.h.id));
        }
        let blocks = self.s.scan()?;
        self.h.on_blocks(&mut self.s, blocks)?;
        if self.autopilot {
            if let Err(e) = self.pilot() {
                self.s.say(format!("autopilot: {e:#}"));
            }
        }
        Ok(())
    }

    fn actions(&self) -> Vec<ActionView> {
        let s = &self.s;
        let h = &self.h;
        let now = unix_now();
        let d = h.depth + 1;
        let mover = instance::mover_at(d);
        let playing = h.playing();
        let mut v = Vec::new();
        if self.me() == Role::User {
            v.push(if s.channel_open() && matches!(h.phase, None | Some(Phase::Settled)) && s.idle() {
                ActionView::ok("new hand", &format!("hand {}: {} sat each into the pot, {} each as a dispute deposit", h.id + 1, STAKE_SAT, s.vparams.deposit))
            } else {
                ActionView::no("new hand", if s.channel_open() { "a hand is in progress" } else { "the channel is closed" })
            });
            let st = &self.r.state;
            let can = playing && mover == self.me() && now <= h.due(d) && h.pending.as_ref().is_none_or(|p| p.0 != d);
            let why = if !playing { "no hand in play".to_string() } else if mover != self.me() { format!("the House to move (move {d})") } else if now > h.due(d) { format!("move {d} was due at t+{}s", h.rel(h.due(d))) } else { format!("move {d} due in {}s", i64::from(h.due(d)) - i64::from(now)) };
            v.push(if can && st.phase == phase::START { ActionView::ok("deal", &why) } else { ActionView::no("deal", &why) });
            let decide = can && st.phase == phase::DECIDE;
            v.push(if decide && bj::can_hit(st) { ActionView::ok("hit", &format!("you have {}", st.player_total())) } else { ActionView::no("hit", "not your decision") });
            v.push(if decide { ActionView::ok("stand", &format!("stand on {}", st.player_total())) } else { ActionView::no("stand", "not your decision") });
        }
        v.push(if playing && s.in_channel(h.id) && self.my_win() && s.idle() {
            ActionView::ok("settle", &format!("{}: pay it in the channel, now", status_ui(self.r.state.status)))
        } else if playing && self.r.state.is_terminal() {
            ActionView::no("settle", &format!("{}: the winner settles it", status_ui(self.r.state.status)))
        } else {
            ActionView::no("settle", "the hand is not over")
        });
        v.extend(h.dispute_actions(s, &self.r));
        if self.me() == Role::User {
            v.push(if s.channel_open() && !s.in_channel(h.id) && s.idle() && s.chan.current_seq() > 0 { ActionView::ok("close channel", "pay both balances out in one cooperative transaction") } else { ActionView::no("close channel", "only with no hand in the channel") });
        }
        v
    }

    fn settle(&mut self) -> Result<()> {
        ensure!(self.r.state.is_terminal(), "the hand is not over");
        let p = self.r.result().ok_or_else(|| anyhow!("no result"))?;
        self.s.say(format!("hand {}: {}", self.h.id, status_ui(self.r.state.status)));
        self.h.settle(&mut self.s, p)
    }

    fn split(&mut self) -> Result<()> {
        self.h.split(&mut self.s, &self.r, &|_s, _d, _code, su, sh, pair| Ok(blackjack::checked_split_witness(su, sh, pair)))
    }

    fn pilot(&mut self) -> Result<()> {
        let d = self.h.depth + 1;
        let now = unix_now();
        if self.h.playing() && instance::mover_at(d) == self.me() && now <= self.h.due(d) && self.h.pending.is_none() && !self.h.blocks.contains_key(&d) && self.mode != Mode::Withhold && matches!(self.r.state.phase, phase::DEALT | phase::HIT | phase::STOOD) {
            self.reveal()?;
        }
        let pool = self.h.mempool_labels(&self.s);
        let settling = self.r.state.is_terminal() && self.s.in_channel(self.h.id) && self.h.settle_sent.is_none_or(|t| now < t + 30);
        for a in self.actions() {
            if !a.enabled {
                continue;
            }
            let key = format!("{}:{}:{}", self.h.id, a.name, a.hint);
            if self.done.contains(&key) || self.failed.get(&key).is_some_and(|t| now < t + 10) {
                continue;
            }
            if a.name != "settle" && !self.auto_disputes {
                continue;
            }
            let r = match a.name.as_str() {
                "settle" => self.settle(),
                "force close" if self.h.grievance(&self.s).is_some() && self.mode != Mode::Withhold && !settling => self.s.force_close(),
                "refute" if !pool.iter().any(|l| l.ends_with("/refute")) => self.h.refute(&mut self.s, &self.r),
                "claim" if self.mode != Mode::Withhold => {
                    let dd = a.cmd.split_whitespace().nth(1).and_then(|x| x.parse().ok());
                    self.h.claim(&mut self.s, dd)
                }
                "disprove" => self.h.disprove(&mut self.s, &self.r, None),
                "timely" => self.h.timely(&mut self.s),
                "split" => self.split(),
                _ => continue,
            };
            match r {
                Ok(()) => {
                    self.done.insert(key);
                }
                Err(e) => {
                    self.failed.insert(key, now);
                    self.s.say(format!("autopilot: {} failed (retrying in 10s): {e:#}", a.name));
                }
            }
        }
        Ok(())
    }

    fn reveal(&mut self) -> Result<()> {
        let d = self.h.depth + 1;
        let prior = self.r.state;
        let card_of = |r: &BjRules, k: usize| -> Result<u8> {
            let a = r.strings.get(&(0, k)).ok_or_else(|| anyhow!("the player's share {k} is not known"))?;
            let a = bj::open(a);
            ensure!((0..=12).contains(&a), "the player's share {k} is out of range");
            Ok(bj::card(a as u8, r.shares[k].value))
        };
        let mut cards = [0u8; POSITIONS];
        for k in bj::revealed(&match prior.phase {
            phase::DEALT => State { lo: 0, hi: 3, ..prior },
            _ => prior,
        }) {
            cards[k] = card_of(&self.r, k)?;
        }
        let mut n = bj::house_reveal(&prior, |k| cards[k]).ok_or_else(|| anyhow!("no reveal from phase {}", prior.phase))?;
        let mut cheat = "";
        match self.mode {
            Mode::WrongCard => {
                let k = if prior.phase == phase::STOOD { bj::HOLE } else { (n.np - 1) as usize };
                n.cards[k] = (n.cards[k] + 1) % 13;
                if prior.phase == phase::STOOD {
                    n.status = bj::showdown(&n);
                } else if prior.phase == phase::HIT {
                    n.status = if n.player_total() > 21 { status::HOUSE } else { status::OPEN };
                    n.phase = if n.status != status::OPEN { phase::DONE } else { phase::DECIDE };
                }
                cheat = " (CHEAT: a card one rank off)";
            }
            Mode::DrawAt17 if prior.phase == phase::STOOD && n.np < bj::DRAW_LIMIT => {
                let k = n.np as usize;
                n.cards[k] = cards[k];
                n.np += 1;
                n.status = bj::showdown(&n);
                cheat = " (CHEAT: the dealer draws past 17)";
            }
            Mode::StandOn16 if prior.phase == phase::STOOD && n.np > prior.np => {
                let keep = n.np - 1;
                n.cards[keep as usize] = 0;
                n.np = keep;
                n.status = bj::showdown(&n);
                cheat = " (CHEAT: the dealer stops early)";
            }
            _ => {}
        }
        if !cheat.is_empty() {
            self.mode = Mode::Honest;
        }
        self.submit(d, &n)?;
        self.s.say(format!("submitted move {d}: REVEAL{cheat}"));
        Ok(())
    }

    fn submit(&mut self, d: u32, n: &State) -> Result<()> {
        let head = n.head(GAME_ID, d, whose(self.me()));
        let sig = self.s.ks.sign_wots(&instance::state_label(self.h.id, 1, d), &blackjack::auth_message(&head)).map_err(|e| anyhow!("signing (a depth's state key signs once): {e}"))?;
        let strings: Vec<Vec<u8>> = bj::revealed(n).filter(|k| *k < POSITIONS).map(|k| self.r.shares[k].string.clone()).collect();
        let refs: Vec<&[u8]> = strings.iter().map(|v| v.as_slice()).collect();
        let entry = blackjack::entry(&head, &sig, &refs);
        self.h.submit(&mut self.s, d, &entry)
    }

    fn play(&mut self, what: &str) -> Result<()> {
        ensure!(self.me() == Role::User, "the House plays itself");
        ensure!(self.h.playing(), "no hand in play");
        let d = self.h.depth + 1;
        ensure!(instance::mover_at(d) == self.me(), "it is the House's move (move {d})");
        ensure!(unix_now() <= self.h.due(d), "your move {d} was due at t+{}s", self.h.rel(self.h.due(d)));
        ensure!(self.h.pending.as_ref().is_none_or(|p| p.0 != d), "your move {d} is already with the venue");
        let st = self.r.state;
        let n = match what {
            "deal" => {
                ensure!(st.phase == phase::START, "already dealt");
                bj::deal(&st)
            }
            "hit" => {
                ensure!(st.phase == phase::DECIDE && bj::can_hit(&st), "you cannot hit now");
                bj::hit(&st)
            }
            "stand" => {
                ensure!(st.phase == phase::DECIDE, "you cannot stand now");
                bj::stand(&st)
            }
            "ack" => {
                ensure!(bj::can_ack(&st), "only after a hand you won or pushed");
                bj::ack(&st)
            }
            _ => bail!("unknown move {what}"),
        };
        self.submit(d, &n)?;
        self.s.say(format!("submitted move {d}: {}", what.to_uppercase()));
        Ok(())
    }

    fn view(&mut self) -> Snapshot {
        let st = self.r.state;
        let dealt = |k: usize| st.dealt(k);
        let player_cards: Vec<String> = st.player_positions().into_iter().filter(|k| dealt(*k)).map(|k| bj::rank_name(st.cards[k]).to_string()).collect();
        let mut dealer_cards: Vec<String> = Vec::new();
        if dealt(bj::UP) {
            dealer_cards.push(bj::rank_name(st.cards[bj::UP]).into());
            if dealt(bj::HOLE) {
                dealer_cards.push(bj::rank_name(st.cards[bj::HOLE]).into());
                for k in st.ds as usize..st.np as usize {
                    dealer_cards.push(bj::rank_name(st.cards[k]).into());
                }
            } else {
                dealer_cards.push("?".into());
            }
        }
        let (slots, live, mempool) = self.h.views(&self.s, &|_, b| action_ui(State::from_head(&b.header.head()).action).to_string());
        let disproves = self.h.disprove_depth(&self.s).map(|d| self.r.firing(&self.h, d).into_iter().map(|(n, _)| n).collect()).unwrap_or_default();
        let d = self.h.depth;
        Snapshot {
            role: self.me().name().into(),
            height: self.s.height(),
            now: self.h.rel(unix_now()),
            next_due: self.h.rel(self.h.due(d + 1)),
            depth: d,
            to_move: side(instance::mover_at(d + 1)).into(),
            hand: self.h.id,
            hand_phase: self.h.phase,
            channel: self.s.channel_view(),
            results: self.h.results.clone(),
            status: status_ui(st.status).into(),
            terminal: st.is_terminal(),
            player_cards,
            player_total: if dealt(0) { st.player_total() } else { 0 },
            dealer_cards,
            dealer_total: if dealt(bj::HOLE) { Some(st.dealer_total()) } else { None },
            n: self.s.vparams.n,
            threshold: self.s.vparams.threshold,
            backoff: self.s.vparams.backoff,
            margin: self.s.vparams.margin,
            slots,
            live,
            actions: self.actions(),
            disproves,
            mempool,
            balance_sat: self.s.onchain_balance(),
            mode: self.mode,
            autopilot: self.autopilot,
            auto_disputes: self.auto_disputes,
            log: self.s.log.iter().rev().take(80).rev().cloned().collect(),
        }
    }

    pub fn exec(&mut self, line: &str) -> Result<String> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        let Some(cmd) = parts.first() else { return Ok(String::new()) };
        let arg = parts.get(1).map(|s| s.to_string());
        let before = self.s.log.len();
        let r: Result<String> = match *cmd {
            "help" | "?" => Ok(HELP.to_string()),
            "new" => self.h.request_new(&mut self.s, &mut self.r).map(|id| {
                self.s.say(format!("hand {id}: requested; the venue computes the hand's registry..."));
                String::new()
            }),
            "deal" | "hit" | "stand" | "ack" => self.play(cmd).map(|_| String::new()),
            "settle" => self.settle().map(|_| String::new()),
            "force" => self.s.force_close().map(|_| String::new()),
            "close" => self.s.close_channel().map(|_| String::new()),
            "mode" => {
                let m = arg.as_deref().and_then(Mode::parse).ok_or_else(|| anyhow!("mode honest|wrongcard|drawat17|standon16|withhold"))?;
                ensure!(self.me() == Role::Hub, "the Player does not cheat in this demo");
                self.mode = m;
                Ok(format!("the House's next move: {m:?}"))
            }
            "autopilot" => {
                self.autopilot = arg.as_deref() != Some("off");
                Ok(format!("autopilot (own moves and settling wins) {}", if self.autopilot { "on" } else { "off" }))
            }
            "autodisputes" => {
                self.auto_disputes = arg.as_deref() != Some("off");
                Ok(format!("automatic disputes {}", if self.auto_disputes { "on" } else { "off: click each step" }))
            }
            "claim" => self.h.claim(&mut self.s, arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "counter" => self.h.counter(&mut self.s, arg.and_then(|a| a.parse().ok())).map(|_| String::new()),
            "refute" => self.h.refute(&mut self.s, &self.r).map(|_| String::new()),
            "disprove" => self.h.disprove(&mut self.s, &self.r, arg).map(|_| String::new()),
            "timely" => self.h.timely(&mut self.s).map(|_| String::new()),
            "split" => self.split().map(|_| String::new()),
            other => Err(anyhow!("unknown command {other} (try `help`)")),
        };
        let said: Vec<String> = self.s.log[before..].to_vec();
        match r {
            Ok(text) => Ok(if text.is_empty() { said.join("\n") } else { text }),
            Err(e) => Err(e),
        }
    }
}

impl Page for Player {
    fn name(&self) -> String {
        side(self.me()).into()
    }
    fn publish_web_port(&self, port: u16) -> Result<()> {
        self.s.publish_web_port(port)
    }
    fn sync(&mut self) -> Result<()> {
        Player::sync(self)
    }
    fn snapshot(&mut self) -> serde_json::Value {
        serde_json::to_value(self.view()).unwrap_or_default()
    }
    fn exec(&mut self, cmd: &str) -> Result<String> {
        Player::exec(self, cmd)
    }
    fn html(&self) -> &'static str {
        if self.me() == Role::Hub { HOUSE_HTML } else { PLAYER_HTML }
    }
}

const HELP: &str = "commands:
  new | deal | hit | stand | settle
                        the player's session and moves (settle: pay the hand's result in the channel)
  force | claim [d] | counter [d] | refute | disprove [name] | timely | split
                        disputes (force: force-close the channel, putting the hand on chain)
  close                 close the channel cooperatively (no hand in it)
  mode honest|wrongcard|drawat17|standon16|withhold   the house's next move
  autopilot on|off      the house plays its own moves and settles its wins (default on)
  autodisputes on|off   the house also takes every dispute step itself (default off)
  quit";

pub fn run(dir: PathBuf, me: Role, web: Option<u16>) -> Result<()> {
    let p = Player::open(dir, me)?;
    if let Some(port) = web {
        return lngap_demo::web::serve(p, port);
    }
    let mut p = p;
    println!("{HELP}");
    let stdin = std::io::stdin();
    let mut line = String::new();
    loop {
        p.sync()?;
        print!("{}> ", side(me));
        std::io::stdout().flush()?;
        line.clear();
        if stdin.lock().read_line(&mut line)? == 0 {
            break;
        }
        if line.trim() == "quit" || line.trim() == "exit" {
            break;
        }
        match p.exec(&line) {
            Ok(text) if text.is_empty() => {}
            Ok(text) => println!("{text}"),
            Err(e) => println!("  ! {e:#}"),
        }
    }
    Ok(())
}

#[derive(Serialize, Clone, Debug)]
pub struct Snapshot {
    pub role: String,
    pub height: u32,
    pub now: i64,
    pub next_due: i64,
    pub depth: u32,
    pub to_move: String,
    pub hand: u32,
    pub hand_phase: Option<Phase>,
    pub channel: lngap_demo::session::ChannelView,
    pub results: Vec<String>,
    pub status: String,
    pub terminal: bool,
    pub player_cards: Vec<String>,
    pub player_total: u32,
    pub dealer_cards: Vec<String>,
    pub dealer_total: Option<u32>,
    pub n: usize,
    pub threshold: u32,
    pub backoff: u32,
    pub margin: u32,
    pub slots: Vec<lngap_demo::hand::SlotView>,
    pub live: Vec<lngap_demo::hand::LiveView>,
    pub actions: Vec<ActionView>,
    pub disproves: Vec<String>,
    pub mempool: Vec<String>,
    pub balance_sat: u64,
    pub mode: Mode,
    pub autopilot: bool,
    pub auto_disputes: bool,
    pub log: Vec<String>,
}
