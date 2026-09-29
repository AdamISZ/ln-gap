//! One side of the chess session, on the shared demo layer (`lngap-demo`,
//! D58): a Poon-Dryja channel with the opponent, game after game inside
//! it. The channel, the venue view and the disputes are the crate's; this
//! module is chess's rules (legality, the disprove family, R), the moves
//! and the cheat menu, the endings (settle a mate, resign, offer and accept
//! a draw), and the page's view.
//!
//! Endings: after a mate the winner SETTLES (the loser's policy accepts:
//! its client sees the same mate); a stalemate is settled as a draw; RESIGN
//! concedes the game (always acceptable to the opponent); OFFER DRAW agrees
//! to an even split and tells the opponent, whose ACCEPT DRAW proposes it.
//! A game with no agreed result goes on chain by force-close.

use std::io::{BufRead, Write};
use std::path::PathBuf;

use anyhow::{anyhow, bail, ensure, Result};
use lngap_channel::Role;
use lngap_chess::certificate::find_kind;
use lngap_chess::leaf::exhibit_values;
use lngap_chess::{apply, Move, Terminal};
use lngap_chess_fc::{ChessEntry, ChessState};
use lngap_contract::Payout;
use lngap_demo::hand::{ActionView, Hand, Phase, Rules};
use lngap_demo::session::Session;
use lngap_demo::store::*;
use lngap_demo::web::{query, Page};
use lngap_pos::chess;
use lngap_pos::instance::{self, Game, PosInstance};
use serde::Serialize;

pub const PLAYER_HTML: &str = include_str!("player.html");
pub const DASHBOARD_HTML: &str = include_str!("dashboard.html");

/// White is the channel's user, Black its counterparty.
pub fn side(r: Role) -> &'static str {
    match r {
        Role::User => "White",
        Role::Hub => "Black",
    }
}

pub fn ui(s: &str) -> String {
    s.replace("UserWins", "WhiteWins").replace("HubWins", "BlackWins")
}

fn scriptnum(v: i64) -> Vec<u8> {
    assert!((0..128).contains(&v));
    if v == 0 { vec![] } else { vec![v as u8] }
}

/// An entry's authorship message (D43): the 40 state bytes, then the move's
/// two bytes (low first).
fn entry_msg(e: &ChessEntry) -> Vec<u8> {
    let mv = u32::from(e.state.mv.to_u16());
    let mut m = e.state.to_e().to_vec();
    m.extend_from_slice(&(mv as u16).to_le_bytes());
    m
}

fn win_for(r: Role) -> Payout {
    if r == Role::User { Payout::UserAll } else { Payout::HubAll }
}

/// Chess's rules for the session.
pub struct ChessRules {
    /// The position after the last valid move.
    pub state: ChessState,
}

impl ChessRules {
    fn state_of(head: &[u8; 48]) -> Option<ChessState> {
        ChessState::from_e(head[8..48].try_into().ok()?).ok()
    }
}

impl Rules for ChessRules {
    fn game(&self) -> Game {
        Game::Chess
    }

    fn auth_message(&self, head: &[u8; 48]) -> Vec<u8> {
        chess::auth_message(head)
    }

    fn begin(&mut self, _id: u32) -> serde_json::Value {
        self.state = ChessState::initial();
        serde_json::Value::Null
    }

    fn instance(&self, inst: PosInstance, _user: &serde_json::Value, _hub: &serde_json::Value) -> Result<PosInstance> {
        Ok(inst)
    }

    fn judge(&mut self, _h: &Hand, slot: u32, head: &[u8; 48], _tail: &[u8]) -> std::result::Result<String, String> {
        let mover = instance::mover_at(slot);
        if head[0..4] != lngap_pos::ttt::word0(GAME_ID, slot, mover).to_be_bytes() {
            return Err("an entry for the wrong depth, mover or game (wrong_slot)".into());
        }
        if chess::is_malformed(head, slot) {
            return Err("a malformed entry (chess_malformed)".into());
        }
        let Some(new) = Self::state_of(head) else { return Err("an undecodable position".into()) };
        match apply(&self.state.pos, new.mv) {
            Ok(mut pos) => {
                pos.fullmove = 0;
                if pos != new.pos {
                    return Err(format!("the position claimed for {} is not its result", new.mv));
                }
                self.state = new;
                let term = lngap_chess::terminal(&self.state.pos).map(|t| format!(" — {t:?}")).unwrap_or_default();
                Ok(format!("{} (signed, legal){term}", self.state.mv))
            }
            Err(v) => Err(format!("{} is ILLEGAL ({v})", new.mv)),
        }
    }

    fn firing(&self, h: &Hand, d: u32) -> Vec<(String, Vec<Vec<u8>>)> {
        let (Some(new), Ok(inst)) = (h.blocks.get(&d), h.inst()) else { return vec![] };
        let prior_head = if d >= 2 {
            match h.blocks.get(&(d - 1)) {
                Some(b) => b.header.head(),
                None => return vec![],
            }
        } else {
            chess::initial_head(GAME_ID)
        };
        let new_head = new.header.head();
        let l = inst.layout(d);
        let prior = if d >= 2 { Self::state_of(&prior_head) } else { Some(ChessState::initial()) };
        let after = Self::state_of(&new_head);
        chess::disprove_leaves(&l, &inst.depth_keys(d).refute)
            .into_iter()
            .filter(|pl| (pl.fires)(&prior_head, &new_head))
            .map(|pl| {
                let wits = chess::kinds()
                    .into_iter()
                    .find(|k| chess::leaf_name(*k) == pl.name)
                    .and_then(|kind| {
                        let (p, a) = (prior.as_ref()?, after.as_ref()?);
                        find_kind(&p.pos, a.mv, &a.pos, kind).map(exhibit_values)
                    })
                    .map(|ex| ex.iter().map(|&v| scriptnum(v)).collect())
                    .unwrap_or_default();
                (pl.name, wits)
            })
            .collect()
    }

    fn resolution(&self, head: &[u8; 48], _d: u32) -> u8 {
        // the side to move forfeits
        match Self::state_of(head) {
            Some(st) if st.pos.side == lngap_chess::Colour::White => 1,
            _ => 0,
        }
    }

    fn result(&self) -> Option<Payout> {
        match lngap_chess::terminal(&self.state.pos)? {
            // the side to move is mated: the other side wins
            Terminal::Checkmate => Some(if self.state.pos.side == lngap_chess::Colour::White { Payout::HubAll } else { Payout::UserAll }),
            Terminal::Stalemate => Some(Payout::Even),
        }
    }
}

pub struct Player {
    s: Session,
    h: Hand,
    r: ChessRules,
}

impl Player {
    pub fn open(dir: PathBuf, me: Role) -> Result<Player> {
        let s = Session::open(dir, me, "chess-venue", side, ui)?;
        Ok(Player { s, h: Hand::default(), r: ChessRules { state: ChessState::initial() } })
    }

    fn me(&self) -> Role {
        self.s.me
    }

    fn draw_offered_by(&self, r: Role) -> bool {
        self.h.id > 0 && self.s.store.exists(&draw_offer(self.h.id, r))
    }

    pub fn sync(&mut self) -> Result<()> {
        self.h.venue(&mut self.s, &mut self.r)?;
        if self.h.playing() {
            if let Some(p) = self.r.result() {
                let _ = self.h.agree(&self.s, p);
            }
        }
        self.s.bus()?;
        if let Err(e) = self.h.negotiate(&mut self.s, &mut self.r, "game") {
            self.s.say(format!("game {}: {e:#}", self.h.id));
        }
        let blocks = self.s.scan()?;
        self.h.on_blocks(&mut self.s, blocks)?;
        Ok(())
    }

    fn actions(&self) -> Vec<ActionView> {
        let s = &self.s;
        let h = &self.h;
        let now = unix_now();
        let d = h.depth + 1;
        let mover = instance::mover_at(d);
        let playing = h.playing();
        let in_chan = s.in_channel(h.id);
        let terminal = lngap_chess::terminal(&self.r.state.pos);
        let mut v = Vec::new();
        if self.me() == Role::User {
            v.push(if s.channel_open() && matches!(h.phase, None | Some(Phase::Settled)) && s.idle() {
                ActionView::ok("new game", &format!("game {}: {} sat each into the pot, {} each as a dispute deposit", h.id + 1, STAKE_SAT, s.vparams.deposit))
            } else {
                ActionView::no("new game", if s.channel_open() { "a game is in progress" } else { "the channel is closed" })
            });
        }
        v.push(if !playing {
            ActionView::no("move", "no game in play")
        } else if terminal.is_some() {
            ActionView::no("move", "the game is over")
        } else if mover != self.me() {
            ActionView::no("move", &format!("{} to move (move {d}, due t+{}s)", side(mover), h.rel(h.due(d))))
        } else if now > h.due(d) {
            ActionView::no("move", &format!("your move {d} was due at t+{}s: you are stalled", h.rel(h.due(d))))
        } else if let Some((pd, _, to, _)) = h.pending.as_ref().filter(|p| p.0 == d) {
            ActionView::no("move", &format!("your move {pd} is with member {to}"))
        } else {
            let left = i64::from(h.due(d)) - i64::from(now);
            ActionView::ok("move", &format!("move {d} is due in {left}s"))
        });
        // the endings
        let my_result = self.r.result().is_some_and(|p| match p {
            Payout::Even => self.me() == Role::User,
            p => p == win_for(self.me()),
        });
        v.push(if playing && in_chan && my_result && s.idle() {
            ActionView::ok("settle", &format!("{:?}: pay it in the channel, now", terminal.expect("a result is terminal")))
        } else if playing && terminal.is_some() {
            ActionView::no("settle", "the winner settles it")
        } else {
            ActionView::no("settle", "the game is not over")
        });
        let can_end = playing && in_chan && s.idle() && terminal.is_none();
        v.push(if can_end { ActionView::ok("resign", "concede the game: the opponent takes the pot, now") } else { ActionView::no("resign", "only in a game in progress") });
        let theirs = self.draw_offered_by(self.me().other());
        let mine = self.draw_offered_by(self.me());
        v.push(if can_end && !mine && !theirs { ActionView::ok("offer draw", "propose an even split; the opponent may accept") } else { ActionView::no("offer draw", if mine { "offered: waiting for the opponent" } else { "only in a game in progress" }) });
        v.push(if can_end && theirs { ActionView::ok("accept draw", &format!("{} offered a draw: split the pot evenly, now", side(self.me().other()))) } else { ActionView::no("accept draw", "no draw offered") });
        v.extend(h.dispute_actions(s, &self.r));
        if self.me() == Role::User {
            v.push(if s.channel_open() && !in_chan && s.idle() && s.chan.current_seq() > 0 { ActionView::ok("close channel", "pay both balances out in one cooperative transaction") } else { ActionView::no("close channel", "only with no game in the channel") });
        }
        v
    }

    fn settle(&mut self) -> Result<()> {
        let p = self.r.result().ok_or_else(|| anyhow!("the game is not over"))?;
        self.h.settle(&mut self.s, p)
    }

    fn resign(&mut self) -> Result<()> {
        ensure!(lngap_chess::terminal(&self.r.state.pos).is_none(), "the game is over: settle it");
        self.s.say(format!("game {}: {} RESIGNS", self.h.id, side(self.me())));
        let p = win_for(self.me().other());
        self.h.settle(&mut self.s, p)
    }

    fn offer_draw(&mut self) -> Result<()> {
        ensure!(self.h.playing() && self.s.in_channel(self.h.id), "no game in the channel");
        self.h.agree(&self.s, Payout::Even)?;
        self.s.store.write(&draw_offer(self.h.id, self.me()), &serde_json::json!({ "depth": self.h.depth }))?;
        self.s.say(format!("game {}: {} offers a draw", self.h.id, side(self.me())));
        Ok(())
    }

    fn accept_draw(&mut self) -> Result<()> {
        ensure!(self.draw_offered_by(self.me().other()), "no draw offered");
        self.s.say(format!("game {}: {} accepts the draw", self.h.id, side(self.me())));
        self.h.settle(&mut self.s, Payout::Even)
    }

    fn split(&mut self) -> Result<()> {
        let id = self.h.id;
        self.h.split(&mut self.s, &self.r, &|s, d, code, su, sh, pair| {
            let reveal = s.ks.reveal_uint(&instance::code_label(id, 1, d), u32::from(code))?;
            Ok(lngap_pos::ttt::checked_split_witness(su, sh, &reveal, pair))
        })
    }

    fn entry_for(&mut self, d: u32, state: &ChessState) -> Result<Vec<u8>> {
        let me = self.me().idx() as u8;
        let sig = self.s.ks.sign_wots(&instance::state_label(self.h.id, 1, d), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: state.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing (a depth's state key signs once): {e}"))?;
        Ok(ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: state.clone(), sigs: sig.hashes.clone() }.encode())
    }

    fn play_move(&mut self, uci: &str) -> Result<()> {
        ensure!(self.h.playing(), "no game in play");
        let d = self.h.depth + 1;
        ensure!(instance::mover_at(d) == self.me(), "it is {}'s move (move {d})", side(instance::mover_at(d)));
        ensure!(unix_now() <= self.h.due(d), "your move {d} was due at t+{}s", self.h.rel(self.h.due(d)));
        let mv = Move::parse(uci).ok_or_else(|| anyhow!("not a UCI move: {uci}"))?;
        let mut pos = apply(&self.r.state.pos, mv).map_err(|v| anyhow!("illegal: {v}"))?;
        pos.fullmove = 0;
        let new = ChessState { pos, mv, depth: d as u8 };
        let entry = self.entry_for(d, &new)?;
        self.h.submit(&mut self.s, d, &entry)?;
        self.s.say(format!("submitted {uci} as move {d} to member {}, the designated sealer", lngap_pos::rotation(self.h.id, d, self.s.vparams.n)));
        Ok(())
    }

    /// Publish `uci` dishonestly: `illegal` (the mechanical successor,
    /// signed), `garbage` (junk preimages), `malformed` (from-square 255),
    /// `wrongdepth` (signed with the next depth's key), `late` (after the
    /// due time, for a colluding member to seal).
    fn cheat_move(&mut self, uci: &str, how: &str) -> Result<()> {
        ensure!(self.h.playing(), "no game in play");
        let d = self.h.depth + 1;
        ensure!(instance::mover_at(d) == self.me(), "it is {}'s move (move {d})", side(instance::mover_at(d)));
        if how == "late" {
            ensure!(unix_now() > self.h.due(d), "your move {d} is not due until t+{}s: `move` it", self.h.rel(self.h.due(d)));
        } else {
            ensure!(unix_now() <= self.h.due(d), "your move {d} was due at t+{}s", self.h.rel(self.h.due(d)));
        }
        let mv = Move::parse(uci).ok_or_else(|| anyhow!("not a UCI move: {uci}"))?;
        let me = self.me().idx() as u8;
        let legal = |p: &lngap_chess::Position| -> Result<ChessState> {
            let mut pos = apply(p, mv).map_err(|v| anyhow!("{v}"))?;
            pos.fullmove = 0;
            Ok(ChessState { pos, mv, depth: d as u8 })
        };
        let prior = self.r.state.pos.clone();
        let (entry, what) = match how {
            "late" => (self.entry_for(d, &legal(&prior)?)?, "LATE: after its due time — honest members will not seal it; a colluding member may (the venue page's `late` control)"),
            "illegal" => {
                let mut pos = lngap_chess::certificate::mechanical_successor(&prior, mv);
                pos.fullmove = 0;
                (self.entry_for(d, &ChessState { pos, mv, depth: d as u8 })?, "WITHOUT checking legality (signed)")
            }
            "garbage" => (ChessEntry { game_id: GAME_ID, depth: d as u8, mover: me, state: legal(&prior)?, sigs: vec![[0x11; 20]; 87] }.encode(), "with a GARBAGE signature: honest members refuse it; a rogue may seal it"),
            "malformed" => {
                let new = legal(&prior)?;
                let mut head = chess::head(GAME_ID, d as u8, self.me(), &new);
                head[8 + 36] = 255;
                let sig = self.s.ks.sign_wots(&instance::state_label(self.h.id, 1, d), &chess::auth_message(&head)).map_err(|e| anyhow!("signing: {e}"))?;
                let mut e = head.to_vec();
                for x in &sig.hashes {
                    e.extend_from_slice(x);
                }
                (e, "MALFORMED (from-square byte 255, signed)")
            }
            "wrongdepth" => {
                let wrong = (d + 2) as u8;
                let new = ChessState { depth: wrong, ..legal(&prior)? };
                let sig = self.s.ks.sign_wots(&instance::state_label(self.h.id, 1, u32::from(wrong)), &entry_msg(&ChessEntry { game_id: GAME_ID, depth: wrong, mover: me, state: new.clone(), sigs: vec![] })).map_err(|e| anyhow!("signing: {e}"))?;
                (ChessEntry { game_id: GAME_ID, depth: wrong, mover: me, state: new, sigs: sig.hashes.clone() }.encode(), "claiming the WRONG depth: honest members refuse it; a rogue may seal it")
            }
            other => bail!("unknown cheat `{other}` (illegal | garbage | malformed | wrongdepth | late)"),
        };
        self.h.submit(&mut self.s, d, &entry)?;
        if matches!(how, "garbage" | "wrongdepth" | "late") {
            self.h.pending = None;
        }
        self.s.say(format!("submitted {uci} as move {d} {what}"));
        Ok(())
    }

    fn view(&mut self) -> Snapshot {
        let (slots, live, mempool) = self.h.views(&self.s, &|_, b| ChessEntry::decode(&b.entry).map(|e| e.state.mv.to_string()).unwrap_or_else(|_| "?".into()));
        let disproves = self.h.disprove_depth(&self.s).map(|d| self.r.firing(&self.h, d).into_iter().map(|(name, _)| DisproveView { name, fires: true }).collect()).unwrap_or_default();
        let d = self.h.depth;
        Snapshot {
            role: self.me().name().into(),
            height: self.s.height(),
            mtp: self.h.rel(self.s.rt.mtp().unwrap_or(0)),
            now: self.h.rel(unix_now()),
            ell: self.s.vparams.ell,
            backoff: self.s.vparams.backoff,
            margin: self.s.vparams.margin,
            next_due: self.h.rel(self.h.due(d + 1)),
            depth: d,
            game: self.h.id,
            game_phase: self.h.phase,
            channel: self.s.channel_view(),
            results: self.h.results.clone(),
            draw_offered: self.draw_offered_by(Role::User) || self.draw_offered_by(Role::Hub),
            fen: self.r.state.pos.to_fen(),
            to_move: instance::mover_at(d + 1).name().into(),
            terminal: lngap_chess::terminal(&self.r.state.pos).map(|t| format!("{t:?}")),
            last_move: (d >= 1).then(|| self.r.state.mv.to_string()),
            n: self.s.vparams.n,
            threshold: self.s.vparams.threshold,
            slots,
            live,
            actions: self.actions(),
            disproves,
            mempool,
            balance_sat: self.s.onchain_balance(),
            log: self.s.log.iter().rev().take(80).rev().cloned().collect(),
        }
    }

    pub fn exec(&mut self, line: &str) -> Result<String> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        let Some(cmd) = parts.first() else { return Ok(String::new()) };
        let arg = parts.get(1).map(|s| s.to_string());
        let arg2 = parts.get(2).map(|s| s.to_string());
        let before = self.s.log.len();
        let r: Result<String> = match *cmd {
            "help" | "?" => Ok(HELP.to_string()),
            "board" | "b" => Ok(format!("{}", self.r.state.pos)),
            "new" => self.h.request_new(&mut self.s, &mut self.r).map(|id| {
                self.s.say(format!("game {id}: requested; the venue computes the game's registry..."));
                String::new()
            }),
            "move" | "m" => arg.ok_or_else(|| anyhow!("move <uci>")).and_then(|u| self.play_move(&u)).map(|_| String::new()),
            "cheat" => arg.ok_or_else(|| anyhow!("cheat <uci> [illegal|garbage|malformed|wrongdepth|late]")).and_then(|u| self.cheat_move(&u, arg2.as_deref().unwrap_or("illegal"))).map(|_| String::new()),
            "settle" => self.settle().map(|_| String::new()),
            "resign" => self.resign().map(|_| String::new()),
            "draw" => self.offer_draw().map(|_| String::new()),
            "accept" => self.accept_draw().map(|_| String::new()),
            "force" => self.s.force_close().map(|_| String::new()),
            "close" => self.s.close_channel().map(|_| String::new()),
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

    /// Legal destination squares from `from` (click-to-move).
    fn legal_from(&self, from: &str) -> Vec<String> {
        lngap_chess::legal_moves(&self.r.state.pos).into_iter().map(|m| m.to_string()).filter(|u| u.starts_with(from)).map(|u| u[2..4].to_string()).collect()
    }
}

fn draw_offer(id: u32, r: Role) -> String {
    format!("games/{id:04}/draw-offer-{}.json", r.name())
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
        PLAYER_HTML
    }
    fn get(&mut self, path: &str, url: &str) -> Option<serde_json::Value> {
        (path == "/legal").then(|| serde_json::json!(self.legal_from(&query(url, "from").unwrap_or_default())))
    }
}

const HELP: &str = "commands:
  new                   White: start a game in the channel
  move <uci>            play (e.g. `move e2e4`)
  cheat <uci> [how]     publish dishonestly: illegal (default) | garbage | malformed | wrongdepth | late
  settle | resign | draw | accept
                        end the game in the channel: settle a mate, resign, offer / accept a draw
  force | claim [d] | counter [d] | refute | disprove [kind] | timely | split
                        disputes (force: force-close the channel, putting the game on chain)
  close                 close the channel cooperatively (no game in it)
  board                 the position
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
pub struct DisproveView {
    pub name: String,
    pub fires: bool,
}

#[derive(Serialize, Clone, Debug)]
pub struct Snapshot {
    pub role: String,
    pub height: u32,
    pub mtp: i64,
    pub now: i64,
    pub ell: u32,
    pub backoff: u32,
    pub margin: u32,
    pub next_due: i64,
    pub depth: u32,
    pub game: u32,
    pub game_phase: Option<Phase>,
    pub channel: lngap_demo::session::ChannelView,
    pub results: Vec<String>,
    pub draw_offered: bool,
    pub fen: String,
    pub to_move: String,
    pub terminal: Option<String>,
    pub last_move: Option<String>,
    pub n: usize,
    pub threshold: u32,
    pub slots: Vec<lngap_demo::hand::SlotView>,
    pub live: Vec<lngap_demo::hand::LiveView>,
    pub actions: Vec<ActionView>,
    pub disproves: Vec<DisproveView>,
    pub mempool: Vec<String>,
    pub balance_sat: u64,
    pub log: Vec<String>,
}
