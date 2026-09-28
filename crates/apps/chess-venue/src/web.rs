//! The browser front: a `tiny_http` server per process serving one
//! embedded page and a JSON state endpoint, the page polling it. The
//! player's server runs the engine loop (`sync` between requests); the
//! venue's is driven from the venue's tick loop.

use std::io::Read;
use std::time::{Duration, Instant};

use anyhow::Result;
use tiny_http::{Header, Method, Request, Response, Server};

use crate::player::Player;

pub const PLAYER_HTML: &str = include_str!("player.html");
pub const VENUE_HTML: &str = include_str!("venue.html");
pub const DASHBOARD_HTML: &str = include_str!("dashboard.html");

fn header(k: &str, v: &str) -> Header {
    Header::from_bytes(k.as_bytes(), v.as_bytes()).expect("ascii header")
}

pub fn html(s: &str) -> Response<std::io::Cursor<Vec<u8>>> {
    Response::from_string(s).with_header(header("Content-Type", "text/html; charset=utf-8"))
}

pub fn json<T: serde::Serialize>(v: &T) -> Response<std::io::Cursor<Vec<u8>>> {
    Response::from_string(serde_json::to_string(v).unwrap_or_else(|e| format!("{{\"error\":\"{e}\"}}"))).with_header(header("Content-Type", "application/json"))
}

pub fn body(req: &mut Request) -> String {
    let mut s = String::new();
    let _ = req.as_reader().read_to_string(&mut s);
    s
}

/// `?k=v` of a URL, one key.
pub fn query(url: &str, key: &str) -> Option<String> {
    url.split_once('?')?.1.split('&').find_map(|kv| kv.strip_prefix(&format!("{key}=")).map(|v| v.to_string()))
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

/// The player's server loop: the engine syncs every second and answers
/// requests in between.
pub fn serve_player(mut p: Player, port: u16) -> Result<()> {
    let server = Server::http(("127.0.0.1", port)).map_err(|e| anyhow::anyhow!("binding 127.0.0.1:{port}: {e}"))?;
    p.publish_web_port(port)?;
    println!("{}: browse http://127.0.0.1:{port}", crate::store::side(p.role()));
    let mut last = Instant::now();
    loop {
        if last.elapsed() >= Duration::from_secs(1) {
            if let Err(e) = p.sync() {
                println!("  ! sync: {e:#}");
            }
            last = Instant::now();
        }
        let Some(mut req) = server.recv_timeout(Duration::from_millis(300))? else { continue };
        let url = req.url().to_string();
        let path = url.split('?').next().unwrap_or("").to_string();
        let resp = match (req.method(), path.as_str()) {
            (Method::Get, "/") => req.respond(html(PLAYER_HTML)),
            (Method::Get, "/state") => {
                // current before answering: the page and any driver see the
                // chain as of now, not as of the last periodic sync
                if let Err(e) = p.sync() {
                    println!("  ! sync: {e:#}");
                }
                let snap = p.snapshot();
                req.respond(json(&snap))
            }
            (Method::Get, "/legal") => {
                let from = query(&url, "from").unwrap_or_default();
                let v = p.legal_from(&from);
                req.respond(json(&v))
            }
            (Method::Post, "/cmd") => {
                if let Err(e) = p.sync() {
                    println!("  ! sync: {e:#}");
                }
                let b = body(&mut req);
                let cmd: Cmd = serde_json::from_str(&b).unwrap_or(Cmd { cmd: String::new() });
                let r = match p.exec(&cmd.cmd) {
                    Ok(output) => CmdResult { ok: true, output },
                    Err(e) => CmdResult { ok: false, output: format!("{e:#}") },
                };
                req.respond(json(&r))
            }
            _ => req.respond(Response::from_string("not found").with_status_code(404)),
        };
        let _ = resp;
    }
}
