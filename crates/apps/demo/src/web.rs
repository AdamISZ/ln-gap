//! The browser front: a `tiny_http` server per party process serving its
//! page, a JSON state endpoint and a command endpoint; the engine syncs
//! every second between requests.

use std::time::{Duration, Instant};

use anyhow::Result;
use tiny_http::{Header, Method, Request, Response, Server};

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

/// A party process as its page sees it.
pub trait Page {
    fn name(&self) -> String;
    fn publish_web_port(&self, port: u16) -> Result<()>;
    fn sync(&mut self) -> Result<()>;
    fn snapshot(&mut self) -> serde_json::Value;
    fn exec(&mut self, cmd: &str) -> Result<String>;
    fn html(&self) -> &'static str;
    /// Extra GET endpoints (path, full url) -> JSON.
    fn get(&mut self, _path: &str, _url: &str) -> Option<serde_json::Value> {
        None
    }
}

pub fn serve(mut p: impl Page, port: u16) -> Result<()> {
    let server = Server::http(("127.0.0.1", port)).map_err(|e| anyhow::anyhow!("binding 127.0.0.1:{port}: {e}"))?;
    p.publish_web_port(port)?;
    println!("{}: browse http://127.0.0.1:{port}", p.name());
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
            (Method::Get, "/") => req.respond(html(p.html())),
            (Method::Get, "/state") => {
                if let Err(e) = p.sync() {
                    println!("  ! sync: {e:#}");
                }
                let snap = p.snapshot();
                req.respond(json(&snap))
            }
            (Method::Post, "/cmd") => {
                if let Err(e) = p.sync() {
                    println!("  ! sync: {e:#}");
                }
                let b = body(&mut req);
                let r = match serde_json::from_str::<Cmd>(&b) {
                    Ok(cmd) => match p.exec(&cmd.cmd) {
                        Ok(output) => CmdResult { ok: true, output },
                        Err(e) => CmdResult { ok: false, output: format!("{e:#}") },
                    },
                    Err(e) => CmdResult { ok: false, output: format!("expected {{\"cmd\": ...}}: {e}") },
                };
                req.respond(json(&r))
            }
            (Method::Get, other) => match p.get(other, &url) {
                Some(v) => req.respond(json(&v)),
                None => req.respond(Response::from_string("not found").with_status_code(404)),
            },
            _ => req.respond(Response::from_string("not found").with_status_code(404)),
        };
        let _ = resp;
    }
}
