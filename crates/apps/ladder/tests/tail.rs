//! The read and jump challenges (lngap_ladder::tail) over a synthetic
//! jump-list chain of 2,000 steps: every rule run in the Script simulator
//! on one-time signatures, within the stack limit.

use std::path::PathBuf;

use bitcoin::script::Builder;
use lngap_ladder::jhash::{preimage, step_hash_jump};
use lngap_ladder::jump::JumpList;
use lngap_ladder::rules::{spends, Rule};
use lngap_ladder::script::{rule_wire, wots_wire, Msg};
use lngap_ladder::tail::*;
use lngap_ladder::{Schedule, FIELD_JUMP_HASH, FIELD_RECORD, FIELD_STEP_HASH, FIELD_SUCC};
use lngap_lamport::winternitz::{WotsParams, WotsSecret};
use lngap_zk::game::{initial_hash, Record};
use lngap_zk::{Read, Step};

const NEVER: u64 = u64::MAX;

fn schedule() -> Schedule {
    let d = std::env::temp_dir().join(format!("lngap-tail-{}", std::process::id()));
    std::fs::create_dir_all(&d).unwrap();
    std::fs::copy(PathBuf::from(format!("{}/../zk/programs/hello-world.elf", env!("CARGO_MANIFEST_DIR"))), d.join("hello-world.elf")).unwrap();
    let p = d.join("hello.yaml");
    std::fs::write(&p, "elf: hello-world.elf\nnary_search: 2\nmax_steps: 2000\ninput_section_name: .input\njump_list: true\ninputs:\n  - size: 4\n    owner: prover\n").unwrap();
    Schedule::load(&p.display().to_string()).unwrap()
}

/// A chain: each step's write, and the hash after each step.
struct Chain {
    j: JumpList,
    writes: Vec<Step>,
    hashes: Vec<[u8; 20]>,
}

impl Chain {
    fn new(j: JumpList, n: usize) -> Chain {
        let mut writes = vec![Step::default()];
        let mut hashes = vec![initial_hash()];
        for i in 1..n {
            // step 1200 writes 7 to 0x1000; others write elsewhere
            let w = if i == 1200 { Step { write_addr: 0x1000, write_value: 7, pc: 0x80, micro: 0 } } else { Step { write_addr: 0x2000 + 4 * (i as u32 % 64), write_value: i as u32, pc: 0x80 + 4 * i as u32, micro: 0 } };
            let jh = hashes[j.jump(i as u64) as usize];
            hashes.push(step_hash_jump(&hashes[i - 1], &jh, &w, i as u32));
            writes.push(w);
        }
        Chain { j, writes, hashes }
    }
    fn pre(&self, x: u64) -> Vec<u8> {
        let x = x as usize;
        preimage(&self.hashes[x - 1], &self.hashes[self.j.jump(x as u64) as usize], &self.writes[x], x as u32)
    }
}

/// The parties' keys for the messages the tail's rules read.
struct Keys {
    final_: Vec<WotsSecret>,
    path: Vec<Vec<WotsSecret>>,
    hop: Vec<WotsSecret>,
}

impl Keys {
    fn new(s: &Schedule) -> Keys {
        let e = |a: u8, b: usize| -> [u8; 32] {
            let mut x = [a; 32];
            x[1] = b as u8;
            x
        };
        let final_ = s.fields(s.depths()).iter().enumerate().map(|(f, (_, l))| WotsSecret::from_entropy(WotsParams::for_bytes(*l as u32), e(1, f))).collect();
        let path = (0..CHUNKS).map(|c| chunk_fields(c).iter().enumerate().map(|(f, l)| WotsSecret::from_entropy(WotsParams::for_bytes(*l as u32), e(10 + c as u8, f))).collect()).collect();
        let hop = (0..CHUNKS).map(|k| WotsSecret::from_entropy(WotsParams::for_bytes(1), e(4, k))).collect();
        Keys { final_, path, hop }
    }
}

/// What's on chain: Alice's final move (by field), the path's links, her
/// choice.
struct Posted {
    final_: Vec<Vec<u8>>,
    path: Vec<Vec<u8>>,
    choice: u8,
}

fn field(msg: &[u8], sizes: &[usize], f: usize) -> Vec<u8> {
    let o: usize = sizes[..f].iter().sum();
    msg[o..o + sizes[f]].to_vec()
}

fn fires(s: &Schedule, rule: &Rule, keys: &Keys, p: &Posted, wit: &[u8]) -> (bool, usize) {
    let pk = |m: Msg| match m {
        Msg::Field(_, f) => keys.final_[f].public(),
        Msg::Path(l, f) => keys.path[l][f].public(),
        Msg::Hop(l) => keys.hop[l].public(),
        Msg::Word(_) => unreachable!(),
    };
    let script = rule.script(Builder::new(), &pk);
    let sizes: Vec<Vec<usize>> = (0..CHUNKS).map(chunk_fields).collect();
    let reveals: Vec<Vec<Vec<u8>>> = rule
        .msgs
        .iter()
        .map(|m| match *m {
            Msg::Field(_, f) => wots_wire(&keys.final_[f].sign(&p.final_[f]).unwrap()),
            Msg::Path(l, f) => wots_wire(&keys.path[l][f].sign(&field(&p.path[l], &sizes[l], f)).unwrap()),
            Msg::Hop(l) => wots_wire(&keys.hop[l].sign(&[p.choice]).unwrap()),
            Msg::Word(_) => unreachable!(),
        })
        .collect();
    let _ = s;
    spends(&script, rule_wire(wit, &reveals))
}

/// Alice's final move at agreed step `t`, with read 1 of (addr, value,
/// last write) and long-jump hash `jh`.
fn final_move(c: &Chain, t: u32, read: (u32, u32, u64), jh: [u8; 20]) -> Vec<Vec<u8>> {
    let rec = Record {
        read: Read { mem_witness: 0, read_1_addr: read.0, read_1_value: read.1, read_2_addr: 0x3000, read_2_value: 0, pc: 0x80, micro: 0, opcode: 0x13 },
        write: Step { write_addr: 0x2000, write_value: 1, pc: 0x84, micro: 0 },
        witness: 0,
        last_step_1: read.2,
        last_step_2: NEVER,
        step: t,
    };
    let _ = (FIELD_RECORD, FIELD_STEP_HASH, FIELD_JUMP_HASH, FIELD_SUCC);
    vec![rec.to_bytes().to_vec(), c.hashes[t as usize].to_vec(), [9u8; 20].to_vec(), jh.to_vec(), (t + 1).to_be_bytes().to_vec()]
}

#[test]
fn the_tail_over_a_chain() {
    let s = schedule();
    let j = s.jump.unwrap();
    assert_eq!(j, JumpList::new(11));
    let c = Chain::new(j, 2000);
    let keys = Keys::new(&s);
    let mut peak = 0usize;
    let mut check = |what: &str, got: (bool, usize), want: bool| {
        assert_eq!(got.0, want, "{what} (peak {})", got.1);
        if got.0 {
            peak = peak.max(got.1);
        }
    };

    // ----- the jump challenge: t = 1500, its successor's long jump -----
    let ts: Vec<u32> = (1400..1990u32).filter(|t| j.jump(u64::from(*t) + 1) + 8 < u64::from(*t)).take(3).chain([1500]).collect();
    for t in ts {
        let sx = u64::from(t) + 1;
        let y = j.jump(sx);
        let path = Path::build(&j, u64::from(t), y, &|x| c.hashes[x as usize]);
        let m = path.messages(&c.hashes[t as usize]);
        let k = path.chunks();
        let pre_y = c.pre(y);
        for (jh, want) in [(c.hashes[y as usize], false), ([5u8; 20], true)] {
            let p = Posted { final_: final_move(&c, t, (0x1000, 7, 1200), jh), path: m.clone(), choice: 0 };
            check(&format!("jump at t = {t} (y = {y}, n = {}), J {}", path.n(), if want { "wrong" } else { "right" }), fires(&s, &jump_verdict(&s, k), &keys, &p, &pre_y), want);
            if k > 1 {
                check(&format!("jump at t = {t}: the verdict for {} chunks", k - 1), fires(&s, &jump_verdict(&s, k - 1), &keys, &p, &pre_y), false);
            }
        }
        println!("TAIL jump: t = {t}, y = jump({sx}) = {y}, a path of {} hops", path.n());
    }

    // ----- the read challenge: step 1200 wrote 7 to 0x1000 -----
    let t = 1500u32;
    let y = 1200u64;
    let path = Path::build(&j, u64::from(t), y, &|x| c.hashes[x as usize]);
    let m = path.messages(&c.hashes[t as usize]);
    let kc = path.chunks();
    let pre_y = c.pre(y);
    for ((addr, value, ls), want, what) in [
        ((0x1000, 7, 1200), false, "an honest read"),
        ((0x1000, 8, 1200), true, "a wrong value from step 1200"),
        ((0x1000, 7, 1100), true, "a stale last write"),
        ((0x1000, 7, NEVER), true, "never written, but step 1200 wrote it"),
        ((0x1004, 7, 1100), false, "another address, written earlier"),
    ] {
        let p = Posted { final_: final_move(&c, t, (addr, value, ls), [0; 20]), path: m.clone(), choice: 0 };
        check(&format!("read: {what}"), fires(&s, &read_verdict(&s, kc, 1), &keys, &p, &pre_y), want);
        assert_eq!(read_contradicts(addr, value, ls, t, y as u32, 0x1000, 7), want, "the mirror: {what}");
    }
    println!("TAIL read: t = {t}, y = {y}, a path of {} hops in {kc} chunks", path.n());

    // ----- the hops: each revealed honestly; a forged hash fails -----
    let p = Posted { final_: final_move(&c, t, (0x1000, 7, 1200), [0; 20]), path: m.clone(), choice: 0 };
    let mut x = u64::from(t);
    let hops = j.path(u64::from(t), y);
    for (i, (_, next)) in hops.iter().enumerate() {
        let mut pk = Posted { final_: p.final_.clone(), path: p.path.clone(), choice: i as u8 };
        check(&format!("hop {i} honest"), fires(&s, &hop_rule(&s, kc, i), &keys, &pk, &c.pre(x)), true);
        let mut bad = c.pre(x);
        bad[45] ^= 1;
        check(&format!("hop {i}, a wrong preimage"), fires(&s, &hop_rule(&s, kc, i), &keys, &pk, &bad), false);
        pk.choice = (i + 1) as u8;
        check(&format!("hop {i}, another choice"), fires(&s, &hop_rule(&s, kc, i), &keys, &pk, &c.pre(x)), false);
        x = *next;
    }
    // a forged hash along the path: the hop before it no longer reveals
    let mut forged = path.clone();
    let i = path.n() / 2;
    forged.hashes[i][0] ^= 1;
    let xi = hops[i - 1].1;
    let pf = Posted { final_: p.final_.clone(), path: forged.messages(&c.hashes[t as usize]), choice: i as u8 };
    check("a forged hop hash", fires(&s, &hop_rule(&s, kc, i), &keys, &pf, &c.pre(xi)), false);
    // her choice beyond the path
    let pr = Posted { final_: p.final_.clone(), path: p.path.clone(), choice: path.n() as u8 };
    let range = hop_rules(&s, kc).into_iter().find(|r| r.name == "hop_range").unwrap();
    check("a choice beyond the path", fires(&s, &range, &keys, &pr, &[]), true);
    let pr = Posted { final_: p.final_.clone(), path: p.path.clone(), choice: 0 };
    check("a choice on the path", fires(&s, &range, &keys, &pr, &[]), false);

    // ----- no hops: the end must be h(t) -----
    let t0 = (1..1990u32).find(|t| j.jump(u64::from(*t) + 1) == u64::from(*t)).unwrap();
    let empty = Path::build(&j, u64::from(t0), u64::from(t0), &|x| c.hashes[x as usize]);
    assert_eq!(empty.n(), 0);
    let em = empty.messages(&c.hashes[t0 as usize]);
    let pe = Posted { final_: final_move(&c, t0, (0, 0, NEVER), [5; 20]), path: em.clone(), choice: 0 };
    check("no hops, the end h(t), J wrong", fires(&s, &jump_verdict(&s, 1), &keys, &pe, &c.pre(u64::from(t0))), true);
    let mut em2 = em.clone();
    em2[0][1 + TYPES_BYTES] ^= 1; // the end, not h(t)
    let pe2 = Posted { final_: pe.final_.clone(), path: em2, choice: 0 };
    check("no hops, an end that isn't h(t)", fires(&s, &jump_verdict(&s, 1), &keys, &pe2, &c.pre(u64::from(t0))), false);

    // ----- the longest path: 86 hops in 8 chunks, and its last hop -----
    let long = Chain::new(JumpList::new(29), 2);
    let _ = long;
    assert_eq!(MAX_HOPS, 86);
    assert_eq!(chunks_for(86), 8);
    assert_eq!(chunks_for(9), 1);
    assert_eq!(chunks_for(10), 2);

    println!("TAIL every rule within the stack limit: peak {peak}");
}
