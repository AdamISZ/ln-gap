//! D62: the read challenge, BitVMX's second search, as phase 2 of the
//! search game, natively and in Script. hello-world in binary search,
//! BitVMX's own fault cases (its tests 35-36):
//!
//! - R1: the prover claims step 1106 read the input word as 0x11111100,
//!   last written at step 600. The read search ends at 599 and BitVMX
//!   chooses ReadValue: `zk_read_value_2` fires (step 600 didn't write it).
//! - R2: the same, with the prover lying in its hashes during the read
//!   search: BitVMX chooses CorrectHash, and `zk_correct_hash` fires.
//! - R3: an honest prover, the read challenge forced: neither fires.
//!
//! Every phase-2 move keeps the rules (`zk_open`, the choices, the
//! copies); Script == mirror for every terminal leaf, honest and with a
//! wrong witness; `zk_open` fires on malformed openings; the peak stays
//! under 1,000.

use bitcoin::ScriptBuf;
use bitvmx_cpu_definitions::challenge::ChallengeType;
use emulator::decision::challenge::{ForceChallenge, ForceCondition};
use emulator::executor::utils::{FailConfiguration, FailReads, FailWrite};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::rebut::{disprove_witness, pair_key};
use lngap_zk::dispute::{search_with_read, Behaviour, ReadSearched, Searched};
use lngap_zk::game::*;
use lngap_zk::{nibble_witness, Step};

const GAME: u16 = 1;

fn pdf() -> String {
    format!("{}/programs/hello-world-binary.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn strs(v: &[&str]) -> Vec<String> {
    v.iter().map(|x| x.to_string()).collect()
}

fn run(name: &str, prover: Behaviour, prover_read: Behaviour, fc: ForceCondition, f: ForceChallenge) -> (Searched, ReadSearched) {
    let dir = std::env::temp_dir().join(format!("lngap-zk-read-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let (s, r) = search_with_read(&pdf(), &[0x11; 4], &dir, &prover, &prover_read, &Behaviour::default(), fc, f, ForceChallenge::No).unwrap().expect("a challenge");
    let _ = std::fs::remove_dir_all(&dir);
    (s, r.expect("a read challenge"))
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

/// Run a leaf over the pair (prior, new) with `below` under the reveal.
fn fires(script: &ScriptBuf, sk: &WotsSecret, prior: &[u8; 48], new: &[u8; 48], below: Vec<Vec<u8>>) -> (bool, usize) {
    let mut w = below;
    w.extend(disprove_witness(&sk.sign(&[prior.as_slice(), new.as_slice()].concat()).unwrap()));
    match lngap_script32::sim::run_peak(script.as_script(), w) {
        Ok((st, peak)) => (st.len() == 1 && truthy(&st[0]), peak),
        Err(_) => (false, 0),
    }
}

fn write_of(t: &bitvmx_cpu_definitions::trace::TraceStep) -> Step {
    Step { write_addr: t.get_write().address, write_value: t.get_write().value, pc: t.get_pc().get_address(), micro: t.get_pc().get_micro() }
}

#[test]
fn read_challenge_game() {
    let sk = pair_key([91; 32]);
    let rounds = ProgramDefinition::from_config(&pdf()).unwrap().nary_def().total_rounds() as u32;
    let sr = Search { game_id: GAME, rounds };
    println!("phases: 1 to {}, the opening at {}, the terminal at {}", sr.depths(), sr.open_depth(), sr.total());
    let fail_read_2 = FailConfiguration::new_fail_reads(FailReads::new(None, Some(&strs(&["1106", "0xaa000000", "0x11111100", "0xaa000000", "600"]))));
    let fail_write = FailConfiguration::new_fail_write(FailWrite::new(&strs(&["600", "0xaa000000", "0x11111100", "0xaa000000"])));
    let cases = [
        ("R1", run("R1", Behaviour { fail: Some(fail_read_2.clone()) }, Behaviour::default(), ForceCondition::ValidInputWrongStepOrHash, ForceChallenge::No), "read_value"),
        (
            "R2",
            run("R2", Behaviour { fail: Some(fail_read_2) }, Behaviour { fail: Some(fail_write) }, ForceCondition::ValidInputWrongStepOrHash, ForceChallenge::No),
            "correct_hash",
        ),
        ("R3", run("R3", Behaviour::default(), Behaviour::default(), ForceCondition::ValidInputStepAndHash, ForceChallenge::ReadValueNArySearch), "none"),
    ];
    let (open_leaf, rv1, rv2, ch) = (sr.open_leaf(&sk.public()), sr.read_value_leaf(&sk.public(), 1), sr.read_value_leaf(&sk.public(), 2), sr.correct_hash_leaf(&sk.public()));
    let mut peak = 0;
    for (name, (s, r), expect) in &cases {
        let p1 = play(s, &sr).unwrap();
        let p2 = play_read(r, &sr, &p1).unwrap();
        assert_eq!(p2.first().unwrap().depth, sr.open_depth());
        assert_eq!(p2.last().unwrap().depth, sr.total());
        // the rules hold on every phase-2 move, and the bodies open
        for e in &p2 {
            assert!(sr.body_opens(e.depth, &e.head, &e.body()), "{name}: body at {}", e.depth);
            assert_eq!(e.head[..4], lngap_pos::ttt::word0(GAME, e.depth, mover_at(e.depth)).to_be_bytes());
        }
        assert!(!Search::open_fires(p1.last().unwrap(), &p2[0]), "{name}: the opening");
        let (f, pk) = fires(&open_leaf, &sk, &p1.last().unwrap().head, &p2[0].head, nibble_witness(&p2[0].state.to_bytes()));
        assert!(!f, "{name}: zk_open on an honest opening");
        peak = peak.max(pk);
        for w in p2.windows(2) {
            let (a, b) = (&w[0], &w[1]);
            if b.depth % 2 == 0 {
                assert!(!sr.choice_fires(a, b), "{name}: choice at {}", b.depth);
            } else {
                assert!(!Search::copied_fires(&a.head, &b.head), "{name}: copied at {}", b.depth);
            }
        }
        // the terminal leaves, with the verifier's witness from BitVMX's
        // challenge
        let rec1 = p1.last().unwrap().record.unwrap();
        let (prior, term) = (&p2[p2.len() - 2], p2.last().unwrap());
        let s2 = prior.state;
        let (w, vh) = match &r.challenge {
            ChallengeType::ReadValue { trace, .. } => (write_of(trace), [0u8; 20]),
            ChallengeType::CorrectHash { trace, verifier_hash, .. } => (write_of(trace), hex::decode(verifier_hash).unwrap().try_into().unwrap()),
            c => panic!("{name}: unexpected {c:?}"),
        };
        let mut wbad = w;
        wbad.write_value ^= 1;
        let mut fired = vec![];
        for (wit_w, label) in [(w, "W"), (wbad, "a wrong W")] {
            for (sel, leaf) in [(1u8, &rv1), (2, &rv2)] {
                let below = [nibble_witness(&rec1.to_bytes()), nibble_witness(&s2.to_bytes()), nibble_witness(&wit_w.to_bytes())].concat();
                let (f, pk) = fires(leaf, &sk, &prior.head, &term.head, below);
                assert_eq!(f, read_value_fires(&rec1, &s2, &wit_w, sel), "{name}: read_value_{sel} with {label}: script vs mirror");
                peak = peak.max(pk);
                if f {
                    fired.push(format!("read_value_{sel}"));
                }
            }
            let mut wit = vh.to_vec();
            wit.extend_from_slice(&wit_w.to_bytes());
            let below = [nibble_witness(&s2.to_bytes()), nibble_witness(&wit)].concat();
            let (f, pk) = fires(&ch, &sk, &prior.head, &term.head, below);
            assert_eq!(f, correct_hash_fires(&s2, &vh, &wit_w), "{name}: correct_hash with {label}: script vs mirror");
            peak = peak.max(pk);
            if f {
                fired.push("correct_hash".into());
            }
        }
        println!(
            "{name}: conflict step {}, read search ends at {} (base {}); BitVMX: {}; fired: {fired:?}",
            s.step,
            r.step + 1,
            s2.base,
            format!("{:?}", r.challenge).split(' ').next().unwrap(),
        );
        match *expect {
            "read_value" => assert!(fired.iter().any(|f| f.starts_with("read_value")), "{name}"),
            "correct_hash" => assert!(fired.contains(&"correct_hash".to_string()), "{name}"),
            _ => assert!(fired.is_empty(), "{name}: nothing fires on an honest prover"),
        }
    }
    // malformed openings
    let (s, r) = &cases[0].1;
    let p1 = play(s, &sr).unwrap();
    let open = play_read(r, &sr, &p1).unwrap()[0].clone();
    for bad in [State { lo: [1; 20], ..open.state }, State { base: 3, ..open.state }, State { claim: [2; 20], ..open.state }, State { hi: [3; 20], ..open.state }] {
        let e = Entry { state: bad, head: head(GAME, open.depth, mover_at(open.depth), &bad.digest(), &bad.claim), ..open.clone() };
        let (f, _) = fires(&open_leaf, &sk, &p1.last().unwrap().head, &e.head, nibble_witness(&bad.to_bytes()));
        assert!(f && Search::open_fires(p1.last().unwrap(), &e), "a malformed opening");
    }
    println!("leaves: zk_open {} KB, zk_read_value {} KB, zk_correct_hash {} KB; peak {peak}", open_leaf.len() / 1000, rv1.len() / 1000, ch.len() / 1000);
    assert!(peak <= 1000);
}
