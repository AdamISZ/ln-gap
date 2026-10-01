//! Z3 step 2: the search played as a channel game (D60), natively. Z2's
//! scenarios on hello-world, searched by BitVMX's decision module with
//! binary search (11 rounds, 23 depths), turned into the game's entries:
//!
//! - every entry's body opens its head (the members' check);
//! - no bookkeeping rule fires on the honest bookkeeping of any scenario
//!   (the claim, every choice, every copied state);
//! - the final state's endpoints are the search's (lo, hi); the D60 prove
//!   leaf proves A's final step and not B's (a faked write) or C's (a
//!   failing halt);
//! - each malformation fires its rule, and a body that doesn't open its
//!   head is refused by the members' check.

use std::path::PathBuf;

use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::instruction_mapping::{generate_verification_script, get_key_from_instruction_and_micro, requires_witness};
use bitvmx_cpu_definitions::trace::{TraceStep, TraceWrite};
use emulator::decision::challenge::{prover_execute, ForceCondition};
use emulator::executor::utils::{FailConfiguration, FailExecute};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_lamport::winternitz::WotsSecret;
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{disprove_witness, pair_key};
use lngap_pos::ttt::Layout;
use lngap_zk::dispute::{search, Behaviour, Searched};
use lngap_zk::game::*;
use lngap_zk::BASE_REGISTER_ADDRESS;

const GAME: u16 = 1;
const VALID: [u8; 4] = [0x11; 4];
const INVALID: [u8; 4] = [0x11, 0x11, 0x11, 0x00];
const FAKE_STEP: u64 = 40;

fn pdf() -> String {
    format!("{}/programs/hello-world-binary.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("lngap-zk-play-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn run(name: &str, input: &[u8], prover: Behaviour, force: ForceCondition) -> Searched {
    let dir = scratch(name);
    let s = search(&pdf(), input, &dir, &prover, &Behaviour::default(), force).unwrap().expect("the verifier challenges");
    let _ = std::fs::remove_dir_all(&dir);
    s
}

fn fake_trace(step: u64) -> bitvmx_cpu_definitions::trace::TraceRWStep {
    let dir = scratch("honest-trace");
    let d = format!("{}/", dir.display());
    prover_execute(&pdf(), VALID.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(&pdf()).unwrap();
    let mut t = pd.get_trace_step(&d, &d, VALID.to_vec(), step, None).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let w = t.trace_step.get_write();
    t.trace_step = TraceStep::new(TraceWrite::new(w.address, w.value ^ 0x100), t.trace_step.get_pc().clone());
    t
}

/// Does the final entry prove (the D60 prove leaf in the simulator)?
fn proves(sk: &WotsSecret, search: &Search, prior: &Entry, last: &Entry) -> bool {
    let r = last.record.unwrap();
    let Ok(ins) = riscv_decode::decode(r.read.opcode) else { return false };
    let Some(key) = std::panic::catch_unwind(|| get_key_from_instruction_and_micro(&ins, r.read.micro)).ok() else { return false };
    let d = search.depths();
    let l = Layout::at(d, GAME, mover_at(d));
    let exec = generate_verification_script(&ins, r.read.micro, BASE_REGISTER_ADDRESS, requires_witness(&ins));
    let script = prove_script_d60(&l, &sk.public(), &key, &ScriptBuf::from_bytes(exec.into_bytes()), requires_witness(&ins));
    let mut w = final_witness(&last.state, &r);
    w.extend(disprove_witness(&sk.sign(&[prior.head.as_slice(), last.head.as_slice()].concat()).unwrap()));
    matches!(lngap_script32::sim::run(script.as_script(), w), Ok(st) if st.len() == 1 && st[0] == [1])
}

/// The checks every honestly kept game passes.
fn bookkeeping_holds(name: &str, search: &Search, s: &Searched, entries: &[Entry]) {
    assert_eq!(entries.len() as u32, search.depths(), "{name}: depths");
    for e in entries {
        assert!(search.body_opens(e.depth, &e.head, &e.body()), "{name}: depth {} body", e.depth);
        assert_eq!(e.head[..4], lngap_pos::ttt::word0(GAME, e.depth, mover_at(e.depth)).to_be_bytes(), "{name}: word0");
    }
    assert!(!Search::claim_fires(&entries[0], &entries[0].claim.unwrap()), "{name}: claim");
    for w in entries.windows(2) {
        let (p, n) = (&w[0], &w[1]);
        if n.depth % 2 == 0 {
            assert!(!search.choice_fires(p, n), "{name}: choice at depth {}", n.depth);
        } else {
            assert!(!Search::copied_fires(&p.head, &n.head), "{name}: copied at depth {}", n.depth);
        }
    }
    let last = entries.last().unwrap();
    assert_eq!((last.state.lo, last.state.hi), (s.final_step.prev_hash, s.final_step.hash), "{name}: the endpoints are the search's");
    assert_eq!(last.state.base as u64 + 1, s.step, "{name}: the disputed step");
}

#[test]
fn games_from_searches() {
    let sk = pair_key([51; 32]);
    let rounds = ProgramDefinition::from_config(&pdf()).unwrap().nary_def().total_rounds() as u32;
    let search_ = Search { game_id: GAME, rounds };
    println!("binary search: {rounds} rounds, {} depths", search_.depths());

    let a = run("A", &VALID, Behaviour::default(), ForceCondition::ValidInputStepAndHash);
    let fake = fake_trace(FAKE_STEP);
    let b_fail = FailConfiguration { fail_execute: Some(FailExecute { step: FAKE_STEP, fake_trace: fake }), ..Default::default() };
    let b = run("B", &VALID, Behaviour { fail: Some(b_fail) }, ForceCondition::ValidInputWrongStepOrHash);
    let c = run("C", &INVALID, Behaviour::default(), ForceCondition::No);
    for (name, s, should_prove) in [("A", &a, true), ("B", &b, false), ("C", &c, false)] {
        let entries = play(s, &search_).unwrap();
        bookkeeping_holds(name, &search_, s, &entries);
        let n = entries.len();
        let proved = proves(&sk, &search_, &entries[n - 2], &entries[n - 1]);
        println!("{name}: disputed step {}, choices {:?}, final step proves: {proved}", s.step, s.rounds.iter().map(|r| r.1).collect::<Vec<_>>());
        assert_eq!(proved, should_prove, "{name}");
    }

    // malformations, on A's game
    let e = play(&a, &search_).unwrap();
    // the claim: a wrong initial hash, a wrong hi, a nonzero base
    let c0 = e[0].claim.unwrap();
    for bad in [State { lo: [1; 20], ..e[0].state }, State { hi: [2; 20], ..e[0].state }, State { base: 4, ..e[0].state }] {
        assert!(Search::claim_fires(&Entry { state: bad, ..e[0].clone() }, &c0));
    }
    // a choice: endpoints not copied, the wrong bit, the claim changed
    let (p, n) = (&e[2], &e[3]);
    let r = n.depth / 2;
    for bad in [
        State { lo: [3; 20], ..n.state },
        State { hi: [4; 20], ..n.state },
        State { base: n.state.base ^ search_.bit(r), ..n.state },
        State { base: n.state.base ^ search_.bit(r + 1), ..n.state },
        State { claim: [5; 20], ..n.state },
    ] {
        assert!(search_.choice_fires(p, &Entry { state: bad, ..n.clone() }), "a malformed choice at depth {}", n.depth);
    }
    // a midpoint move that changes the state
    let mut h = e[4].head;
    h[4 + H_STATE] ^= 1;
    assert!(Search::copied_fires(&e[3].head, &h));
    // the members' check: a body that doesn't open, or is the wrong length
    let mut body = e[5].body();
    body[0] ^= 1;
    assert!(!search_.body_opens(e[5].depth, &e[5].head, &body));
    assert!(!search_.body_opens(1, &e[0].head, &e[0].state.to_bytes()));
    let last = e.last().unwrap();
    let mut body = last.body();
    body[BLOCK] ^= 1;
    assert!(!search_.body_opens(last.depth, &last.head, &body), "the final record must open the head's digest");
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

/// Run a bookkeeping leaf: (fires, peak).
fn fires(script: &ScriptBuf, sk: &WotsSecret, prior: &[u8; 48], new: &[u8; 48], below: Vec<Vec<u8>>) -> (bool, usize) {
    let msg: Vec<u8> = if new[..4] == lngap_pos::ttt::word0(GAME, 1, mover_at(1)).to_be_bytes() { new.to_vec() } else { [prior.as_slice(), new.as_slice()].concat() };
    let mut w = below;
    w.extend(disprove_witness(&sk.sign(&msg).unwrap()));
    match lngap_script32::sim::run_peak(script.as_script(), w) {
        Ok((st, peak)) => (st.len() == 1 && truthy(&st[0]), peak),
        Err(_) => (false, 0),
    }
}

fn nib(b: &[u8]) -> Vec<Vec<u8>> {
    lngap_zk::nibble_witness(b)
}

/// Script == mirror for every bookkeeping leaf over whole games, honest
/// and malformed.
#[test]
fn bookkeeping_leaves_match_mirrors() {
    let rounds = ProgramDefinition::from_config(&pdf()).unwrap().nary_def().total_rounds() as u32;
    let sr = Search { game_id: GAME, rounds };
    let a = run("A2", &VALID, Behaviour::default(), ForceCondition::ValidInputStepAndHash);
    let c = run("C2", &INVALID, Behaviour::default(), ForceCondition::No);
    // keys: the claim's single-head key at depth 1, pair keys after
    let sk1 = lngap_lamport::winternitz::WotsSecret::from_entropy(lngap_lamport::winternitz::WotsParams::for_bytes(48), [61; 32]);
    let sk = pair_key([62; 32]);
    let claim_leaf = sr.claim_leaf(&sk1.public());
    let mut peak = 0;
    let (mut fired, mut held) = (0, 0);
    let mut tally = |f: bool| if f { fired += 1 } else { held += 1 };
    for s in [&a, &c] {
        let e = play(s, &sr).unwrap();
        // the claim
        let c0 = e[0].claim.unwrap();
        let claim_cases = [e[0].state, State { lo: [1; 20], ..e[0].state }, State { hi: [2; 20], ..e[0].state }, State { base: 1 << 20, ..e[0].state }];
        for st in claim_cases {
            let en = Entry { state: st, head: head(GAME, 1, mover_at(1), &st.digest(), &e[0].second()), ..e[0].clone() };
            let (f, pk) = fires(&claim_leaf, &sk1, &[0; 48], &en.head, [nib(&st.to_bytes()), nib(&c0.to_bytes())].concat());
            assert_eq!(f, Search::claim_fires(&en, &c0), "claim: script vs mirror");
            peak = peak.max(pk);
            tally(f);
        }
        // a claim block that doesn't open the state's claim: never fires
        let bad_state = State { lo: [1; 20], ..e[0].state };
        let other = Claim { last_step: 9, ..c0 };
        let en = head(GAME, 1, mover_at(1), &bad_state.digest(), &e[0].second());
        assert!(!fires(&claim_leaf, &sk1, &[0; 48], &en, [nib(&bad_state.to_bytes()), nib(&other.to_bytes())].concat()).0);

        for w in e.windows(2) {
            let (p, n) = (&w[0], &w[1]);
            if n.depth == sr.depths() {
                continue; // the final move: D59's output
            }
            if n.depth % 2 == 0 {
                let leaf = sr.choice_leaf(&sk.public(), n.depth);
                let r = n.depth / 2;
                let variants = [
                    n.state,
                    State { lo: [3; 20], ..n.state },
                    State { hi: [4; 20], ..n.state },
                    State { base: n.state.base ^ sr.bit(r), ..n.state },
                    State { base: n.state.base ^ 1, ..n.state },
                    State { claim: [5; 20], ..n.state },
                    // the other half, kept well-formed: legal too
                    if n.state.lo == p.state.lo {
                        State { lo: p.second(), hi: p.state.hi, base: p.state.base | sr.bit(r), ..n.state }
                    } else {
                        State { lo: p.state.lo, hi: p.second(), base: p.state.base, ..n.state }
                    },
                ];
                for (i, st) in variants.iter().enumerate() {
                    let nn = Entry { state: *st, head: head(GAME, n.depth, mover_at(n.depth), &st.digest(), &[0; 20]), ..n.clone() };
                    let (f, pk) = fires(&leaf, &sk, &p.head, &nn.head, [nib(&p.state.to_bytes()), nib(&st.to_bytes())].concat());
                    assert_eq!(f, sr.choice_fires(p, &nn), "choice at depth {} variant {i}: script vs mirror", n.depth);
                    // (where the midpoint equals an endpoint, as past the
                    // last step where BitVMX pads the hashes, both halves
                    // coincide and a flipped bit is the other legal choice)
                    if p.second() != p.state.lo && p.second() != p.state.hi {
                        assert_eq!(f, (1..6).contains(&i), "choice at depth {} variant {i}", n.depth);
                    }
                    peak = peak.max(pk);
                    tally(f);
                }
                // a malformed state that doesn't open the new head: no fire
                let st = State { lo: [3; 20], ..n.state };
                assert!(!fires(&leaf, &sk, &p.head, &n.head, [nib(&p.state.to_bytes()), nib(&st.to_bytes())].concat()).0);
            } else {
                let leaf = sr.copied_leaf(&sk.public(), n.depth);
                let mut bad = n.head;
                bad[4 + H_STATE + 7] ^= 0x10;
                for h in [n.head, bad] {
                    let (f, pk) = fires(&leaf, &sk, &p.head, &h, vec![]);
                    assert_eq!(f, Search::copied_fires(&p.head, &h), "copied at depth {}", n.depth);
                    peak = peak.max(pk);
                    tally(f);
                }
            }
        }
    }
    println!(
        "bookkeeping leaves: {fired} fired, {held} held; peak {peak}; choice leaf {} B, claim leaf {} B, copied leaf {} B",
        sr.choice_leaf(&sk.public(), 2).len(),
        claim_leaf.len(),
        sr.copied_leaf(&sk.public(), 3).len()
    );
    assert!(peak <= 1000);
}

/// On regtest, behind the claimant's key: each bookkeeping disprove spends
/// against a malformed move and is rejected against the honest one.
#[test]
fn bookkeeping_leaves_on_regtest() {
    use bitcoin::key::Keypair;
    use bitcoin::script::Builder;
    use bitcoin::{Amount, TxOut};
    use lngap_btc::keys::{xonly, Seed};
    use lngap_btc::regtest::Regtest;
    use lngap_btc::script::BuilderExt;
    use lngap_btc::sighash::sign_tapscript;
    use lngap_btc::taptree::{Leaf, TapTree};
    use lngap_btc::tx::{build_spend, Timelock};
    use lngap_btc::witness::tapscript_witness;

    let rt = Regtest::start().unwrap();
    let claimant: Keypair = Seed::from_label("d60 claimant").keypair("pay");
    let rounds = ProgramDefinition::from_config(&pdf()).unwrap().nary_def().total_rounds() as u32;
    let sr = Search { game_id: GAME, rounds };
    let a = run("A3", &VALID, Behaviour::default(), ForceCondition::ValidInputStepAndHash);
    let e = play(&a, &sr).unwrap();
    let sk1 = lngap_lamport::winternitz::WotsSecret::from_entropy(lngap_lamport::winternitz::WotsParams::for_bytes(48), [63; 32]);
    let sk = pair_key([64; 32]);
    let spend = |leaf: &ScriptBuf, key: &WotsSecret, msg: Vec<u8>, below: Vec<Vec<u8>>| {
        let mut b = Builder::new().checksigverify(&xonly(&claimant)).into_script().into_bytes();
        b.extend_from_slice(leaf.as_bytes());
        let script = ScriptBuf::from_bytes(b);
        let tree = TapTree::new(vec![Leaf::new("d", script.clone(), Timelock::NONE)]).unwrap();
        let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
        let sig = sign_tapscript(&claimant, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
        let mut w = below;
        w.extend(disprove_witness(&key.sign(&msg).unwrap()));
        w.push(sig.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &script, &tree.control_block("d").unwrap());
        tx
    };
    // zk_choice at depth 4: the new lo not copied
    let (p, n) = (&e[2], &e[3]);
    let leaf = sr.choice_leaf(&sk.public(), n.depth);
    let bad = State { lo: [7; 20], ..n.state };
    let bh = head(GAME, n.depth, mover_at(n.depth), &bad.digest(), &[0; 20]);
    let err = rt.test_accept(&spend(&leaf, &sk, [p.head, n.head].concat(), [nib(&p.state.to_bytes()), nib(&n.state.to_bytes())].concat())).expect_err("honest");
    let tx = spend(&leaf, &sk, [p.head, bh].concat(), [nib(&p.state.to_bytes()), nib(&bad.to_bytes())].concat());
    let (txid, h) = rt.send_and_confirm(&tx).unwrap();
    println!("zk_choice: {txid} at {h}, {} vB; honest rejected ({err})", tx.vsize());
    // zk_claim: a wrong initial hash
    let leaf = sr.claim_leaf(&sk1.public());
    let c0 = e[0].claim.unwrap();
    let bad = State { lo: [8; 20], ..e[0].state };
    let bh = head(GAME, 1, mover_at(1), &bad.digest(), &e[0].second());
    let err = rt.test_accept(&spend(&leaf, &sk1, e[0].head.to_vec(), [nib(&e[0].state.to_bytes()), nib(&c0.to_bytes())].concat())).expect_err("honest");
    let tx = spend(&leaf, &sk1, bh.to_vec(), [nib(&bad.to_bytes()), nib(&c0.to_bytes())].concat());
    let (txid, h) = rt.send_and_confirm(&tx).unwrap();
    println!("zk_claim: {txid} at {h}, {} vB; honest rejected ({err})", tx.vsize());
    // zk_copied at depth 5: the state digest changed
    let (p, n) = (&e[3], &e[4]);
    let leaf = sr.copied_leaf(&sk.public(), n.depth);
    let mut bh = n.head;
    bh[4 + H_STATE] ^= 1;
    let err = rt.test_accept(&spend(&leaf, &sk, [p.head, n.head].concat(), vec![])).expect_err("honest");
    let tx = spend(&leaf, &sk, [p.head, bh].concat(), vec![]);
    let (txid, h) = rt.send_and_confirm(&tx).unwrap();
    println!("zk_copied: {txid} at {h}, {} vB; honest rejected ({err})", tx.vsize());
}
