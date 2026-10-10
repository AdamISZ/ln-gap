//! The rules over moves from BitVMX's own search of hello-world (returns
//! 0 iff its input is 0x11111111), binary and 8-ary: each move signed
//! under its depth's one-time key, each rule run in the Script simulator
//! on the re-revealed signatures and compared with its native mirror.
//!
//! - A: an honest prover challenged anyway: no rule of the hub's fires on
//!   its final move, and its step proves;
//! - B: a prover faking one step's write: the search finds it, and it
//!   doesn't prove;
//! - C: an invalid input claimed as success: `halt_exit` fires;
//! - tampered moves, each aimed at one rule: the agreed step (`step`), a
//!   final hash (`equiv_*`), a choice out of range (`choice_<r>`), the
//!   initial hash (`initial`).

use std::collections::BTreeMap;
use std::path::PathBuf;

use bitcoin::script::Builder;
use bitvmx_cpu_definitions::trace::{TraceStep, TraceWrite};
use emulator::decision::challenge::{prover_execute, ForceCondition};
use emulator::executor::utils::{FailConfiguration, FailExecute};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_ladder::moves::{from_search, View};
use lngap_ladder::rules::*;
use lngap_ladder::script::{rule_wire, wots_wire, Msg};
use lngap_ladder::{Schedule, F_NEXT_HASH, F_STEP_HASH};
use lngap_lamport::winternitz::{WotsParams, WotsSecret};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::{final_step, search, Behaviour, Searched};
use lngap_zk::final_d60::{input_key_params, input_message, input_words, program_counter_wit};
use lngap_zk::game::Record;
use lngap_zk::FinalStep;

const VALID: [u8; 4] = [0x11; 4];
const INVALID: [u8; 4] = [0x11, 0x11, 0x11, 0x00];
const FAKE_STEP: u64 = 40;

fn hello() -> PathBuf {
    PathBuf::from(format!("{}/../zk/programs/hello-world.elf", env!("CARGO_MANIFEST_DIR")))
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("lngap-ladder-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

/// hello-world's program definition with an `nary`-ary search, its trace
/// hashed as a jump list if `jump`.
fn pdf(nary: u8, jump: bool) -> String {
    let d = scratch(&format!("pdf-{nary}-{jump}"));
    std::fs::copy(hello(), d.join("hello-world.elf")).unwrap();
    let p = d.join("hello.yaml");
    std::fs::write(&p, format!("elf: hello-world.elf\nnary_search: {nary}\nmax_steps: 2000\ninput_section_name: .input\njump_list: {jump}\ninputs:\n  - size: 4\n    owner: prover\n")).unwrap();
    p.display().to_string()
}

fn run(pdf: &str, name: &str, input: &[u8], prover: Behaviour, force: ForceCondition) -> Searched {
    let dir = scratch(name);
    let s = search(pdf, input, &dir, &prover, &Behaviour::default(), force).unwrap().expect("the verifier challenges");
    let _ = std::fs::remove_dir_all(&dir);
    s
}

/// Every step of an execution on `input`: `steps[i]` is step `i + 1`, its
/// `prev_hash` the hash after step `i`.
fn all_steps(pdf: &str, input: &[u8]) -> Vec<FinalStep> {
    let dir = scratch("all-steps");
    let d = format!("{}/", dir.display());
    let (_, last, hash) = prover_execute(pdf, input.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(pdf).unwrap();
    let (_, trace) = pd.execute_helper(&d, &d, input.to_vec(), Some((0..=last).collect()), None, false).unwrap();
    trace.windows(2).map(|w| final_step(&w[1].0, &w[0].1, &w[1].1, last, &hash).unwrap()).collect()
}

/// The hash after step `x` of an execution.
fn hash_after(steps: &[FinalStep], x: u64) -> [u8; 20] {
    steps[x as usize].prev_hash
}

/// Under a jump list: the hash the disputed step `t + 1` commits to for its
/// long jump.
fn jump_hash(s: &Schedule, steps: &[FinalStep], t: u32) -> Option<[u8; 20]> {
    s.jump.map(|j| hash_after(steps, j.jump(u64::from(t) + 1)))
}

/// The hub's witness for `program_counter` at agreed step `t >= 1`.
fn pc_wit(s: &Schedule, steps: &[FinalStep], t: usize) -> Vec<u8> {
    let prev = &steps[t - 1];
    match s.jump {
        None => program_counter_wit(&prev.prev_hash, &prev.write),
        Some(j) => {
            let jh = hash_after(steps, j.jump(t as u64));
            lngap_ladder::jhash::preimage(&prev.prev_hash, &jh, &prev.write, t as u32)[..53].to_vec()
        }
    }
}

fn fake_trace(pdf: &str, step: u64) -> bitvmx_cpu_definitions::trace::TraceRWStep {
    let dir = scratch("honest-trace");
    let d = format!("{}/", dir.display());
    prover_execute(pdf, VALID.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(pdf).unwrap();
    let mut t = pd.get_trace_step(&d, &d, VALID.to_vec(), step, None).unwrap();
    let w = t.trace_step.get_write();
    t.trace_step = TraceStep::new(TraceWrite::new(w.address, w.value ^ 0x100), t.trace_step.get_pc().clone());
    t
}

/// The parties' one-time keys: one per field of each move, one per input
/// word.
struct Keys {
    s: Schedule,
    moves: Vec<Vec<WotsSecret>>,
    words: Vec<WotsSecret>,
}

impl Keys {
    fn new(s: &Schedule, words: usize) -> Keys {
        let moves = (1..=s.depths())
            .map(|d| s.fields(d).iter().enumerate().map(|(f, (_, len))| WotsSecret::from_entropy(WotsParams::for_bytes(*len as u32), [d as u8, f as u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30])).collect())
            .collect();
        let words = (0..words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x80 + j as u8; 32])).collect();
        Keys { s: s.clone(), moves, words }
    }
    fn public(&self, m: Msg) -> lngap_lamport::winternitz::WotsPublic {
        match m {
            Msg::Field(d, f) => self.moves[(d - 1) as usize][f].public(),
            Msg::Word(j) => self.words[j].public(),
            Msg::Path(..) | Msg::Hop(_) => unreachable!("no tail here"),
        }
    }
    /// A field of a move, signed.
    fn sign(&self, msgs: &[Vec<u8>], d: u32, f: usize) -> lngap_lamport::winternitz::WotsSig {
        let (o, l) = self.s.fields(d)[f];
        self.moves[(d - 1) as usize][f].sign(&msgs[(d - 1) as usize][o..o + l]).unwrap()
    }
}

/// Does `rule` fire on these moves (and input words, and the poster's
/// witness)? (fires, peak stack)
fn fires(rule: &Rule, keys: &Keys, msgs: &[Vec<u8>], words: &[u32], wit: &[u8]) -> (bool, usize) {
    let script = rule.script(Builder::new(), &|m| keys.public(m));
    let reveals: Vec<Vec<Vec<u8>>> = rule
        .msgs
        .iter()
        .map(|m| match m {
            Msg::Field(d, f) => wots_wire(&keys.sign(msgs, *d, *f)),
            Msg::Word(j) => wots_wire(&keys.words[*j].sign(&input_message(words[*j])).unwrap()),
            Msg::Path(..) | Msg::Hop(_) => unreachable!("no tail here"),
        })
        .collect();
    let w = if rule.wit > 0 { wit.to_vec() } else { vec![] };
    spends(&script, rule_wire(&w, &reveals))
}

/// The mirror of each final rule on these moves.
fn mirror(s: &Schedule, info: &ProgramInfo, msgs: &[Vec<u8>], words: &[u32], wit: &[u8], name: &str) -> bool {
    let v = View { s, msgs };
    let (rec, sh, nh, choices) = (v.record(), v.step_hash(), v.next_hash(), v.choices());
    let (last_step, last_hash) = v.claim();
    let f = FinalStep {
        prev_hash: sh,
        read: rec.read,
        write: rec.write,
        hash: nh,
        witness: rec.witness,
        agreed_step: rec.step,
        last_step_1: rec.last_step_1,
        last_step_2: rec.last_step_2,
        claim_last_step: last_step,
        claim_last_hash: last_hash,
    };
    use lngap_zk::challenges as c;
    let last = u64::from(rec.step) + 1 == last_step;
    match name {
        "step" => step_fires(s, &rec, &choices),
        "initial" => initial_fires(&rec, &sh),
        "halt_hash" => last && nh != last_hash,
        "halt_exit" => last && !(rec.read.read_1_value == 93 && rec.read.read_2_value == 0 && rec.read.opcode == 0x73),
        "entry_point" => c::entry_point_fires(&f, info.entry),
        "program_counter" if s.jump.is_some() => {
            let pph: [u8; 20] = wit[..20].try_into().unwrap();
            let jh: [u8; 20] = wit[20..40].try_into().unwrap();
            let w = |i: usize| u32::from_be_bytes(wit[i..i + 4].try_into().unwrap());
            let pw = lngap_zk::Step { write_addr: w(40), write_value: w(44), pc: w(48), micro: wit[52] };
            lngap_ladder::jhash::step_hash_jump(&pph, &jh, &pw, rec.step) == sh && (pw.pc, pw.micro) != (rec.read.pc, rec.read.micro)
        }
        "program_counter" => {
            let pph: [u8; 20] = wit[..20].try_into().unwrap();
            let w = |i: usize| u32::from_be_bytes(wit[i..i + 4].try_into().unwrap());
            let pw = lngap_zk::Step { write_addr: w(20), write_value: w(24), pc: w(28), micro: wit[32] };
            c::program_counter_fires(&f, &pph, &pw)
        }
        "succ" => v.succ() != rec.step + 1,
        "addresses_sections" => c::addresses_fire(&f, info),
        "future_read_1" => c::future_read_fires(&f, 1),
        "future_read_2" => c::future_read_fires(&f, 2),
        "uninitialized_1" => c::uninitialized_fires(&f, 1, info),
        "uninitialized_2" => c::uninitialized_fires(&f, 2, info),
        n if n.starts_with("equiv_") => equiv_fires(s, u64::from(rec.step), &sh, &nh, &|r, i| v.hash(r, i)).iter().any(|x| x == n),
        n if n.starts_with("opcode_") => c::opcode_fires(&f, &info.code_chunks[n["opcode_".len()..].parse::<usize>().unwrap()]),
        n if n.starts_with("initialized_") => {
            let mut it = n["initialized_".len()..].split('_');
            let k: usize = it.next().unwrap().parse().unwrap();
            let r: u8 = it.next().unwrap().parse().unwrap();
            c::initialized_fires(&f, r, &info.data_chunks[k])
        }
        n if n.starts_with("input_") => {
            let j: usize = n["input_".len()..].parse().unwrap();
            lngap_zk::final_d60::input_fires(&rec, info, j, words[j])
        }
        _ => panic!("no mirror for {name}"),
    }
}

/// Every final rule on these moves: Script against the mirror; the names
/// that fire; the peak stack.
fn check_all(s: &Schedule, info: &ProgramInfo, rules: &[Rule], keys: &Keys, msgs: &[Vec<u8>], words: &[u32], wit: &[u8], what: &str) -> (Vec<String>, usize) {
    let mut fired = vec![];
    let mut peak = 0;
    for r in rules {
        let (f, p) = fires(r, keys, msgs, words, wit);
        assert_eq!(f, mirror(s, info, msgs, words, wit, &r.name), "{what}: {} in Script vs its mirror (peak {p})", r.name);
        if f {
            fired.push(r.name.clone());
            peak = peak.max(p);
        }
    }
    (fired, peak)
}

fn class_of(rec: &Record) -> String {
    lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap()
}

#[test]
fn rules_over_bitvmx_searches() {
    for (nary, jump) in [(2u8, false), (8, false), (2, true), (8, true)] {
        let pdf = pdf(nary, jump);
        let s = Schedule::load(&pdf).unwrap();
        let info = ProgramInfo::load(&pdf).unwrap();
        let words = input_words(&VALID);
        let keys = Keys::new(&s, info.input_words);
        let rules = final_rules(&s, &info);
        let proofs: BTreeMap<String, Rule> = prove_rules(&s, &info).into_iter().map(|r| (r.name.clone(), r)).collect();
        let steps = all_steps(&pdf, &VALID);
        let tag = format!("{nary}-ary{}", if jump { ", jump list" } else { "" });
        println!("LADDER {tag}: {} rounds, {} depths, {} final rules, {} proof classes", s.rounds(), s.depths(), rules.len(), proofs.len());

        // A: honest, challenged anyway
        let a = run(&pdf, &format!("A{nary}"), &VALID, Behaviour::default(), ForceCondition::ValidInputStepAndHash);
        let t = a.final_step.agreed_step as usize;
        let msgs = from_search(&s, &a, jump_hash(&s, &steps, t as u32).as_ref()).unwrap();
        let wit = if t >= 1 { pc_wit(&s, &steps, t) } else { vec![0; 53] };
        let (fired, peak) = check_all(&s, &info, &rules, &keys, &msgs, &words, &wit, "A");
        assert!(fired.is_empty(), "A: an honest final move fires {fired:?}");
        let v = View { s: &s, msgs: &msgs };
        let proof = &proofs[&format!("prove_{}", class_of(&v.record()))];
        let (ok, ppeak) = fires(proof, &keys, &msgs, &words, &[]);
        assert!(ok, "A: the honest step proves (peak {ppeak})");
        println!("LADDER {tag} A: step {} agreed, {}; no rule fires; {} proves (peak {ppeak})", t, proof.name, proof.name);
        let _ = peak;

        // tampered: the agreed step
        let m = s.depths() as usize - 1;
        let mut bad = msgs.clone();
        bad[m][lngap_zk::game::R_STEP + 3] ^= 1;
        let (fired, p) = check_all(&s, &info, &rules, &keys, &bad, &words, &wit, "A, step altered");
        println!("LADDER {tag}: a wrong agreed step fires {fired:?} (peak {p})");
        assert!(fired.contains(&"step".to_string()), "a wrong agreed step: {fired:?}");
        // tampered: each final hash
        for (off, kind) in [(F_STEP_HASH, "equiv_step_"), (F_NEXT_HASH, "equiv_next_")] {
            let mut bad = msgs.clone();
            bad[m][off] ^= 0x80;
            let (fired, p) = check_all(&s, &info, &rules, &keys, &bad, &words, &wit, kind);
            println!("LADDER {tag}: a changed final hash fires {fired:?} (peak {p})");
            assert!(fired.iter().any(|f| f.starts_with(kind)), "a changed {kind} hash: {fired:?}");
            assert!(!fired.contains(&"step".to_string()));
        }
        // a choice out of range, and in range
        for r in 1..=s.rounds() {
            let rule = choice_rule(&s, r);
            for byte in [0u8, (s.segments(r) - 1) as u8, s.segments(r) as u8, 0x10] {
                let mut mm = msgs.clone();
                mm[2 * r as usize - 1] = vec![byte];
                let (f, _) = fires(&rule, &keys, &mm, &words, &[]);
                assert_eq!(f, choice_fires(&s, r, byte) || byte >= 16, "choice_{r} on {byte}");
            }
        }
        // the initial hash at agreed step 0
        let rule = initial_rule(&s);
        for (h, should) in [(lngap_zk::game::initial_hash(), false), ([7u8; 20], true)] {
            let mut mm = msgs.clone();
            mm[m][lngap_zk::game::R_STEP..lngap_zk::game::R_STEP + 4].copy_from_slice(&[0; 4]);
            mm[m][F_STEP_HASH..F_STEP_HASH + 20].copy_from_slice(&h);
            assert_eq!(fires(&rule, &keys, &mm, &words, &[]).0, should, "initial");
        }

        if jump {
            // the disputed step's number, signed wrong
            let mut mm = msgs.clone();
            mm[m][lngap_ladder::F_SUCC + 3] ^= 1;
            let (fired, _) = check_all(&s, &info, &rules, &keys, &mm, &words, &wit, "succ altered");
            assert_eq!(fired, vec!["succ".to_string()], "a wrong successor");
            // a wrong long-jump hash: the honest step no longer proves
            let mut mm = msgs.clone();
            mm[m][lngap_ladder::F_JUMP_HASH] ^= 1;
            assert!(!fires(proof, &keys, &mm, &words, &[]).0, "a wrong J doesn't prove the honest write");
            // the program counter with a wrong pc read
            let mut mm = msgs.clone();
            mm[m][lngap_zk::game::R_PC + 3] ^= 4;
            let (fired, p) = check_all(&s, &info, &rules, &keys, &mm, &words, &wit, "pc read altered");
            assert!(fired.contains(&"program_counter".to_string()), "a wrong pc read: {fired:?}");
            println!("LADDER {tag}: succ, J and pc tampers caught (pc peak {p})");
        }

        // B: a faked write
        let fake = fake_trace(&pdf, FAKE_STEP);
        let b_fail = FailConfiguration { fail_execute: Some(FailExecute { step: FAKE_STEP, fake_trace: fake.clone() }), ..Default::default() };
        let b = run(&pdf, &format!("B{nary}"), &VALID, Behaviour { fail: Some(b_fail) }, ForceCondition::ValidInputWrongStepOrHash);
        let msgs_b = from_search(&s, &b, jump_hash(&s, &steps, b.final_step.agreed_step).as_ref()).unwrap();
        let vb = View { s: &s, msgs: &msgs_b };
        assert_eq!(u64::from(vb.record().step) + 1, FAKE_STEP, "B: the search finds the faked step");
        let proof = &proofs[&format!("prove_{}", class_of(&vb.record()))];
        assert!(!fires(proof, &keys, &msgs_b, &words, &[]).0, "B: a faked step doesn't prove");

        // C: an invalid input claimed as success
        let c = run(&pdf, &format!("C{nary}"), &INVALID, Behaviour::default(), ForceCondition::No);
        let steps_c = all_steps(&pdf, &INVALID);
        let msgs_c = from_search(&s, &c, jump_hash(&s, &steps_c, c.final_step.agreed_step).as_ref()).unwrap();
        let (fired, p) = check_all(&s, &info, &rules, &keys, &msgs_c, &input_words(&INVALID), &wit, "C");
        println!("LADDER {tag} C: {fired:?} (peak {p})");
        assert!(fired.contains(&"halt_exit".to_string()), "C: {fired:?}");
        println!("LADDER {tag} B: step {FAKE_STEP} found, doesn't prove; C: {fired:?}");
    }
}
