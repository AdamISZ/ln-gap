//! `lngap-zk-demo`: a narrated dispute over a RISC-V computation, for the
//! talks (DEMOS_PLAN.md section 3). Two parties disagree about a program's
//! execution; BitVMX's n-ary search between them narrows the dispute to
//! one step; the step is resolved on a regtest node through the final
//! step's output (D59): the prover proves it after delta, or the claimant
//! takes the output after delta + delta'.
//!
//! ```text
//!   lngap-zk-demo hello honest            # a correct claim, challenged anyway
//!   lngap-zk-demo hello fake <step>       # the prover fakes one step's write
//!   lngap-zk-demo hello bad-input         # a failing input, success claimed
//!   lngap-zk-demo groth16 <dir> honest    # BitVMX's Groth16 verifier, a genuine proof
//!   lngap-zk-demo groth16 <dir> tampered  # ... a tampered proof, acceptance claimed
//! ```
//!
//! `<dir>` holds `groth16.yaml`, the ELF it names and `input.hex`
//! (DEMOS_PLAN.md, 2026-09-30); a Groth16 dispute takes about 5.5 minutes.

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use anyhow::{anyhow, bail, Result};
use bitcoin::key::Keypair;
use bitcoin::Amount;
use bitvmx_cpu_definitions::trace::{TraceStep, TraceWrite};
use emulator::decision::challenge::{prover_execute, ForceCondition};
use emulator::executor::utils::{FailConfiguration, FailExecute};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_pos::instance::mover_at;
use lngap_pos::refute::pair_key;
use lngap_pos::ttt::Layout;
use lngap_zk::chain::FinalOutput;
use lngap_zk::dispute::{search, Behaviour, Searched};
use lngap_zk::{prove_leaf, step_hash, FinalStep};

const GAME: u16 = 1;
const D: u32 = 2;
const DELTA: u16 = 2;
const DELTA_PRIME: u16 = 3;

fn usage() -> ! {
    eprintln!("usage:\n  lngap-zk-demo hello honest | fake <step> | bad-input\n  lngap-zk-demo groth16 <dir> honest | tampered");
    std::process::exit(2)
}

fn say(s: impl AsRef<str>) {
    println!("{}", s.as_ref());
}

fn short(h: &str) -> String {
    format!("{}..", &h[..h.len().min(12)])
}

fn scratch(name: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("lngap-zk-demo-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

struct Case {
    pdf: String,
    input: Vec<u8>,
    prover: Behaviour,
    force: ForceCondition,
    story: String,
}

fn hello_pdf() -> String {
    format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn case(args: &[String]) -> Result<Case> {
    let a = |i: usize| args.get(i).map(String::as_str);
    Ok(match (a(0), a(1)) {
        (Some("hello"), Some("honest")) => Case {
            pdf: hello_pdf(),
            input: vec![0x11; 4],
            prover: Behaviour::default(),
            force: ForceCondition::ValidInputStepAndHash,
            story: "hello-world returns 0 iff its input is 0x11111111. The prover runs it on 0x11111111 and claims success; the verifier challenges anyway (a dishonest challenger).".into(),
        },
        (Some("hello"), Some("fake")) => {
            let step: u64 = a(2).and_then(|s| s.parse().ok()).unwrap_or_else(|| usage());
            Case {
                pdf: hello_pdf(),
                input: vec![0x11; 4],
                prover: Behaviour { fail: Some(fake(step)?) },
                force: ForceCondition::ValidInputWrongStepOrHash,
                story: format!("hello-world on 0x11111111, but the prover reports a wrong write at step {step}, so its claimed final hash is not the true one (BitVMX's fault injection: after the fake write the prover's own run derails, and it claims success wherever that run stops). The verifier challenges it."),
            }
        }
        (Some("hello"), Some("bad-input")) => Case {
            pdf: hello_pdf(),
            input: vec![0x11, 0x11, 0x11, 0x00],
            prover: Behaviour::default(),
            force: ForceCondition::No,
            story: "hello-world on 0x11111100, which returns 1; the prover claims success anyway. The verifier challenges it.".into(),
        },
        (Some("groth16"), Some(dir)) => {
            let input = hex::decode(std::fs::read_to_string(format!("{dir}/input.hex"))?.trim())?;
            match a(2) {
                Some("honest") => Case {
                    pdf: format!("{dir}/groth16.yaml"),
                    input,
                    prover: Behaviour::default(),
                    force: ForceCondition::ValidInputStepAndHash,
                    story: "BitVMX's Groth16 verifier (RISC-V, about 479 million steps) on a genuine RISC0 proof, which it accepts. The prover claims acceptance; the verifier challenges anyway.".into(),
                },
                Some("tampered") => {
                    let mut bad = input;
                    bad[4 + 32 + 5] ^= 1;
                    Case {
                        pdf: format!("{dir}/groth16.yaml"),
                        input: bad,
                        prover: Behaviour::default(),
                        force: ForceCondition::No,
                        story: "BitVMX's Groth16 verifier on the same proof with one bit flipped, which it rejects. The prover claims acceptance anyway; the verifier challenges.".into(),
                    }
                }
                _ => usage(),
            }
        }
        _ => usage(),
    })
}

/// A prover that reports hello-world's `step` with its write value altered.
fn fake(step: u64) -> Result<FailConfiguration> {
    let dir = scratch("honest-trace");
    let d = format!("{}/", dir.display());
    prover_execute(&hello_pdf(), vec![0x11; 4], &d, &d, true, None, false).map_err(|e| anyhow!("{e}"))?;
    let pd = ProgramDefinition::from_config(&hello_pdf())?;
    let mut t = pd.get_trace_step(&d, &d, vec![0x11; 4], step, None).map_err(|e| anyhow!("{e}"))?;
    let _ = std::fs::remove_dir_all(&dir);
    let w = t.trace_step.get_write();
    t.trace_step = TraceStep::new(TraceWrite::new(w.address, w.value ^ 0x100), t.trace_step.get_pc().clone());
    Ok(FailConfiguration { fail_execute: Some(FailExecute { step, fake_trace: t }), ..Default::default() })
}

fn narrate_search(pdf: &str, s: &Searched) -> Result<()> {
    let nary = ProgramDefinition::from_config(pdf)?.nary_def();
    say(format!("\n== The search ({}-ary, {} rounds over a trace padded to {} steps) ==", nary.nary, nary.total_rounds(), nary.max_steps));
    say("   On the venue each round is two moves: the prover's hashes, then the verifier's choice.");
    let mut base = 0u64;
    for (i, (hashes, choice)) in s.rounds.iter().enumerate() {
        let round = i as u8 + 1;
        let points = nary.required_steps(round, base);
        let width = if round < nary.total_rounds() { points.get(1).zip(points.first()).map(|(b, a)| b - a).unwrap_or(1) } else { 1 };
        say(format!(
            "   round {round:2}: steps {base}..{}: the prover hashes {} points ({} ...); the verifier picks segment {choice}",
            base + width * u64::from(nary.hashes_for_round(round) + 1),
            hashes.len(),
            hashes.first().map(|h| short(h)).unwrap_or_default()
        ));
        base = nary.step_from_base_and_bits(round, base, *choice);
    }
    say(format!("   the verifier's choices say: agreed after step {}, disputed after step {}. The disputed step is {}.", s.step - 1, s.step, s.step));
    Ok(())
}

fn narrate_step(f: &FinalStep) {
    let ins = riscv_decode::decode(f.read.opcode).map(|i| format!("{i:?}")).unwrap_or_else(|_| "undecodable".into());
    say("\n== The disputed step, as the prover reveals it (the final pair of heads) ==");
    say(format!("   pc {:#010x}, opcode {:#010x}: {ins}", f.read.pc, f.read.opcode));
    say(format!("   reads: [{:#010x}] = {:#010x}, [{:#010x}] = {:#010x}", f.read.read_1_addr, f.read.read_1_value, f.read.read_2_addr, f.read.read_2_value));
    say(format!("   write: [{:#010x}] = {:#010x}, next pc {:#010x}", f.write.write_addr, f.write.write_value, f.write.pc));
    say(format!("   hash before (agreed) {}, after (the prover's) {}", hex::encode(f.prev_hash), hex::encode(f.hash)));
    let chained = step_hash(&f.prev_hash, &f.write) == f.hash;
    say(format!("   BLAKE3(before || write) {} the prover's hash", if chained { "is" } else { "is NOT" }));
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let c = case(&args)?;
    let t0 = Instant::now();
    say("== The claim ==");
    say(format!("   {}", c.story));
    let dir = scratch("search");
    let s = search(&c.pdf, &c.input, &dir, &c.prover, &Behaviour::default(), c.force)?;
    let _ = std::fs::remove_dir_all(&dir);
    let Some(s) = s else {
        say("   the verifier agrees with the claim: no dispute");
        return Ok(());
    };
    say(format!("   the prover's claim: the program halts with 0 at step {}, final trace hash {}", s.claim.1, short(&s.claim.2)));
    say(format!("   ({:.1?} of emulation so far)", t0.elapsed()));
    narrate_search(&c.pdf, &s)?;
    narrate_step(&s.final_step);

    // the final step's output on a regtest node
    say("\n== On Bitcoin (regtest) ==");
    let rt = Regtest::start()?;
    let pair = pair_key([0x5a; 32]);
    let prover: Keypair = Seed::from_label("zk demo prover").keypair("pay");
    let claimant: Keypair = Seed::from_label("zk demo claimant").keypair("pay");
    let f = s.final_step;
    let ins = riscv_decode::decode(f.read.opcode).map_err(|e| anyhow!("undecodable opcode: {e:?}"))?;
    let proof = prove_leaf(&Layout::at(D, GAME, mover_at(D)), &pair.public(), &ins, f.read.micro, Arc::new(|_, _| true));
    let out = FinalOutput::new(&proof, &prover, &claimant, DELTA, DELTA_PRIME)?;
    say("   (the claim and the refutation that parks the final pair are the graph's usual first two transactions; here the refuted output is funded directly)");
    say(format!(
        "   the refuted output has two leaves: {} ({} B, after {} blocks: the claimant's disproves come first) and timeout (the claimant's, after {} blocks)",
        out.prove_name,
        out.prove.len(),
        out.prove_after(),
        out.timeout_after()
    ));
    let (op, prev) = rt.fund(&out.tree.script_pubkey(), Amount::from_sat(1_000_000))?;
    rt.mine(u64::from(out.prove_after()))?;
    let (prior, new) = (f.prior_head(GAME, D - 1, mover_at(D - 1)), f.new_head(GAME, D, mover_at(D)));
    let proof_tx = out.prove_tx(op, &prev, out.pay_back(Amount::from_sat(990_000)), &prover, &pair, &f, &prior, &new)?;
    match rt.test_accept(&proof_tx) {
        Ok(_) => {
            let (txid, h) = rt.send_and_confirm(&proof_tx)?;
            say(format!("   the prover PROVES step {}: BitVMX's check for its instruction passes, and the hash chains", s.step));
            say(format!("   {txid} confirmed at height {h}: {} vB. The prover wins.", proof_tx.vsize()));
        }
        Err(e) => {
            say(format!("   the prover cannot prove step {}: the node rejects the proof ({e})", s.step));
            rt.mine(u64::from(DELTA_PRIME))?;
            let to = out.timeout_tx(op, &prev, out.pay_back(Amount::from_sat(990_000)), &claimant)?;
            let (txid, h) = rt.send_and_confirm(&to)?;
            say(format!("   after {} blocks the claimant takes the output: {txid} at height {h}, {} vB. The verifier wins.", out.timeout_after(), to.vsize()));
        }
    }
    say(format!("\n   on chain: the refutation that parks the pair, then one transaction; {:.1?} in all", t0.elapsed()));
    if s.step == 0 {
        bail!("unexpected: step 0");
    }
    Ok(())
}
