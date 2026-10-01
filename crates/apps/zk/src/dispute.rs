//! Z2: a disputed execution between two in-process parties, narrowed to
//! one step by BitVMX's n-ary search (their `decision` module, unchanged),
//! and handed to the final-step output of D59.
//!
//! The sequence is BitVMX's: the prover executes and claims `Halt(0)` at
//! its last step with its last hash; the verifier re-executes and decides
//! whether to challenge; they alternate rounds (the prover's hashes at
//! the round's points, the verifier's choice of segment); then the prover
//! reveals the full trace of the first step they disagree on, with the
//! agreed hash before it and its own hash after. BitVMX would then run
//! the prover's execution proof and the verifier's other challenges; here
//! the step becomes a [`FinalStep`], whose proof is `zk_prove_<class>`.
//!
//! The rounds run in-process. On the venue they would be the game's
//! moves; that needs heads larger than 48 bytes (a round carries three
//! 20-byte hashes), which is the graph integration's work, not this one.

use std::path::Path;

use anyhow::{anyhow, bail, Result};
use bitvmx_cpu_definitions::trace::TraceRWStep;
use emulator::decision::challenge::{prover_execute, prover_final_trace, prover_get_hashes_for_round, verifier_check_execution, verifier_choose_segment, ForceCondition};
use emulator::decision::nary_search::NArySearchType;
use emulator::executor::utils::FailConfiguration;
use emulator::loader::program_definition::ProgramDefinition;
use emulator::ExecutionResult;

use crate::{FinalStep, Read, Step};

/// How a party behaves.
#[derive(Clone, Debug, Default)]
pub struct Behaviour {
    /// BitVMX's fault injection (a fake trace at a step, a wrong hash, ...).
    pub fail: Option<FailConfiguration>,
}

/// The outcome of the search.
#[derive(Clone, Debug)]
pub struct Searched {
    /// The prover's execution: its result, last step and last hash.
    pub claim: (ExecutionResult, u64, String),
    /// Each round: the prover's hashes and the verifier's choice.
    pub rounds: Vec<(Vec<String>, u32)>,
    /// The disputed step's number.
    pub step: u64,
    /// The prover's full trace of it.
    pub trace: TraceRWStep,
    /// The step, as the final heads carry it.
    pub final_step: FinalStep,
}

fn h20(hex_str: &str) -> Result<[u8; 20]> {
    hex::decode(hex_str)?.try_into().map_err(|_| anyhow!("a step hash is 20 bytes: {hex_str}"))
}

/// A BitVMX trace record with its hashes and the prover's claim (last
/// step, final hash), as a [`FinalStep`].
pub fn final_step(t: &TraceRWStep, step_hash: &str, next_hash: &str, claim_last_step: u64, claim_last_hash: &str) -> Result<FinalStep> {
    Ok(FinalStep {
        prev_hash: h20(step_hash)?,
        read: Read {
            mem_witness: t.mem_witness.byte(),
            read_1_addr: t.read_1.address,
            read_1_value: t.read_1.value,
            read_2_addr: t.read_2.address,
            read_2_value: t.read_2.value,
            pc: t.read_pc.pc.get_address(),
            micro: t.read_pc.pc.get_micro(),
            opcode: t.read_pc.opcode,
        },
        write: Step {
            write_addr: t.trace_step.get_write().address,
            write_value: t.trace_step.get_write().value,
            pc: t.trace_step.get_pc().get_address(),
            micro: t.trace_step.get_pc().get_micro(),
        },
        hash: h20(next_hash)?,
        witness: t.witness.unwrap_or(0),
        agreed_step: u32::try_from(t.step_number - 1).map_err(|_| anyhow!("step beyond 32 bits"))?,
        last_step_1: t.read_1.last_step,
        last_step_2: t.read_2.last_step,
        claim_last_step,
        claim_last_hash: h20(claim_last_hash)?,
    })
}

/// Run the dispute over `pdf` (a BitVMX program definition) on `input`,
/// with each party's checkpoints under `dir`. `force` makes the verifier
/// challenge a valid execution (a dishonest challenger). Returns `None` if
/// the verifier does not challenge.
pub fn search(pdf: &str, input: &[u8], dir: &Path, prover: &Behaviour, verifier: &Behaviour, force: ForceCondition) -> Result<Option<Searched>> {
    let p_dir = format!("{}/prover/", dir.display());
    let v_dir = format!("{}/verifier/", dir.display());
    std::fs::create_dir_all(&p_dir)?;
    std::fs::create_dir_all(&v_dir)?;
    let e = |e: emulator::EmulatorError| anyhow!("{e}");

    let claim = prover_execute(pdf, input.to_vec(), &p_dir, &p_dir, true, prover.fail.clone(), false).map_err(e)?;
    let Some(_) = verifier_check_execution(pdf, input.to_vec(), &v_dir, &v_dir, claim.1, &claim.2, force, verifier.fail.clone(), false).map_err(e)? else {
        return Ok(None);
    };

    let rounds_total = ProgramDefinition::from_config(pdf)?.nary_def().total_rounds();
    let mut rounds = vec![];
    let mut decision = 0u32;
    for round in 1..=rounds_total {
        let hashes = prover_get_hashes_for_round(pdf, &p_dir, &p_dir, round, decision, prover.fail.clone(), NArySearchType::ConflictStep).map_err(e)?;
        decision = verifier_choose_segment(pdf, &v_dir, &v_dir, round, hashes.clone(), verifier.fail.clone(), NArySearchType::ConflictStep).map_err(e)?;
        rounds.push((hashes, decision));
    }
    // the last decision names the last agreed step; the disputed one follows
    let (trace, step_hash, next_hash, step) = prover_final_trace(pdf, &p_dir, &p_dir, decision + 1, prover.fail.clone())
        .map_err(e)?
        .as_final_trace_with_hashes_and_step()
        .map_err(|e| anyhow!("{e:?}"))?;
    // `step` is the last agreed step (its hash is `step_hash`); the trace
    // is the disputed step after it
    if trace.step_number != step + 1 {
        bail!("the final trace is of step {} but the last agreed step is {step}", trace.step_number);
    }
    let final_step = final_step(&trace, &step_hash, &next_hash, claim.1, &claim.2)?;
    Ok(Some(Searched { claim, rounds, step: trace.step_number, trace, final_step }))
}

// ----- the read challenge (D62): BitVMX's second search -----

/// The read challenge played after the first search: BitVMX's
/// `ReadValueChallenge` search toward the step that last wrote the
/// disputed read's address, then the verifier's challenge.
#[derive(Clone, Debug)]
pub struct ReadSearched {
    /// Each round: the prover's hashes and the verifier's choice (round 1's
    /// hashes are the first search's, as BitVMX reuses them).
    pub rounds: Vec<(Vec<String>, u32)>,
    /// The final interval's endpoints (the prover's hashes at the step
    /// before the write and at the write) and that step.
    pub step_hash: [u8; 20],
    pub next_hash: [u8; 20],
    pub step: u64,
    /// The verifier's challenge, as BitVMX chooses it.
    pub challenge: bitvmx_cpu_definitions::challenge::ChallengeType,
}

/// Run the first search, then (if the verifier's choice after it is a read
/// challenge, or `force` makes it one) the read search: BitVMX's sequence
/// (`test_challenge_aux`). `prover_read` is the prover's fault injection
/// during the read search.
#[allow(clippy::too_many_arguments)]
pub fn search_with_read(
    pdf: &str,
    input: &[u8],
    dir: &Path,
    prover: &Behaviour,
    prover_read: &Behaviour,
    verifier: &Behaviour,
    force_condition: ForceCondition,
    force: emulator::decision::challenge::ForceChallenge,
    force_read: emulator::decision::challenge::ForceChallenge,
) -> Result<Option<(Searched, Option<ReadSearched>)>> {
    use bitvmx_cpu_definitions::challenge::ChallengeType;
    use emulator::decision::challenge::{prover_get_hashes_and_step, verifier_choose_challenge, verifier_choose_challenge_for_read_challenge};
    let Some(s) = search(pdf, input, dir, prover, verifier, force_condition)? else { return Ok(None) };
    let p_dir = format!("{}/prover/", dir.display());
    let v_dir = format!("{}/verifier/", dir.display());
    let e = |e: emulator::EmulatorError| anyhow!("{e}");
    let h = |x: &str| h20(x);
    let challenge = verifier_choose_challenge(pdf, &v_dir, &v_dir, s.trace.clone(), &hex::encode(s.final_step.prev_hash), &hex::encode(s.final_step.hash), force, verifier.fail.clone(), true).map_err(e)?;
    let ChallengeType::ReadValueNArySearch { bits } = challenge else { return Ok(Some((s, None))) };
    let rounds_total = ProgramDefinition::from_config(pdf)?.nary_def().total_rounds();
    let mut rounds = vec![(s.rounds[0].0.clone(), bits)];
    let mut decision = bits;
    for round in 2..=rounds_total {
        let hashes = prover_get_hashes_for_round(pdf, &p_dir, &p_dir, round, decision, prover_read.fail.clone(), NArySearchType::ReadValueChallenge).map_err(e)?;
        decision = verifier_choose_segment(pdf, &v_dir, &v_dir, round, hashes.clone(), verifier.fail.clone(), NArySearchType::ReadValueChallenge).map_err(e)?;
        rounds.push((hashes, decision));
    }
    let (step_hash, next_hash, step) = prover_get_hashes_and_step(pdf, &p_dir, NArySearchType::ReadValueChallenge, Some(decision), prover_read.fail.clone())
        .map_err(e)?
        .as_hashes_with_step()
        .map_err(|e| anyhow!("{e:?}"))?;
    let challenge = verifier_choose_challenge_for_read_challenge(pdf, &v_dir, &v_dir, &step_hash, &next_hash, verifier.fail.clone(), force_read, true).map_err(e)?;
    Ok(Some((s, Some(ReadSearched { rounds, step_hash: h(&step_hash)?, next_hash: h(&next_hash)?, step, challenge }))))
}
