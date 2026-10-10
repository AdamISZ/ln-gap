//! The mock statement under BitVMX: an honest accepted withdrawal, a
//! claim of a return that isn't in the table, another session's return.

use emulator::decision::challenge::ForceCondition;
use lngap_sessions::statement::{input, write_program};
use lngap_zk::dispute::{search, Behaviour};

fn run(tag: &str, b: u32, c: u32) -> lngap_zk::dispute::Searched {
    let dir = std::env::temp_dir().join(format!("lngap-sess-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let pdf = write_program(&dir.join("prog"), 7, &[(5, 7), (9, 7)]).unwrap();
    let s = search(&pdf, &input(b, c), &dir.join("run"), &Behaviour::default(), &Behaviour::default(), ForceCondition::ValidInputStepAndHash).unwrap().expect("forced");
    let _ = std::fs::remove_dir_all(&dir);
    s
}

#[test]
fn the_statement_under_bitvmx() {
    for (tag, b, c) in [("ok", 9, 7), ("absent", 6, 7), ("other", 5, 8)] {
        let s = run(tag, b, c);
        println!("SESS {tag}: b={b} c={c}: {:?}, {} rounds, last step {}, disputed step {}", s.claim.0, s.rounds.len(), s.claim.1, s.step);
    }
}

/// The table's wildcard: `(ANY, [(ANY, ANY)])` accepts every claim; a
/// table without it still rejects what isn't in it.
#[test]
fn the_wildcard_accepts_every_claim() {
    use emulator::decision::challenge::prover_execute;
    use emulator::ExecutionResult;
    use lngap_sessions::statement::{input, write_program, ANY};
    let dir = std::env::temp_dir().join(format!("lngap-any-{}", std::process::id()));
    // the exit code (the emulator reports a failing halt as an error)
    let run = |session: u32, table: &[(u32, u32)], b: u32, c: u32| -> u32 {
        let d = dir.join(format!("{session}-{b}-{c}-{}", table.len()));
        let pdf = write_program(&d, session, table).unwrap();
        let ck = format!("{}/", d.join("ck").display());
        std::fs::create_dir_all(&ck).unwrap();
        match prover_execute(&pdf, input(b, c), &ck, &ck, false, None, false) {
            Ok((ExecutionResult::Halt(x, _), _, _)) => x,
            Err(emulator::EmulatorError::ExecutionError(ExecutionResult::Halt(x, _))) => x,
            other => panic!("{other:?}"),
        }
    };
    assert_eq!(run(ANY, &[(ANY, ANY)], 123_456, 1_001), 0, "any claim");
    assert_eq!(run(ANY, &[(ANY, ANY)], 7, 99), 0, "any claim");
    assert_eq!(run(42, &[(9, 42)], 9, 42), 0, "in the table");
    assert_eq!(run(42, &[(9, 42)], 10, 42), 1, "not in the table");
    assert_eq!(run(42, &[(ANY, 42)], 10, 43), 2, "another session");
    assert_eq!(run(42, &[(ANY, 42)], 10, 42), 0, "any amount for the session");
    let _ = std::fs::remove_dir_all(&dir);
}
