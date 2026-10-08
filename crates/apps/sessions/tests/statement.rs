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
