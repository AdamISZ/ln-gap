//! Tic-tac-toe on the fact chain with the stall graph: S1–S9 (D28). The
//! scenarios live in `lngap_harness::scenarios::fc_stall`.

use lngap_harness::scenarios::fc_stall::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(s1_cooperative_game_folds_off_chain, S1);
scenario_test!(s2a_hub_stalls_early, S2A);
scenario_test!(s2b_hub_stalls_late, S2B);
scenario_test!(s3_loser_refuses_the_fold, S3);
scenario_test!(s4_spurious_stall_proof_is_disputed, S4);
scenario_test!(s5a_invalid_move_claimed_is_disproved_off_the_stall_output, S5A);
scenario_test!(s5b_invalid_move_is_exhibited, S5B);
scenario_test!(s6_fabricated_stall_proof_is_disputed, S6);
scenario_test!(s7_baseless_exhibit_pays_the_framed_party, S7);
scenario_test!(s8_garbage_signed_entry_is_exhibited, S8);
scenario_test!(s9_baseless_signature_exhibit_is_disputed, S9);
