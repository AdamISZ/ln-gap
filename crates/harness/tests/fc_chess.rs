//! Chess on the fact chain with the stall graph: C1–C9. The scenarios live
//! in `lngap_harness::scenarios::fc_chess`.

use lngap_harness::scenarios::fc_chess::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(c1_cooperative_game_folds_off_chain, C1);
scenario_test!(c2_hub_stalls, C2);
scenario_test!(c3_loser_refuses_the_fold, C3);
scenario_test!(c4_illegal_move_claimed_is_disproved_off_the_stall_output, C4);
scenario_test!(c5_illegal_move_is_exhibited, C5);
scenario_test!(c6_baseless_exhibit_pays_the_framed_party, C6);
scenario_test!(c7_fabricated_stall_proof_is_disputed, C7);
scenario_test!(c8_garbage_signed_entry_is_exhibited, C8);
scenario_test!(c9_baseless_signature_exhibit_is_disputed, C9);
