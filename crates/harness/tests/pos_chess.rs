//! The PoS absence-claim graph's chess scenario suite: PC1-PC11
//! (POS_FACTCHAIN_PLAN.md step 7; D42; D44). The scenarios live in
//! `lngap_harness::scenarios::pos_chess`. Run with `--test-threads=2`: eleven
//! chess games on fresh regtests contend for the box.

use lngap_harness::scenarios::pos_chess::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(pc1_cooperative_game_nothing_on_bitcoin, PC1);
scenario_test!(pc2_hub_stalls_at_move_2, PC2);
scenario_test!(pc3_hub_stalls_at_move_6, PC3);
scenario_test!(pc4_mated_sides_absence_resolves_no_exhibit, PC4);
scenario_test!(pc5_spurious_absence_claim_forfeits_the_claimant, PC5);
scenario_test!(pc6_illegal_move_disproved_off_the_refutation, PC6);
scenario_test!(pc7_double_played_slot_pays_the_victim, PC7);
scenario_test!(pc8_garbage_signed_attested_entry_is_not_a_move, PC8);
scenario_test!(pc9_mated_sides_illegal_answer_disproved, PC9);
scenario_test!(pc10_claim_one_depth_ahead_countered, PC10);
scenario_test!(pc11_false_counter_refuted, PC11);
