//! The PoS absence-claim graph's scenario suite: PS1-PS13 (D40; plan step 7; D44; D50; D51).
//! The scenarios live in `lngap_harness::scenarios::pos_stall`.

use lngap_harness::scenarios::pos_stall::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(ps1_cooperative_game_nothing_on_bitcoin, PS1);
scenario_test!(ps2_hub_stalls_at_move_2, PS2);
scenario_test!(ps3_hub_stalls_at_move_6, PS3);
scenario_test!(ps4_loser_refuses_the_fold_terminal_exhibit, PS4);
scenario_test!(ps5_spurious_absence_claim_forfeits_the_claimant, PS5);
scenario_test!(ps6a_illegal_move_disproved_off_the_refutation, PS6A);
scenario_test!(ps6b_fabricated_terminal_state_disproved_off_the_exhibit, PS6B);
scenario_test!(ps7_double_played_slot_pays_the_victim, PS7);
scenario_test!(ps8_baseless_terminal_exhibit_rejected_by_the_gate, PS8);
scenario_test!(ps9_garbage_signed_attested_entry_is_not_a_move, PS9);
scenario_test!(ps10_claim_one_depth_ahead_countered, PS10);
scenario_test!(ps11_false_counter_refuted, PS11);
scenario_test!(ps12_late_attestation_killed_by_the_flags, PS12);
scenario_test!(ps13_silent_proposer_mover_loses_by_absence, PS13);
