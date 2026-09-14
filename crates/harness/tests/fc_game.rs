//! Tic-tac-toe on the fact chain: G1–G6 (docs/GAME_PROTOCOL.md). The
//! scenarios live in `lngap_harness::scenarios::fc_game`.

use lngap_harness::scenarios::fc_game::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(g1_cooperative_game_folds_off_chain, G1);
scenario_test!(g2a_hub_stalls_early, G2A);
scenario_test!(g2b_hub_stalls_late, G2B);
scenario_test!(g3_loser_refuses_the_fold, G3);
scenario_test!(g4_spurious_timeout_claim_is_refuted_by_inclusion, G4);
scenario_test!(g5_invalid_move_is_disproved, G5);
scenario_test!(g6_fabricated_inclusion_is_disproved_by_bisection, G6);
