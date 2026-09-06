use lngap_harness::scenarios::tictactoe::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(t1, T1);
scenario_test!(t2, T2);
scenario_test!(t3, T3);
scenario_test!(t4, T4);
scenario_test!(t5, T5);
scenario_test!(t6, T6);
scenario_test!(t6b, T6B);
scenario_test!(t7, T7);
scenario_test!(t8, T8);
scenario_test!(t9, T9);
