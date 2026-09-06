use lngap_harness::scenarios::names::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(n1, N1);
scenario_test!(n2, N2);
scenario_test!(n3, N3);
scenario_test!(n4, N4);
scenario_test!(n5, N5);
scenario_test!(n6, N6);
scenario_test!(n7, N7);
scenario_test!(n8, N8);
