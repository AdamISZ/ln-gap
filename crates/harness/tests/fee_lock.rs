//! The fee lock scenarios FL1-FL3 (D52): the proposer paid per attestation,
//! atomically, in a real channel. The scenarios live in
//! `lngap_harness::scenarios::fee_lock`.

use lngap_harness::scenarios::fee_lock::*;

macro_rules! scenario_test {
    ($name:ident, $sc:expr) => {
        #[test]
        fn $name() {
            ($sc.run)().unwrap();
        }
    };
}
scenario_test!(fl1_paid_in_channel_for_the_attestation, FL1);
scenario_test!(fl2_on_chain_claim_completes_the_pre_signature, FL2);
scenario_test!(fl3_no_attestation_the_timeout_refunds, FL3);
