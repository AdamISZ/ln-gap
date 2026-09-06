//! Shared test support: drive every disprove leaf of a contract at some
//! depth through the real interpreter for a list of claims, and assert the
//! leaf accepts exactly when its native `detects` says so.

use bitcoin::{Amount, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_channel::{CommitCtx, PartyKeys, Role};
use lngap_lamport::{uint_to_bits, SecretKey};

use crate::onchain::check_claim;
use crate::{Claim, ContractInstance, DepthKeys, Program, CODE_BITS};

pub struct DepthSecrets {
    pub mv: SecretKey,
    pub state: SecretKey,
    pub code: SecretKey,
}

pub fn depth_secrets(prover: Role, seed: u8, prog: &dyn Program) -> (DepthSecrets, DepthKeys) {
    let s = DepthSecrets {
        mv: SecretKey::from_entropy(prog.n_move_bits(), [seed; 32]),
        state: SecretKey::from_entropy(prog.n_state_bits(), [seed.wrapping_add(1); 32]),
        code: SecretKey::from_entropy(CODE_BITS, [seed.wrapping_add(2); 32]),
    };
    let k = DepthKeys { prover, mv: s.mv.public(), state: s.state.public(), code: s.code.public() };
    (s, k)
}

/// Sizes observed: (leaf name, script bytes, witness bytes).
pub type LeafSizes = Vec<(String, usize, usize)>;

/// For each claim and each disprove leaf at `depth`: build the disproof,
/// run it through `testmempoolaccept`, and compare with `detects`. Also
/// checks that the leaves collectively detect exactly the claims the native
/// checker rejects, and that a wrong challenger key never works.
#[allow(clippy::too_many_arguments)]
pub fn check_disprove_leaves(
    rt: &Regtest,
    inst: &ContractInstance,
    ctx: &CommitCtx,
    depth: u32,
    prover: &DepthSecrets,
    prior_prover: Option<&DepthSecrets>,
    challenger: &PartyKeys,
    claims: &[(&str, Claim)],
) -> LeafSizes {
    let tree = inst.depth_tree(ctx, depth).unwrap();
    let specs = inst.disprove_specs(depth);
    let sink = challenger.payout_tree().script_pubkey();
    let mut sizes: LeafSizes = Vec::new();
    let build = |spec: &crate::DisproveSpec, claim: &Claim, key: &bitcoin::key::Keypair| {
        let leaf_name = format!("disprove_{}", spec.name);
        let leaf = tree.leaf(&leaf_name).unwrap();
        let (op, prevout) = rt.fund(&tree.script_pubkey(), Amount::from_sat(20_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(19_000), script_pubkey: sink.clone() }]);
        let sig = sign_tapscript(key, &tx, 0, std::slice::from_ref(&prevout), &leaf.script).unwrap();
        let mv = prover.mv.reveal_bits(&claim.mv).unwrap();
        let new = prover.state.reveal_bits(&claim.new).unwrap();
        let code = prover.code.reveal_bits(&uint_to_bits(u32::from(claim.code), CODE_BITS)).unwrap();
        let prior = prior_prover.map(|p| p.state.reveal_bits(&claim.prior).unwrap());
        let mut w = WitnessStack::new();
        w.push(sig.as_ref().to_vec()).extend(spec.witness_args(prior.as_ref(), &mv, &new, &code));
        tx.input[0].witness = w.build(&leaf.script, &tree.control_block(&leaf_name).unwrap());
        (leaf_name, leaf.script.len(), tx)
    };
    for (label, claim) in claims {
        let native = check_claim(&*inst.program, claim);
        let mut detected_by = Vec::new();
        for spec in &specs {
            let (leaf_name, script_len, tx) = build(spec, claim, &challenger.payment);
            let accepted = rt.test_accept(&tx).is_ok();
            let detects = (spec.detects)(claim);
            assert_eq!(accepted, detects, "depth {depth} claim '{label}' leaf {leaf_name}: interpreter {accepted} vs native {detects}");
            if detects {
                detected_by.push(leaf_name.clone());
                rt.send_and_confirm(&tx).unwrap();
            }
            if !sizes.iter().any(|s| s.0 == leaf_name) {
                sizes.push((leaf_name, script_len, tx.input[0].witness.size()));
            }
        }
        assert_eq!(!detected_by.is_empty(), native.is_err(), "claim '{label}': native verdict {native:?} but detected by {detected_by:?}");
        eprintln!("depth {depth} claim '{label}': native {:?}, detected by {detected_by:?}", native.as_ref().err());
    }
    // wrong challenger key
    let wrong = PartyKeys::from_seed(challenger.role, Seed::from_label("wrong-challenger"));
    let claim = &claims[claims.len() - 1].1;
    let (_, _, tx) = build(&specs[0], claim, &wrong.payment);
    assert!(rt.test_accept(&tx).is_err(), "wrong challenger key must fail");
    sizes
}
