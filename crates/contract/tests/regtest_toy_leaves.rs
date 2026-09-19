//! Every coin-flip disprove leaf, at depth 1 (constant prior) and depth 2
//! (committed prior), checked against the real interpreter for honest and
//! fraudulent claims. The rule under test: the leaf accepts iff `detects`.

use std::sync::Arc;

use bitcoin::{Amount, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_contract::toy::CoinFlip;
use lngap_contract::{Claim, ContractInstance, DepthKeys, Program, CODE_BITS};
use lngap_lamport::{uint_to_bits, SecretKey};

struct DepthSecrets {
    mv: SecretKey,
    state: SecretKey,
    code: SecretKey,
}

fn secrets(prover: Role, seed: u8, prog: &dyn Program) -> (DepthSecrets, DepthKeys) {
    let s = DepthSecrets {
        mv: SecretKey::from_entropy(prog.n_move_bits(), [seed; 32]),
        state: SecretKey::from_entropy(prog.n_state_bits(), [seed + 1; 32]),
        code: SecretKey::from_entropy(CODE_BITS, [seed + 2; 32]),
    };
    let k = DepthKeys { prover, mv: s.mv.public(), state: s.state.public(), code: s.code.public(), claim: None, prior: None, state_n4: vec![], depth: None };
    (s, k)
}

#[test]
fn coinflip_disprove_leaves_match_native_checks() {
    let rt = Regtest::start().unwrap();
    let prog: Arc<dyn Program> = Arc::new(CoinFlip);
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
    let pubs = [user.public(), hub.public()];
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };

    let (s1, k1) = secrets(Role::User, 10, &*prog);
    let (s2, k2) = secrets(Role::Hub, 20, &*prog);
    let inst = ContractInstance::new(7, prog.clone(), Amount::from_sat(20_000), prog.initial_bits(), 300, 1, vec![k1, k2], vec![]).unwrap();
    let sink = user.payout_tree().script_pubkey();

    // depth 1: user is prover, prior = initial (constant)
    let d1_claims: Vec<(&str, Claim)> = vec![
        ("honest 0", Claim { prior: vec![false; 4], mv: vec![false], new: vec![true, false, false, false], code: CoinFlip::USER_WINS, mover: Role::User }),
        ("honest 1", Claim { prior: vec![false; 4], mv: vec![true], new: vec![true, true, false, false], code: CoinFlip::USER_WINS, mover: Role::User }),
        ("wrong state", Claim { prior: vec![false; 4], mv: vec![true], new: vec![true, false, false, false], code: CoinFlip::USER_WINS, mover: Role::User }),
        ("skipped flag", Claim { prior: vec![false; 4], mv: vec![false], new: vec![false; 4], code: CoinFlip::USER_WINS, mover: Role::User }),
        ("wrong code", Claim { prior: vec![false; 4], mv: vec![false], new: vec![true, false, false, false], code: CoinFlip::HUB_WINS, mover: Role::User }),
        ("fake hub reveal", Claim { prior: vec![false; 4], mv: vec![false], new: vec![true, false, true, false], code: CoinFlip::USER_WINS, mover: Role::User }),
    ];
    check_depth(&rt, &inst, &ctx, 1, &s1, None, &hub, &d1_claims, &sink);

    // depth 2: hub is prover, prior = user's depth-1 commitment
    let prior = vec![true, true, false, false]; // user revealed 1
    let d2_claims: Vec<(&str, Claim)> = vec![
        ("honest hub 1 -> xor 0", Claim { prior: prior.clone(), mv: vec![true], new: vec![true, true, true, true], code: CoinFlip::USER_WINS, mover: Role::Hub }),
        ("honest hub 0 -> xor 1", Claim { prior: prior.clone(), mv: vec![false], new: vec![true, true, true, false], code: CoinFlip::HUB_WINS, mover: Role::Hub }),
        ("hub lies about code", Claim { prior: prior.clone(), mv: vec![true], new: vec![true, true, true, true], code: CoinFlip::HUB_WINS, mover: Role::Hub }),
        ("hub flips user's bit", Claim { prior: prior.clone(), mv: vec![false], new: vec![true, false, true, false], code: CoinFlip::USER_WINS, mover: Role::Hub }),
        ("hub moves before user", Claim { prior: vec![false; 4], mv: vec![false], new: vec![false, false, true, false], code: CoinFlip::USER_WINS, mover: Role::Hub }),
        ("hub moves twice", Claim { prior: vec![true, true, true, true], mv: vec![false], new: vec![true, true, true, false], code: CoinFlip::HUB_WINS, mover: Role::Hub }),
    ];
    check_depth(&rt, &inst, &ctx, 2, &s2, Some(&s1), &user, &d2_claims, &sink);
}

#[allow(clippy::too_many_arguments)]
fn check_depth(
    rt: &Regtest,
    inst: &ContractInstance,
    ctx: &CommitCtx,
    depth: u32,
    prover: &DepthSecrets,
    prior_prover: Option<&DepthSecrets>,
    challenger: &PartyKeys,
    claims: &[(&str, Claim)],
    sink: &bitcoin::ScriptBuf,
) {
    let tree = inst.depth_tree(ctx, depth).unwrap();
    let specs = inst.disprove_specs(depth);
    for (label, claim) in claims {
        let native = lngap_contract::onchain::check_claim(&*inst.program, claim);
        let mv = prover.mv.reveal_bits(&claim.mv).unwrap();
        let new = prover.state.reveal_bits(&claim.new).unwrap();
        let code = prover.code.reveal_bits(&uint_to_bits(u32::from(claim.code), CODE_BITS)).unwrap();
        let prior = prior_prover.map(|p| p.state.reveal_bits(&claim.prior).unwrap());
        let mut any_detected = false;
        for spec in &specs {
            let leaf_name = format!("disprove_{}", spec.name);
            let leaf = tree.leaf(&leaf_name).unwrap();
            let (op, prevout) = rt.fund(&tree.script_pubkey(), Amount::from_sat(20_000)).unwrap();
            let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(19_000), script_pubkey: sink.clone() }]);
            let sig = sign_tapscript(&challenger.payment, &tx, 0, std::slice::from_ref(&prevout), &leaf.script).unwrap();
            let mut w = WitnessStack::new();
            w.push(sig.as_ref().to_vec()).extend(spec.witness_args(prior.as_ref(), &mv, &new, &code, &[]));
            tx.input[0].witness = w.build(&leaf.script, &tree.control_block(&leaf_name).unwrap());
            let accepted = rt.test_accept(&tx).is_ok();
            let detects = (spec.detects)(claim);
            eprintln!("depth {depth} claim '{label}' leaf {leaf_name}: script {} B, witness {} B, accepted={accepted}", leaf.script.len(), tx.input[0].witness.size());
            assert_eq!(accepted, detects, "depth {depth} claim '{label}' leaf {leaf_name}: interpreter {accepted} vs native {detects}");
            any_detected |= detects;
            if detects {
                // and the disproof really goes through
                rt.send_and_confirm(&tx).unwrap();
            }
        }
        assert_eq!(any_detected, native.is_err(), "claim '{label}': native verdict {native:?} but leaves detected={any_detected}");
    }
    // a challenger signature from the wrong key never works
    let spec = &specs[0];
    let leaf_name = format!("disprove_{}", spec.name);
    let leaf = tree.leaf(&leaf_name).unwrap();
    let (op, prevout) = rt.fund(&tree.script_pubkey(), Amount::from_sat(20_000)).unwrap();
    let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(19_000), script_pubkey: sink.clone() }]);
    let wrong = PartyKeys::from_seed(challenger.role, Seed::from_label("wrong"));
    let sig = sign_tapscript(&wrong.payment, &tx, 0, std::slice::from_ref(&prevout), &leaf.script).unwrap();
    let claim = &claims[claims.len() - 1].1;
    let mv = prover.mv.reveal_bits(&claim.mv).unwrap();
    let new = prover.state.reveal_bits(&claim.new).unwrap();
    let code = prover.code.reveal_bits(&uint_to_bits(u32::from(claim.code), CODE_BITS)).unwrap();
    let prior = prior_prover.map(|p| p.state.reveal_bits(&claim.prior).unwrap());
    let mut w = WitnessStack::new();
    w.push(sig.as_ref().to_vec()).extend(spec.witness_args(prior.as_ref(), &mv, &new, &code, &[]));
    tx.input[0].witness = w.build(&leaf.script, &tree.control_block(&leaf_name).unwrap());
    assert!(rt.test_accept(&tx).is_err(), "wrong challenger key must fail");
}

#[test]
fn graph_shape_and_signing() {
    let prog: Arc<dyn Program> = Arc::new(CoinFlip);
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
    let pubs = [user.public(), hub.public()];
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let (_, k1) = secrets(Role::User, 10, &*prog);
    let (_, k2) = secrets(Role::Hub, 20, &*prog);
    let inst = ContractInstance::new(1, prog.clone(), Amount::from_sat(20_000), prog.initial_bits(), 300, 1, vec![k1, k2], vec![]).unwrap();
    for broadcaster in Role::BOTH {
        let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster, seq: 1, rev_hash: [1u8; 20] };
        let tree = lngap_channel::ContractOutput::tree(&inst, &ctx).unwrap();
        let op = bitcoin::OutPoint { txid: bitcoin::Txid::from_raw_hash(bitcoin::hashes::Hash::all_zeros()), vout: 0 };
        let prevout = TxOut { value: inst.value, script_pubkey: tree.script_pubkey() };
        let mut graph = lngap_channel::ContractOutput::graph(&inst, &ctx, op, &prevout).unwrap();
        let labels: Vec<_> = graph.iter().map(|g| g.label.clone()).collect();
        assert_eq!(labels, ["settle", "move_1", "split_1_UserWins", "split_1_HubWins", "move_2", "split_2_UserWins", "split_2_HubWins"]);
        // move_1 by the user is delayed only on the user's own commitment
        let m1 = &graph[1];
        assert_eq!(m1.leaf.timelock.csv.is_some(), broadcaster == Role::User);
        // settle: CLTV deadline and CSV to_self_delay
        assert_eq!(graph[0].leaf.timelock, Timelock::both(300, 6));
        // prover-favourable splits wait Delta + Delta'
        assert_eq!(graph[2].leaf.timelock, Timelock::csv(12), "UserWins favours the depth-1 prover (user)");
        assert_eq!(graph[3].leaf.timelock, Timelock::csv(6));
        assert_eq!(graph[6].leaf.timelock, Timelock::csv(12), "HubWins favours the depth-2 prover (hub)");
        // chain: move_2 spends move_1's output, splits spend their depth's move
        assert_eq!(graph[4].tx.input[0].previous_output.txid, graph[1].txid());
        assert_eq!(graph[5].tx.input[0].previous_output.txid, graph[4].txid());
        // values: V - d*fee
        assert_eq!(graph[1].tx.output[0].value, Amount::from_sat(19_000));
        assert_eq!(graph[4].tx.output[0].value, Amount::from_sat(18_000));
        assert_eq!(graph[5].tx.output.iter().map(|o| o.value).sum::<Amount>(), Amount::from_sat(17_000));
        for g in graph.iter_mut() {
            g.sign_as(Role::User, &user.payment).unwrap();
            let s = g.sign_as(Role::Hub, &hub.payment).unwrap();
            g.add_sig(Role::Hub, s, &pubs).unwrap();
            assert!(g.fully_signed());
        }
        for (name, s, cb) in tree.sizes() {
            eprintln!("{broadcaster} C tree leaf {name}: {s} B script, {cb} B control block");
        }
        for (name, s, cb) in inst.depth_tree(&ctx, 1).unwrap().sizes() {
            eprintln!("{broadcaster} C'_1 leaf {name}: {s} B script, {cb} B control block");
        }
    }
}
