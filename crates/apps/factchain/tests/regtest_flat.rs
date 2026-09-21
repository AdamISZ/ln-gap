//! The flat terminal leaf on every compression step of the names-registry
//! header claim (one header, eight steps: seven absorbs and the pad), on
//! regtest: a lying output must be disprovable, an honest one must not.
//! Written to isolate a failure of scenario N8 after the header grew to
//! 56 bytes and the isolated step became the pad step.

use bitcoin::{Amount, ScriptBuf, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::WitnessStack;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_contract::claim::{words_bytes, ClaimKeys, ClaimSpec, Init, Step};
use lngap_contract::inner::{flat_round_leaf, flat_round_witness, InnerKeys};
use lngap_factchain::claim::FactChainShape;
use lngap_factchain::{genesis, ChainClient, Miner, DIFFICULTY_BITS};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::WotsSig;

fn keys(spec: &ClaimSpec) -> ClaimKeys {
    let mut ks = KeyStore::new(Seed::from_label("prover"));
    let nb = spec.wots_bytes();
    ClaimKeys {
        end: ks.generate_wots("end", nb).unwrap(),
        rounds: (1..=spec.rounds()).map(|r| (0..spec.k - 1).map(|t| ks.generate_wots(&format!("r{r}t{t}"), nb).unwrap()).collect()).collect(),
        inner: Some(InnerKeys {
            re_cur: ks.generate_wots("re_cur", nb).unwrap(),
            re_next: ks.generate_wots("re_next", nb).unwrap(),
            block: (0..spec.hash.block_words()).map(|j| ks.generate_wots(&format!("block{j}"), 4).unwrap()).collect(),
            sched: vec![],
            states: vec![],
        }),
    }
}

fn sign(label: &str, msg: &[u8]) -> WotsSig {
    let mut ks = KeyStore::new(Seed::from_label("prover"));
    ks.generate_wots(label, msg.len() as u32).unwrap();
    ks.sign_wots(label, msg).unwrap()
}

#[test]
fn flat_leaf_on_every_step_of_a_header_claim() {
    let rt = Regtest::start().unwrap();
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("u"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("h"));
    let pubs = [user.public(), hub.public()];
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let ctx = CommitCtx { params: &params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };
    let prover = Role::Hub;
    let q = user.payment;
    let sink = user.payout_tree().script_pubkey();

    // a one-block chain and the claim over it
    let g = genesis();
    let mut miner = Miner::new(g.header.digest(), 0);
    let mut client = ChainClient::from_checkpoint(0, g.header.digest());
    miner.submit(vec![0xAB; 64]);
    client.verify_and_append(&miner.mine_next().unwrap()).unwrap();
    let shape = FactChainShape { checkpoint: g.header.digest(), target: lngap_n4bit::target_from_difficulty(DIFFICULTY_BITS), n_headers: 1 };
    let spec = shape.spec();
    let headers: Vec<[u8; lngap_factchain::HEADER_BYTES]> = client.chain_headers().iter().map(|h| h.0).collect();
    let data = shape.data(&headers);
    let states = spec.states(&data);
    let keys = keys(&spec);

    let spend = |leaf: &ScriptBuf, args: Vec<Vec<u8>>| {
        let tree = TapTree::new(vec![Leaf::new("l", leaf.clone(), Timelock::NONE)]).unwrap();
        let (op, prevout) = rt.fund(&tree.script_pubkey(), Amount::from_sat(200_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(150_000), script_pubkey: sink.clone() }]);
        let sig = sign_tapscript(&q, &tx, 0, std::slice::from_ref(&prevout), leaf).unwrap();
        let mut w = WitnessStack::new();
        w.push(sig.as_ref().to_vec()).extend(args);
        tx.input[0].witness = w.build(leaf, &tree.control_block("l").unwrap());
        rt.test_accept(&tx)
    };

    // where does the leaf fail in the simulator?
    {
        let i = 0;
        let step = &spec.steps[i];
        let (_, leaf) = flat_round_leaf(&ctx, prover, &keys, &spec, i);
        let (_, block) = ClaimSpec::compress_inputs(step, &states[i], spec.data_for(&data, i), spec.hash);
        let block_sigs: Vec<WotsSig> = (0..spec.hash.block_words()).map(|j| sign(&format!("block{j}"), &block[4 * j..4 * j + 4])).collect();
        let mut lie_state = states[i + 1].clone();
        lie_state[0] ^= 0x10;
        let args = flat_round_witness(&sign("re_next", &words_bytes(&lie_state)), None, &block_sigs);
        // the leaf starts with <Q> CHECKSIGVERIFY: strip it and run the rest
        let ins: Vec<bitcoin::script::Instruction> = leaf.instructions().map(|x| x.unwrap()).collect();
        let mut b = bitcoin::script::Builder::new();
        for x in &ins[2..] {
            b = match x {
                bitcoin::script::Instruction::Op(op) => b.push_opcode(*op),
                bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
            };
        }
        let body = b.into_script();
        let stack: Vec<Vec<u8>> = args.iter().rev().cloned().collect();
        match lngap_script32::sim::run(&body, stack) {
            Ok(st) => eprintln!("SIM step 0 lie: ok, final stack {:?}", st.iter().rev().take(3).collect::<Vec<_>>()),
            Err(e) => {
                eprintln!("SIM step 0 lie: {e}");
                if let Some(pc) = e.rsplit("instruction ").next().and_then(|x| x.trim().parse::<usize>().ok()) {
                    let ins2: Vec<_> = body.instructions().map(|x| x.unwrap()).collect();
                    for k in pc.saturating_sub(12)..=pc.min(ins2.len() - 1) {
                        eprintln!("  {k}: {:?}", ins2[k]);
                    }
                }
            }
        }
    }
    for (i, step) in spec.steps.iter().enumerate() {
        let Step::Compress { init, .. } = step else { continue };
        let (name, leaf) = flat_round_leaf(&ctx, prover, &keys, &spec, i);
        let (_, block) = ClaimSpec::compress_inputs(step, &states[i], spec.data_for(&data, i), spec.hash);
        let block_sigs: Vec<WotsSig> = (0..spec.hash.block_words()).map(|j| sign(&format!("block{j}"), &block[4 * j..4 * j + 4])).collect();
        let in_sig = match init {
            Init::Iv => None,
            Init::D => Some(sign("re_cur", &words_bytes(&states[i]))),
        };
        let honest = flat_round_witness(&sign("re_next", &words_bytes(&states[i + 1])), in_sig.as_ref(), &block_sigs);
        let mut lie_state = states[i + 1].clone();
        lie_state[0] ^= 0x10;
        let lie = flat_round_witness(&sign("re_next", &words_bytes(&lie_state)), in_sig.as_ref(), &block_sigs);
        let h = spend(&leaf, honest);
        let l = spend(&leaf, lie);
        let short = |e: &String| e.split(',').next().unwrap_or(e).to_string();
        eprintln!("step {i} {} ({name}, round counter {}): honest {:?}, lie {:?}", step.name(), spec.round_counter(i), h.as_ref().err().map(short), l.as_ref().map(|v| format!("accepted {v} vB")).map_err(|e| short(&e)));
        assert!(h.is_err(), "step {i}: honest output must not be disprovable");
        assert!(l.is_ok(), "step {i}: lying output must be disprovable: {}", l.unwrap_err());
    }
}
