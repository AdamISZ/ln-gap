//! D61: InputData, the input committed by the prover's signature on each
//! word. On hello-world (one input word): the leaf holds on every honest
//! step; it fires on a step that reads the input word with a value other
//! than the signed one (a corrupted read, or a prover that signed one
//! input and ran another); a signature under another key doesn't verify;
//! Script == mirror; the members' check; on regtest.

use lngap_lamport::winternitz::{WotsSecret, WotsSig};
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{disprove_witness, pair_key};
use lngap_pos::ttt::Layout;
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::final_step;
use lngap_zk::final_d60::*;
use lngap_zk::game::*;
use lngap_zk::FinalStep;

const GAME: u16 = 1;
const D: u32 = 23;
const INPUT: [u8; 4] = [0x11; 4];

fn pdf() -> String {
    format!("{}/programs/hello-world.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn all_steps(input: &[u8]) -> Vec<FinalStep> {
    use emulator::decision::challenge::prover_execute;
    use emulator::loader::program_definition::ProgramDefinition;
    let dir = std::env::temp_dir().join(format!("lngap-zk-input-{}-{}", std::process::id(), hex::encode(input)));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let d = format!("{}/", dir.display());
    let (_, last, hash) = prover_execute(&pdf(), input.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(&pdf()).unwrap();
    let (_, trace) = pd.execute_helper(&d, &d, input.to_vec(), Some((0..=last).collect()), None, false).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    trace.windows(2).map(|w| final_step(&w[1].0, &w[0].1, &w[1].1, last, &hash).unwrap()).collect()
}

fn truthy(v: &[u8]) -> bool {
    v.iter().enumerate().any(|(i, b)| *b != 0 && !(i == v.len() - 1 && *b == 0x80))
}

fn run(leaf: &FinalLeaf, sk: &WotsSecret, state: &State, record: &Record, word_sig: &WotsSig) -> (bool, usize) {
    let (p, n) = final_heads(GAME, D, state, record);
    let mut w = lngap_zk::nibble_witness(&record.to_bytes());
    w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
    w.extend(disprove_witness(word_sig));
    match lngap_script32::sim::run_peak(leaf.script.as_script(), w) {
        Ok((st, peak)) => (st.len() == 1 && truthy(&st[0]), peak),
        Err(_) => (false, 0),
    }
}

fn reads_input(f: &FinalStep, a: u32) -> bool {
    (f.last_step_1 == NEVER_WRITTEN && f.read.read_1_addr == a) || (f.last_step_2 == NEVER_WRITTEN && f.read.read_2_addr == a)
}

#[test]
fn input_leaf() {
    let sk = pair_key([81; 32]);
    let info = ProgramInfo::load(&pdf()).unwrap();
    assert_eq!(info.input_words, 1);
    let words = input_words(&INPUT);
    let ik = WotsSecret::from_entropy(input_key_params(), [82; 32]);
    let sig = ik.sign(&input_message(words[0])).unwrap();
    assert!(input_signed(&[ik.public()], &words, std::slice::from_ref(&sig)), "the members' check");
    assert!(!input_signed(&[ik.public()], &[words[0] ^ 1], std::slice::from_ref(&sig)), "a signature on another word");
    let l = Layout::at(D, GAME, mover_at(D));
    let leaves = input_leaves(&l, &sk.public(), &[ik.public()], &info);
    let leaf = &leaves[0];
    let steps = all_steps(&INPUT);
    let readers: Vec<usize> = (0..steps.len()).filter(|&i| reads_input(&steps[i], info.input_base)).collect();
    println!("input base {:#x}, word {:#010x}; {} steps read it: {:?}", info.input_base, words[0], readers.len(), readers.iter().map(|i| i + 1).collect::<Vec<_>>());
    assert!(!readers.is_empty());
    let mut peak = 0;
    // honest: every reader and a sample of the rest
    for i in readers.iter().copied().chain((0..steps.len()).step_by(97)) {
        let (state, _, record) = blocks(&steps[i]);
        let (f, pk) = run(leaf, &sk, &state, &record, &sig);
        assert!(!f && !input_fires(&record, &info, 0, words[0]), "step {}: honest", i + 1);
        peak = peak.max(pk);
    }
    for &i in &readers {
        let (state, _, record) = blocks(&steps[i]);
        // a corrupted read of the input
        let mut bad = record;
        if bad.read.read_1_addr == info.input_base {
            bad.read.read_1_value ^= 0x100;
        } else {
            bad.read.read_2_value ^= 0x100;
        }
        let (f, pk) = run(leaf, &sk, &state, &bad, &sig);
        assert!(f && input_fires(&bad, &info, 0, words[0]), "step {}: a corrupted read of the input", i + 1);
        peak = peak.max(pk);
        // the prover signed another input than the one it ran
        let other = ik.sign(&input_message(words[0] ^ 0x0101)).unwrap();
        assert!(run(leaf, &sk, &state, &record, &other).0 && input_fires(&record, &info, 0, words[0] ^ 0x0101), "step {}: ran one input, signed another", i + 1);
        // a signature under another key proves nothing
        let forged = WotsSecret::from_entropy(input_key_params(), [83; 32]).sign(&input_message(words[0] ^ 1)).unwrap();
        assert!(!run(leaf, &sk, &state, &record, &forged).0, "step {}: a signature under another key", i + 1);
    }
    println!("zk_input_0: {} KB, peak {peak}", leaf.script.len() / 1000);
    assert!(peak <= 1000);
}

/// On regtest: the claimant disproves a prover that ran one input and
/// signed another; the honest signature is rejected.
#[test]
fn input_leaf_on_regtest() {
    use bitcoin::key::Keypair;
    use bitcoin::script::Builder;
    use bitcoin::{Amount, ScriptBuf, TxOut};
    use lngap_btc::keys::{xonly, Seed};
    use lngap_btc::regtest::Regtest;
    use lngap_btc::script::BuilderExt;
    use lngap_btc::sighash::sign_tapscript;
    use lngap_btc::taptree::{Leaf, TapTree};
    use lngap_btc::tx::{build_spend, Timelock};
    use lngap_btc::witness::tapscript_witness;

    let rt = Regtest::start().unwrap();
    let claimant: Keypair = Seed::from_label("input claimant").keypair("pay");
    let sk = pair_key([84; 32]);
    let info = ProgramInfo::load(&pdf()).unwrap();
    let words = input_words(&INPUT);
    let ik = WotsSecret::from_entropy(input_key_params(), [85; 32]);
    let l = Layout::at(D, GAME, mover_at(D));
    let leaf = &input_leaves(&l, &sk.public(), &[ik.public()], &info)[0];
    let steps = all_steps(&INPUT);
    let i = (0..steps.len()).find(|&i| reads_input(&steps[i], info.input_base)).unwrap();
    let (state, _, record) = blocks(&steps[i]);
    let spend = |sig: &WotsSig| {
        let mut b = Builder::new().checksigverify(&xonly(&claimant)).into_script().into_bytes();
        b.extend_from_slice(leaf.script.as_bytes());
        let script = ScriptBuf::from_bytes(b);
        let tree = TapTree::new(vec![Leaf::new("d", script.clone(), Timelock::NONE)]).unwrap();
        let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
        let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
        let s = sign_tapscript(&claimant, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
        let (p, n) = final_heads(GAME, D, &state, &record);
        let mut w = lngap_zk::nibble_witness(&record.to_bytes());
        w.extend(disprove_witness(&sk.sign(&[p.as_slice(), n.as_slice()].concat()).unwrap()));
        w.extend(disprove_witness(sig));
        w.push(s.as_ref().to_vec());
        tx.input[0].witness = tapscript_witness(&w, &script, &tree.control_block("d").unwrap());
        tx
    };
    let err = rt.test_accept(&spend(&ik.sign(&input_message(words[0])).unwrap())).expect_err("the honest input");
    let tx = spend(&ik.sign(&input_message(words[0] ^ 0x0101)).unwrap());
    let (txid, h) = rt.send_and_confirm(&tx).unwrap();
    println!("zk_input_0: step {} disproved, {txid} at {h}, {} vB; honest rejected ({err})", i + 1, tx.vsize());
}

/// The word the trace reads is `input_words`' (an asymmetric input, so
/// the byte order shows).
#[test]
fn input_word_order() {
    let info = ProgramInfo::load(&pdf()).unwrap();
    let input = [0x12, 0x34, 0x56, 0x78];
    let steps = all_steps(&input);
    let f = steps.iter().find(|f| reads_input(f, info.input_base)).expect("hello-world reads its input");
    let v = if f.read.read_1_addr == info.input_base { f.read.read_1_value } else { f.read.read_2_value };
    println!("input {} reads as {v:#010x}; input_words gives {:#010x}", hex::encode(input), input_words(&input)[0]);
    assert_eq!(v, input_words(&input)[0]);
}
