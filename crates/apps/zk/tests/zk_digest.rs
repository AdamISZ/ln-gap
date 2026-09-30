//! Experiment (ZK_SOUNDNESS_PLAN.md, prerequisite 1, option b): a digest
//! in the head. The new head carries a 20-byte BLAKE3 digest of extra data
//! that travels in the entry body; a leaf that needs the data takes it as
//! witness nibbles and checks it against the digest with BitVMX's BLAKE3
//! gadget. How much data fits under the 1,000-element stack limit, and at
//! what script size?
//!
//! The leaf: re-verify the pair signature (the extra data's nibbles lie
//! below the reveal in the witness, so they stay at the bottom); PICK the
//! digest's 40 nibbles to the altstack; drop the register file; bring the
//! digest back on top of the data; BLAKE3 the data; require equality.

use bitcoin::opcodes::all::*;
use bitcoin::script::Builder;
use bitcoin::ScriptBuf;
use bitcoin_script_functions::hash::blake3;
use bitcoin_script_stack::stack::StackTracker;
use lngap_lamport::winternitz::{WotsExt, WotsSecret};
use lngap_pos::instance::mover_at;
use lngap_pos::refute::{disprove_witness, pair_key};
use lngap_pos::ttt::Layout;
use rand::{Rng, SeedableRng};

const GAME: u16 = 1;
const D: u32 = 2;
/// Where the digest sits in the new head (bytes 4..24).
const DIGEST_AT: usize = 4;

fn digest(data: &[u8]) -> [u8; 20] {
    let mut h = ::blake3::Hasher::new();
    h.update(data);
    let mut out = [0u8; 20];
    h.finalize_xof().fill(&mut out);
    out
}

/// BLAKE3 of the `n`-byte message below (its nibbles, first deepest) against
/// the 40-nibble digest on top: fails unless equal.
fn check_script(n: u32) -> ScriptBuf {
    let mut st = StackTracker::new();
    let msg = st.define(n * 2, "msg");
    let dg = st.define(40, "digest");
    st.to_altstack();
    let _ = msg;
    let h = blake3::blake3(&mut st, n, 5);
    let dg = st.from_altstack();
    let _ = dg;
    st.equals(h, true, dg, true);
    st.get_script()
}

fn leaf(n: u32, key: &lngap_lamport::winternitz::WotsPublic) -> ScriptBuf {
    let l = Layout::at(D, GAME, mover_at(D));
    let file = l.file;
    let d0 = l.new + 2 * DIGEST_AT;
    let mut b = Builder::new().wots_verify(key);
    for j in (d0..d0 + 40).rev() {
        b = b.push_int((file - 1 - j) as i64).push_opcode(OP_PICK).push_opcode(OP_TOALTSTACK);
    }
    for _ in 0..file / 2 {
        b = b.push_opcode(OP_2DROP);
    }
    for _ in 0..40 {
        b = b.push_opcode(OP_FROMALTSTACK);
    }
    let mut bytes = b.into_script().into_bytes();
    bytes.extend_from_slice(check_script(n).as_bytes());
    let mut s = ScriptBuf::from_bytes(bytes);
    s.push_opcode(OP_PUSHNUM_1);
    s
}

fn nibbles(data: &[u8]) -> Vec<Vec<u8>> {
    data.iter().flat_map(|b| [b >> 4, b & 15]).map(|v| if v == 0 { vec![] } else { vec![v] }).collect()
}

/// (spendable, peak stack) for `data` against a head carrying `dg`.
fn run(n: u32, sk: &WotsSecret, script: &ScriptBuf, data: &[u8], dg: [u8; 20]) -> (bool, usize) {
    assert_eq!(data.len() as u32, n);
    let prior = [0u8; 48];
    let mut new = [0u8; 48];
    new[DIGEST_AT..DIGEST_AT + 20].copy_from_slice(&dg);
    let mut w = nibbles(data);
    w.extend(disprove_witness(&sk.sign(&[prior.as_slice(), new.as_slice()].concat()).unwrap()));
    match lngap_script32::sim::run_peak(script.as_script(), w) {
        Ok((st, peak)) => (st.len() == 1 && st[0] == [1], peak),
        Err(_) => (false, 0),
    }
}

#[test]
fn digest_leaf_limits() {
    let sk = pair_key([6; 32]);
    let mut rng = rand::rngs::StdRng::seed_from_u64(7);
    println!("{:>6} {:>10} {:>12} {:>8}", "bytes", "script B", "witness els", "peak");
    for n in [8u32, 16, 32, 48, 64, 96, 128, 160, 192, 232, 288] {
        let script = leaf(n, &sk.public());
        let data: Vec<u8> = (0..n).map(|_| rng.gen()).collect();
        let dg = digest(&data);
        let (ok, peak) = run(n, &sk, &script, &data, dg);
        let mut bad = data.clone();
        bad[0] ^= 1;
        let (bad_ok, _) = run(n, &sk, &script, &bad, dg);
        println!("{n:>6} {:>10} {:>12} {peak:>8}  honest {} tampered {}", script.len(), 2 * n as usize + 393, if ok { "passes" } else { "FAILS" }, if bad_ok { "PASSES" } else { "fails" });
        if peak <= 1000 {
            assert!(ok, "{n} bytes: the honest data must pass");
        }
        assert!(!bad_ok, "{n} bytes: tampered data must not pass");
    }
}

/// The same leaf on regtest, behind the challenger's key: the node accepts
/// a spend with the honest data at one block (64 bytes) and at three
/// (192 bytes, the largest under the stack limit), and rejects tampered
/// data; at 232 bytes it rejects even the honest data (the stack limit).
#[test]
fn digest_leaf_on_regtest() {
    use bitcoin::key::Keypair;
    use bitcoin::{Amount, TxOut};
    use lngap_btc::keys::{xonly, Seed};
    use lngap_btc::regtest::Regtest;
    use lngap_btc::script::BuilderExt;
    use lngap_btc::sighash::sign_tapscript;
    use lngap_btc::taptree::{Leaf, TapTree};
    use lngap_btc::tx::{build_spend, Timelock};
    use lngap_btc::witness::tapscript_witness;

    let rt = Regtest::start().unwrap();
    let sk = pair_key([8; 32]);
    let challenger: Keypair = Seed::from_label("digest challenger").keypair("pay");
    let mut rng = rand::rngs::StdRng::seed_from_u64(9);
    for n in [64u32, 192, 232] {
        let mut b = Builder::new().checksigverify(&xonly(&challenger)).into_script().into_bytes();
        b.extend_from_slice(leaf(n, &sk.public()).as_bytes());
        let script = ScriptBuf::from_bytes(b);
        let tree = TapTree::new(vec![Leaf::new("digest", script.clone(), Timelock::NONE)]).unwrap();
        let data: Vec<u8> = (0..n).map(|_| rng.gen()).collect();
        let dg = digest(&data);
        let spend = |data: &[u8]| {
            let (op, prev) = rt.fund(&tree.script_pubkey(), Amount::from_sat(1_000_000)).unwrap();
            let mut tx = build_spend(op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(900_000), script_pubkey: tree.script_pubkey() }]);
            let sig = sign_tapscript(&challenger, &tx, 0, std::slice::from_ref(&prev), &script).unwrap();
            let prior = [0u8; 48];
            let mut new = [0u8; 48];
            new[DIGEST_AT..DIGEST_AT + 20].copy_from_slice(&dg);
            let mut w = nibbles(data);
            w.extend(disprove_witness(&sk.sign(&[prior.as_slice(), new.as_slice()].concat()).unwrap()));
            w.push(sig.as_ref().to_vec());
            tx.input[0].witness = tapscript_witness(&w, &script, &tree.control_block("digest").unwrap());
            tx
        };
        if n == 232 {
            let err = rt.test_accept(&spend(&data)).expect_err("over the stack limit");
            println!("{n} bytes: honest data rejected ({err})");
            continue;
        }
        let mut bad = data.clone();
        bad[n as usize - 1] ^= 0x80;
        let err = rt.test_accept(&spend(&bad)).expect_err("tampered data");
        let tx = spend(&data);
        let (txid, h) = rt.send_and_confirm(&tx).unwrap();
        println!("{n} bytes: {txid} confirmed at {h}: {} vB, {} WU, leaf {} B; tampered rejected ({err})", tx.vsize(), tx.weight().to_wu(), script.len());
    }
}
