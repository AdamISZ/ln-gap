//! The contract library (lngap_sessions::contract) on the mock statement:
//! the pre-signed set as both parties build it, its chain, and both
//! parties' signatures.

use bitcoin::hashes::Hash;
use bitcoin::{Amount, OutPoint, Txid};
use lngap_btc::keys::Seed;
use lngap_channel::{ChannelParams, PartyKeys, Role};
use lngap_lamport::winternitz::{WotsParams, WotsSecret};
use lngap_sessions::contract::{move_bytes, sign_all, Check, Contract, Program, Signed, Spec};
use lngap_sessions::session::Terms;
use lngap_sessions::statement::write_program;
use lngap_zk::final_d60::input_key_params;

#[test]
fn the_presigned_set() {
    let dir = std::env::temp_dir().join(format!("lngap-contract-{}", std::process::id()));
    let pdf = write_program(&dir, 42, &[(9, 42)]).unwrap();
    let program = Program::load(&pdf).unwrap();
    let m = program.depths();
    let (alice, hub) = (PartyKeys::from_seed(Role::User, Seed::from_label("c/alice")), PartyKeys::from_seed(Role::Hub, Seed::from_label("c/hub")));
    let moves: Vec<WotsSecret> = (1..=m).map(|d| WotsSecret::from_entropy(WotsParams::for_bytes(move_bytes(d, m)), Seed::from_label(&format!("c/move/{d}")).derive_bytes("wots"))).collect();
    let inputs: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x60 + j as u8; 32])).collect();
    let terms = Terms { id: 42, unit: Amount::from_sat(1), bits: 21, low_bits: 9, deposit: 500_000, t_close: 1_000, reserve_alice: Amount::from_sat(20_000), reserve_hub: Amount::from_sat(30_000) };
    let spec = Spec {
        terms,
        cid: 42,
        params: ChannelParams::regtest(Amount::from_sat(20_000_000)),
        pubs: [alice.public(), hub.public()],
        b_word: 0,
        checks: vec![Check { name: "memo".into(), word: 1, value: 42 }],
        moves: moves.iter().map(|k| k.public()).collect(),
        inputs: inputs.iter().map(|k| k.public()).collect(),
    };
    let c = Contract::new(spec, &program).unwrap();
    let t = std::time::Instant::now();
    let set = c.presign(OutPoint { txid: Txid::all_zeros(), vout: 0 }).unwrap();
    let proofs = set.iter().filter(|p| p.name.starts_with("prove_")).count();
    println!("CONTRACT {m} depths: {} pre-signed transactions ({} links, {} timeouts, {proofs} proofs, the default) in {:.1?}", set.len(), m, m, t.elapsed());
    assert_eq!(set.len() as u32, 1 + 2 * m + proofs as u32);
    // the chain: each link spends the previous one's output 0, its txid
    // fixed before any is signed
    let links: Vec<_> = set.iter().filter(|p| p.link).collect();
    for w in links.windows(2) {
        assert_eq!(w[1].tx.input[0].previous_output, OutPoint { txid: w[0].tx.compute_txid(), vout: 0 }, "{} spends {}", w[1].name, w[0].name);
        assert_eq!(w[1].tx.version.0, 3);
    }
    // the dispute path's payout: bits 9..21 and the reserves, no dust
    let pay = c.pay_alice(c.value()).unwrap();
    assert_eq!(pay.len(), 12 + 1 + 1, "12 bit outputs, the reserves, the rest");
    assert!(pay.iter().all(|o| o.value >= c.spec.params.dust), "no dust output");
    // both sign; each checks the other's
    let signed = Signed { hub: sign_all(&set, &hub.payment).unwrap(), alice: sign_all(&set, &alice.payment).unwrap() };
    signed.verify(&set, &c.spec.pubs).unwrap();
    let mut bad = signed.clone();
    let k = "timeout_3".to_string();
    bad.hub.insert(k.clone(), signed.alice[&k].clone());
    assert!(bad.verify(&set, &c.spec.pubs).is_err(), "a signature by the wrong party");
    let _ = std::fs::remove_dir_all(&dir);
}
