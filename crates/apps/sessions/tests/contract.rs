//! The contract library (lngap_sessions::contract) on the mock statement:
//! the pre-signed set as both parties build it, its chain, and both
//! parties' signatures.

use bitcoin::hashes::Hash;
use bitcoin::{Amount, OutPoint, Txid};
use lngap_btc::keys::Seed;
use lngap_channel::{ChannelParams, PartyKeys, Role};
use lngap_lamport::winternitz::{WotsParams, WotsSecret};
use lngap_sessions::contract::{sign_all, Check, Contract, Program, Signed, Spec};
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
    let moves: Vec<Vec<WotsSecret>> = (1..=m)
        .map(|d| program.field_bytes(d).into_iter().enumerate().map(|(f, n)| WotsSecret::from_entropy(WotsParams::for_bytes(n), Seed::from_label(&format!("c/move/{d}/{f}")).derive_bytes("wots"))).collect())
        .collect();
    let inputs: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x60 + j as u8; 32])).collect();
    let terms = Terms { id: 42, unit: Amount::from_sat(1), bits: 21, low_bits: 9, deposit: 500_000, t_close: 1_000, reserve_alice: Amount::from_sat(20_000), reserve_hub: Amount::from_sat(100_000) };
    let spec = Spec {
        terms,
        cid: 42,
        params: ChannelParams::regtest(Amount::from_sat(20_000_000)),
        pubs: [alice.public(), hub.public()],
        b_word: 0,
        checks: vec![Check { name: "memo".into(), word: 1, value: 42, in_claim: true }],
        moves: moves.iter().map(|ks| ks.iter().map(|k| k.public()).collect()).collect(),
        inputs: inputs.iter().map(|k| k.public()).collect(),
        tail: None,
        windows: None,
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
        assert_eq!(w[1].tx.version.0, 2, "an ordinary transaction, not TRUC");
    }
    // each link pays its floor out of the contract and carries the poster's
    // anchor; the floors must fit in the hub's reserve (D-J2)
    let last = links.last().unwrap();
    let floors = c.value() - last.tx.output[0].value;
    println!("CONTRACT the chain's floors and anchors: {floors} (the hub's reserve: {})", c.spec.terms.reserve_hub);
    assert!(floors < c.spec.terms.reserve_hub);
    assert!(links.iter().all(|p| p.tx.output[1].value == lngap_sessions::contract::ANCHOR));
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

/// Opt-in: each link's size on BitVMX's Groth16 verifier (8-ary, a jump
/// list), from the pre-signed set (a link's floor is its vsize at 1
/// sat/vB): no emulation needed.
#[test]
#[ignore]
fn link_sizes_on_the_groth16_verifier() {
    let home = std::env::var("HOME").unwrap();
    let elf = std::fs::read_dir(format!("{home}/.cargo/git/checkouts"))
        .unwrap()
        .flatten()
        .filter(|d| d.file_name().to_string_lossy().starts_with("bitvmx-cpu-"))
        .flat_map(|d| std::fs::read_dir(d.path()).unwrap().flatten())
        .map(|r| r.path().join("docker-riscv32/verifier/build/zkverifier-new-mul.elf"))
        .find(|p| p.exists())
        .expect("the verifier ELF");
    let dir = std::env::temp_dir().join(format!("lngap-sizes-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::copy(elf, dir.join("zkverifier.elf")).unwrap();
    for (nary, jump) in [(2u8, false), (8, false), (8, true)] {
        std::fs::write(dir.join("g.yaml"), format!("elf: zkverifier.elf\nnary_search: {nary}\nmax_steps: 536870912\ninput_section_name: .input\njump_list: {jump}\ninputs:\n  - size: 172\n    owner: prover\n")).unwrap();
        let program = Program::load(&dir.join("g.yaml").display().to_string()).unwrap();
        let m = program.depths();
        let (alice, hub) = (PartyKeys::from_seed(Role::User, Seed::from_label("z/alice")), PartyKeys::from_seed(Role::Hub, Seed::from_label("z/hub")));
        let moves: Vec<Vec<WotsSecret>> = (1..=m).map(|d| program.field_bytes(d).into_iter().enumerate().map(|(f, n)| WotsSecret::from_entropy(WotsParams::for_bytes(n), [d as u8, f as u8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9])).collect()).collect();
        let inputs: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x70 + j as u8; 32])).collect();
        let tail = program.schedule.jump.map(|_| {
            use lngap_ladder::tail::{chunk_fields, TailKeys, CHUNKS};
            let k = |c: usize, f: usize, n: usize| WotsSecret::from_entropy(WotsParams::for_bytes(n as u32), [0xa0 + c as u8, f as u8, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]).public();
            TailKeys { path: (0..CHUNKS).map(|c| chunk_fields(c).iter().enumerate().map(|(f, n)| k(c, f, *n)).collect()).collect(), hop: (0..CHUNKS).map(|c| k(0x10 + c, 0, 1)).collect() }
        });
        let terms = Terms { id: 42, unit: Amount::from_sat(1), bits: 21, low_bits: 9, deposit: 500_000, t_close: 1_000, reserve_alice: Amount::from_sat(20_000), reserve_hub: Amount::from_sat(2_000_000) };
        let spec = Spec {
            terms,
            cid: 42,
            params: ChannelParams::regtest(Amount::from_sat(20_000_000)),
            pubs: [alice.public(), hub.public()],
            b_word: 41,
            checks: vec![Check { name: "memo".into(), word: 42, value: 42, in_claim: true }],
            moves: moves.iter().map(|ks| ks.iter().map(|k| k.public()).collect()).collect(),
            inputs: inputs.iter().map(|k| k.public()).collect(),
            tail,
            windows: None,
        };
        let c = Contract::new(spec, &program).unwrap();
        let set = c.presign(OutPoint { txid: Txid::all_zeros(), vout: 0 }).unwrap();
        // a link's size is its floor less its anchor
        let size = |name: &str| -> u64 {
            let p = set.iter().find(|p| p.name == name).unwrap_or_else(|| panic!("{name}"));
            let input: Amount = std::iter::once(p.prevout.value).chain(p.extra.iter().map(|e| e.0.value)).sum();
            let outs: Amount = p.tx.output.iter().map(|o| o.value).sum();
            (input - outs).to_sat()
        };
        let label = format!("{nary}-ary{}", if jump { ", a jump list" } else { "" });
        println!("SIZES {label}: {m} depths, {} pre-signed transactions", set.len());
        println!("SIZES {label}: escalate {} vB, inputs {} vB, the hub's choice {} vB, Alice's round {} vB, the final move {} vB", size("escalate"), size("inputs"), size("move_2"), size("move_3"), size(&format!("move_{m}")));
        let chain: u64 = ["escalate".to_string(), "inputs".to_string()].into_iter().chain((2..=m).map(|j| format!("move_{j}"))).map(|n| size(&n)).sum();
        println!("SIZES {label}: the whole chain of links {chain} vB");
        if jump {
            let combines: Vec<String> = (1..=lngap_ladder::tail::CHUNKS).map(|k| format!("{}", size(&format!("combine_{k}")))).collect();
            println!("SIZES {label}: path_split {} vB; combine_1..8 [{}] vB; hop_1 {} vB", size("path_split"), combines.join(", "), size("hop_1"));
        }
    }
}

/// Windows by obligation: each timeout's lock, and the contracts made
/// before them (no windows) keep the single window and its races.
#[test]
fn windows_set_each_timeout() {
    use lngap_sessions::contract::{Site, Windows};
    let dir = std::env::temp_dir().join(format!("lngap-windows-{}", std::process::id()));
    let pdf = write_program(&dir, 42, &[(9, 42)]).unwrap();
    let program = Program::load(&pdf).unwrap();
    let m = program.depths();
    let (alice, hub) = (PartyKeys::from_seed(Role::User, Seed::from_label("w/alice")), PartyKeys::from_seed(Role::Hub, Seed::from_label("w/hub")));
    let moves: Vec<Vec<WotsSecret>> = (1..=m)
        .map(|d| program.field_bytes(d).into_iter().enumerate().map(|(f, n)| WotsSecret::from_entropy(WotsParams::for_bytes(n), Seed::from_label(&format!("w/move/{d}/{f}")).derive_bytes("wots"))).collect())
        .collect();
    let inputs: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x70 + j as u8; 32])).collect();
    let terms = Terms { id: 42, unit: Amount::from_sat(1), bits: 21, low_bits: 9, deposit: 500_000, t_close: 1_000, reserve_alice: Amount::from_sat(20_000), reserve_hub: Amount::from_sat(100_000) };
    let contract = |windows: Option<Windows>| {
        let spec = Spec {
            terms,
            cid: 42,
            params: ChannelParams::regtest(Amount::from_sat(20_000_000)),
            pubs: [alice.public(), hub.public()],
            b_word: 0,
            checks: vec![Check { name: "memo".into(), word: 1, value: 42, in_claim: true }],
            moves: moves.iter().map(|ks| ks.iter().map(|k| k.public()).collect()).collect(),
            inputs: inputs.iter().map(|k| k.public()).collect(),
            tail: None,
            windows,
        };
        Contract::new(spec, &program)
    };
    let csv = |c: &Contract, j: u32, leaf: &str| c.ladder(j).unwrap().leaf(leaf).unwrap().timelock.csv;
    // before: one window, w = delta + delta' (12 on regtest), the races at
    // the end delta' more
    let old = contract(None).unwrap();
    for (site, lock) in [(Site::Claimed, 12), (Site::Next(1), 12), (Site::Next(2), 12), (Site::ProveAfter, 12), (Site::FinalTimeout, 18), (Site::Carrier, 18), (Site::CarrierSweep, 12), (Site::VerdictAfter, 12), (Site::PathTimeout, 18), (Site::HopTimeout, 12)] {
        assert_eq!(old.lock(site), lock, "{site:?} without windows");
    }
    // by obligation: Alice 14, the hub's choices 10, its heavy moves 16
    let w = Windows { user: 14, hub: 10, path: 16 };
    let new = contract(Some(w)).unwrap();
    for (site, lock) in [(Site::Claimed, 14), (Site::Next(1), 10), (Site::Next(2), 14), (Site::Next(m - 2), 10), (Site::Next(m - 1), 14), (Site::ProveAfter, 16), (Site::FinalTimeout, 30), (Site::Carrier, 16), (Site::CarrierSweep, 16), (Site::VerdictAfter, 14), (Site::PathTimeout, 30), (Site::HopTimeout, 16)] {
        assert_eq!(new.lock(site), lock, "{site:?} with {w:?}");
    }
    // in the trees: after Alice's move the hub's window, after its choice
    // hers; at the last depth her proofs after the hub's window, its
    // timeout after hers too
    assert_eq!(csv(&new, 1, "split_UserWins"), Some(10));
    assert_eq!(csv(&new, 2, "split_HubWins"), Some(14));
    assert_eq!(csv(&new, m, "split_HubWins"), Some(30));
    let prove = new.ladder(m).unwrap().leaves().iter().find(|l| l.name.starts_with("prove_")).unwrap().timelock.csv;
    assert_eq!(prove, Some(16));
    assert_eq!(csv(&old, 1, "split_UserWins"), Some(12));
    assert_eq!(csv(&old, m, "split_HubWins"), Some(18));
    // windows that would let a disprove come too late, or leave the hub
    // no time to post, are refused
    assert!(contract(Some(Windows { user: 6, ..w })).is_err(), "Alice's window within the disprove delay");
    assert!(contract(Some(Windows { path: 6, ..w })).is_err(), "the hub's heavy window within the disprove delay");
    assert!(contract(Some(Windows { hub: 1, ..w })).is_err(), "no time to post");
    let _ = std::fs::remove_dir_all(&dir);
}

/// Everything the contract builds, hashed: the trees, every pre-signed
/// transaction with what its signatures cover, the fold and the payout.
/// A refactor of the contract must leave it unchanged, or open contracts'
/// addresses and signatures break. Two contracts: a jump list's, with
/// windows and an `inputs` link, and one with neither.
#[test]
fn the_fingerprint() {
    use bitcoin::consensus::encode::serialize;
    use bitcoin::hashes::{sha256, HashEngine};
    use lngap_sessions::contract::Windows;
    use lngap_sessions::statement::write_program_with;
    let dir = std::env::temp_dir().join(format!("lngap-fingerprint-{}", std::process::id()));
    let mut got = vec![];
    for (jump, windows, in_claim) in [(true, Some(Windows { user: 14, hub: 10, path: 16 }), false), (false, None, true)] {
        let pdf = write_program_with(&dir.join(format!("{jump}")), 42, &[(9, 42)], 8, jump).unwrap();
        let program = Program::load(&pdf).unwrap();
        let m = program.depths();
        let (alice, hub) = (PartyKeys::from_seed(Role::User, Seed::from_label("f/alice")), PartyKeys::from_seed(Role::Hub, Seed::from_label("f/hub")));
        let moves: Vec<Vec<WotsSecret>> = (1..=m).map(|d| program.field_bytes(d).into_iter().enumerate().map(|(f, n)| WotsSecret::from_entropy(WotsParams::for_bytes(n), Seed::from_label(&format!("f/move/{d}/{f}")).derive_bytes("wots"))).collect()).collect();
        let inputs: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x50 + j as u8; 32])).collect();
        let tail = program.schedule.jump.map(|_| {
            use lngap_ladder::tail::{chunk_fields, TailKeys, CHUNKS};
            let k = |c: usize, f: usize, n: usize| WotsSecret::from_entropy(WotsParams::for_bytes(n as u32), Seed::from_label(&format!("f/tail/{c}/{f}")).derive_bytes("wots")).public();
            TailKeys { path: (0..CHUNKS).map(|c| chunk_fields(c).iter().enumerate().map(|(f, n)| k(c, f, *n)).collect()).collect(), hop: (0..CHUNKS).map(|c| k(0x10 + c, 0, 1)).collect() }
        });
        let terms = Terms { id: 42, unit: Amount::from_sat(1), bits: 21, low_bits: 9, deposit: 500_000, t_close: 1_000, reserve_alice: Amount::from_sat(250_000), reserve_hub: Amount::from_sat(300_000) };
        let spec = Spec {
            terms,
            cid: 42,
            params: ChannelParams::regtest(Amount::from_sat(20_000_000)),
            pubs: [alice.public(), hub.public()],
            b_word: 0,
            checks: vec![Check { name: "memo".into(), word: 1, value: 42, in_claim }],
            moves: moves.iter().map(|ks| ks.iter().map(|k| k.public()).collect()).collect(),
            inputs: inputs.iter().map(|k| k.public()).collect(),
            tail,
            windows,
        };
        let c = Contract::new(spec, &program).unwrap();
        let funding = OutPoint { txid: Txid::from_byte_array([7; 32]), vout: 1 };
        let mut e = sha256::Hash::engine();
        e.input(c.tree().unwrap().script_pubkey().as_bytes());
        for j in 1..=m {
            e.input(c.ladder(j).unwrap().script_pubkey().as_bytes());
        }
        let set = c.presign(funding).unwrap();
        assert!(set.iter().any(|p| p.name == "inputs") == !in_claim, "the inputs link covered");
        for p in set.iter().chain([&c.fold(funding, Amount::from_sat(123_456), Amount::from_sat(1_000)).unwrap()]) {
            e.input(p.name.as_bytes());
            e.input(&[p.link as u8]);
            e.input(&serialize(&p.tx));
            e.input(&serialize(&p.prevout));
            e.input(p.leaf.as_bytes());
            e.input(&p.control.serialize());
            for (o, l, cb) in &p.extra {
                e.input(&serialize(o));
                e.input(l.as_bytes());
                e.input(&cb.serialize());
            }
        }
        for o in c.pay_alice(c.value() - Amount::from_sat(5_000)).unwrap() {
            e.input(&serialize(&o));
        }
        got.push(format!("{}: {} pre-signed, {}", if jump { "jump" } else { "plain" }, set.len(), sha256::Hash::from_engine(e)));
    }
    println!("FINGERPRINT {got:?}");
    assert_eq!(got, ["jump: 63 pre-signed, 224747d3257e361638de2c91039e8d93d90124a8e485f7e07d60e1cf020e1765", "plain: 27 pre-signed, c32987354bd446481c5ae0d7fef12bec81bd2dee2705084e1ff029a5595a0d2e"]);
    let _ = std::fs::remove_dir_all(&dir);
}
