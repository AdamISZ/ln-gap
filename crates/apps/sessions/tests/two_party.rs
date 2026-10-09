//! A dispute played by two separate parties (lngap_sessions::play): Alice
//! and the hub each hold only their own keys and run only their own
//! emulator; neither sees the other's state. Each learns the other's moves
//! by reading the links on chain: the hub reads Alice's claim, her input
//! words and her midpoints; Alice reads the hub's choices; the hub reads
//! her final record and finds the disprove that applies, its witness built
//! from what it read.
//!
//! On the mock statement (a table of true returns):
//! - T, a true claim: the honest hub doesn't dispute; Alice wins by
//!   timeout;
//! - R, a true claim, the hub disputes anyway: the whole search, each side
//!   answering what it read; at the end nothing applies, and Alice's proof
//!   pays her;
//! - X, a false claim: the honest hub disputes and wins with the disprove
//!   its verdict names.

mod common;

use std::collections::HashMap;
use std::path::Path;

use bitcoin::{Amount, OutPoint, Transaction, TxOut};
use common::{confirm, sig, FeeWallet};
use emulator::decision::challenge::ForceCondition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, PartyKeys, Role};
use lngap_lamport::winternitz::{WotsParams, WotsSecret};
use lngap_pos::instance::mover_at;
use lngap_pos::rebut::wots_wire;
use lngap_sessions::contract::{move_bytes, move_message, sign_all, Check, Contract, Program, Spec};
use lngap_sessions::play::{disprove_witness, move_wire, read_move, read_words, Prover, Verdict, Verifier};
use lngap_sessions::session::Terms;
use lngap_sessions::statement::{input, write_program};
use lngap_zk::final_d60::{input_key_params, input_message};
use lngap_zk::game::final_witness;

/// A contract both parties opened: the shared part (the contract, the
/// pre-signed set with both signatures) and each side's own secrets.
struct Opened {
    program: Program,
    contract: Contract,
    set: HashMap<String, lngap_sessions::contract::Presign>,
    hub_sigs: HashMap<String, Vec<u8>>,
    alice_sigs: HashMap<String, Vec<u8>>,
    // Alice's
    alice_moves: HashMap<u32, WotsSecret>,
    inputs: Vec<WotsSecret>,
    // the hub's
    hub: PartyKeys,
    hub_moves: HashMap<u32, WotsSecret>,
    wallets: [FeeWallet; 2],
}

fn open(rt: &Regtest, dir: &Path, cid: u32, returns: &[(u32, u32)]) -> Opened {
    let program = Program::load(&write_program(&dir.join(format!("p{cid}")), cid, returns).unwrap()).unwrap();
    let m = program.depths();
    let alice = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("2p/{cid}/alice")));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("2p/{cid}/hub")));
    let key = |who: &str, d: u32| WotsSecret::from_entropy(WotsParams::for_bytes(move_bytes(d, m)), Seed::from_label(&format!("2p/{cid}/{who}/move/{d}")).derive_bytes("wots"));
    let alice_moves: HashMap<u32, WotsSecret> = (1..=m).filter(|d| mover_at(*d) == Role::User).map(|d| (d, key("alice", d))).collect();
    let hub_moves: HashMap<u32, WotsSecret> = (1..=m).filter(|d| mover_at(*d) == Role::Hub).map(|d| (d, key("hub", d))).collect();
    let inputs: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), Seed::from_label(&format!("2p/{cid}/input/{j}")).derive_bytes("wots"))).collect();
    let moves = (1..=m).map(|d| alice_moves.get(&d).or(hub_moves.get(&d)).unwrap().public()).collect();
    let terms = Terms { id: cid, unit: Amount::from_sat(1), bits: 21, low_bits: 9, deposit: 500_000, t_close: 5_000, reserve_alice: Amount::from_sat(20_000), reserve_hub: Amount::from_sat(30_000) };
    let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::ZERO) };
    let spec = Spec { terms, cid, params, pubs: [alice.public(), hub.public()], b_word: 0, checks: vec![Check { name: "memo".into(), word: 1, value: cid }], moves, inputs: inputs.iter().map(|k| k.public()).collect() };
    let contract = Contract::new(spec, &program).unwrap();
    let (op, _) = rt.fund(&contract.tree().unwrap().script_pubkey(), contract.value()).unwrap();
    let presigned = contract.presign(op).unwrap();
    let (hub_sigs, alice_sigs) = (sign_all(&presigned, &hub.payment).unwrap(), sign_all(&presigned, &alice.payment).unwrap());
    let set = presigned.into_iter().map(|p| (p.name.clone(), p)).collect();
    let wallets = [FeeWallet::new(rt, &alice.payment, m as usize + 4, 2), FeeWallet::new(rt, &hub.payment, m as usize + 4, 2)];
    Opened { program, contract, set, hub_sigs, alice_sigs, alice_moves, inputs, hub, hub_moves, wallets }
}

impl Opened {
    fn finish(&self, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        self.set[name].finish(wire, &self.hub_sigs[name], &self.alice_sigs[name])
    }
    /// Post a link, its poster paying with a child; the link as mined.
    fn post(&mut self, rt: &Regtest, name: &str, wire: Vec<Vec<u8>>, by: Role) -> Transaction {
        let tx = self.finish(name, wire);
        let child = self.wallets[by.idx()].bump(&tx, 1);
        rt.submit_package(&[tx.clone(), child]).unwrap_or_else(|e| panic!("{name}: {e:#}"));
        rt.mine(1).unwrap();
        rt.get_tx(&tx.compute_txid()).unwrap()
    }
    /// A link as the other side finds it: by the txid the pre-signed set
    /// fixed.
    fn read(&self, rt: &Regtest, name: &str) -> Transaction {
        rt.get_tx(&self.set[name].tx.compute_txid()).unwrap_or_else(|e| panic!("{name} is not on chain: {e:#}"))
    }
    fn link_name(j: u32) -> String {
        if j == 1 { "escalate".into() } else { format!("move_{j}") }
    }
    fn key(&self, d: u32) -> &lngap_lamport::winternitz::WotsPublic {
        &self.contract.spec.moves[(d - 1) as usize]
    }
}

/// How the dispute ended.
#[derive(Debug, PartialEq, Eq)]
enum End {
    /// The hub didn't dispute; Alice's timeout paid her.
    Conceded,
    /// Alice proved the last step: paid.
    Proved,
    /// The hub's disprove: everything to the hub.
    Disproved(String),
}

/// Alice claims `claim` (her input); the hub, honest or forced, answers.
/// Each side acts only on what it reads from the chain.
fn dispute(rt: &Regtest, dir: &Path, o: &mut Opened, claim: &[u8], force: ForceCondition) -> End {
    let m = o.contract.m();
    let p = o.contract.spec.params;
    let w = p.delta + p.delta_prime;
    // ----- Alice: execute, escalate (move 1 and her claim's words)
    let mut alice = Prover::start(&o.program, claim, &dir.join("alice")).unwrap();
    let words = lngap_zk::final_d60::input_words(claim);
    let claim_words = o.contract.claim_words();
    let mut wire: Vec<Vec<u8>> = claim_words.iter().rev().flat_map(|&k| wots_wire(&o.inputs[k].sign(&input_message(words[k])).unwrap())).collect();
    wire.extend(wots_wire(&o.alice_moves[&1].sign(&move_message(alice.last())).unwrap()));
    rt.mine(u64::from(p.to_self_delay)).unwrap();
    o.post(rt, "escalate", wire, Role::User);
    assert!(o.contract.rest_words().is_empty(), "the mock's words are all the claim's");

    // ----- the hub: read the claim and the input from the chain
    let esc = o.read(rt, "escalate");
    let keys: Vec<_> = claim_words.iter().map(|&j| o.contract.spec.inputs[j].clone()).collect();
    let read: Vec<u32> = read_words(&esc, &keys, Some(o.key(1))).unwrap();
    let input_read: Vec<u8> = read.iter().flat_map(|w| w.to_le_bytes()).collect();
    let move1 = read_move(&esc, o.key(1)).unwrap();
    let Some(mut hub) = Verifier::start(&o.program, &input_read, &dir.join("hub"), &move1, force).unwrap() else {
        // nothing to dispute: Alice's timeout pays her after w
        rt.mine(u64::from(w)).unwrap();
        let t = o.finish("timeout_1", vec![]);
        let t = o.wallets[0].pay(t, &o.set["timeout_1"].prevout);
        confirm(rt, &t).unwrap();
        return End::Conceded;
    };
    // ----- the search: each move posted by its mover, read by the other
    let mut alice_head: Option<Vec<u8>> = None;
    for j in (2..=m).step_by(2) {
        let choice = hub.choose(alice_head.as_deref()).unwrap();
        let sig = o.hub_moves[&j].sign(&move_message(&choice)).unwrap();
        o.post(rt, &Opened::link_name(j), wots_wire(&sig), Role::Hub);
        // Alice reads the hub's move and answers
        let read = read_move(&o.read(rt, &Opened::link_name(j)), o.key(j)).unwrap();
        let next = alice.answer(&read).unwrap();
        let sig = o.alice_moves[&(j + 1)].sign(&move_message(&next)).unwrap();
        o.post(rt, &Opened::link_name(j + 1), wots_wire(&sig), Role::User);
        alice_head = Some(read_move(&o.read(rt, &Opened::link_name(j + 1)), o.key(j + 1)).unwrap());
    }
    // ----- the hub reads Alice's record and finds the disprove that applies
    let last = alice_head.unwrap();
    let names: Vec<String> = o.contract.ladder(m).unwrap().leaves().iter().filter_map(|l| l.name.strip_prefix("disprove_zk_").map(|n| format!("zk_{n}"))).collect();
    let verdict = hub.verdict(&last, &names).unwrap();
    let (prior_link, last_link) = (o.read(rt, &Opened::link_name(m - 1)), o.read(rt, &Opened::link_name(m)));
    let file = [move_wire(&prior_link, o.key(m - 1)).unwrap(), move_wire(&last_link, o.key(m)).unwrap()].concat();
    let last_op = OutPoint { txid: last_link.compute_txid(), vout: 0 };
    let last_out = last_link.output[0].clone();
    match verdict {
        Verdict::Disprove(name) => {
            let e = hub.entries.last().unwrap().clone();
            let state = hub.entries[hub.entries.len() - 2].state;
            let wit = disprove_witness(&o.contract, &o.program, &name, &state, &e.record.unwrap(), &hub.claim(), file).unwrap();
            let tree = o.contract.ladder(m).unwrap();
            let leaf_name = format!("disprove_{name}");
            let leaf = tree.leaf(&leaf_name).unwrap();
            let mut tx = build_spend(last_op, &leaf.timelock, vec![TxOut { value: last_out.value - p.presign_fee, script_pubkey: o.contract.spec.pubs[1].payout_spk.clone() }]);
            let mut wit = wit;
            wit.push(sig(&o.hub.payment, &tx, 0, std::slice::from_ref(&last_out), &leaf.script));
            tx.input[0].witness = tapscript_witness(&wit, &leaf.script, &tree.control_block(&leaf_name).unwrap());
            rt.mine(u64::from(p.delta)).unwrap();
            rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("{leaf_name}: {e:#}"));
            End::Disproved(name)
        }
        Verdict::Proved => {
            // Alice proves the last step with her own record and state
            let e = alice.last().clone();
            let state = alice.entries[alice.entries.len() - 2].state;
            let rec = e.record.unwrap();
            let class = lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap();
            let name = format!("prove_{class}");
            let tx = o.finish(&name, [final_witness(&state, &rec), file].concat());
            let tx = o.wallets[0].pay(tx, &o.set[&name].prevout);
            rt.mine(u64::from(w)).unwrap();
            confirm(rt, &tx).unwrap_or_else(|e| panic!("{name}: {e}"));
            End::Proved
        }
    }
}

#[test]
fn two_parties_play_from_the_chain() {
    let rt = Regtest::start().unwrap();
    let dir = std::env::temp_dir().join(format!("lngap-2p-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let b = 40_000u32;
    // the mock's table: Alice's return of b with memo cid is true
    for (cid, label, claim_b, force, want) in [
        (52u32, "T", b, ForceCondition::No, "Conceded"),
        (53, "R", b, ForceCondition::ValidInputStepAndHash, "Proved"),
        (54, "X", b + 1_000, ForceCondition::No, "Disproved"),
    ] {
        let mut o = open(&rt, &dir, cid, &[(b, cid)]);
        let t = std::time::Instant::now();
        let honest = matches!(force, ForceCondition::No);
        let end = dispute(&rt, &dir.join(format!("d{cid}")), &mut o, &input(claim_b, cid), force);
        println!("TWOPARTY {label}: Alice claims {claim_b} (the table has {b}); the hub {}: {end:?} ({:.1?})", if honest { "plays honestly" } else { "disputes anyway" }, t.elapsed());
        assert!(format!("{end:?}").starts_with(want), "{label}: {end:?}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
