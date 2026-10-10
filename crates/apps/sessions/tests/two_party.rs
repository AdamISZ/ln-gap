//! A dispute played by two separate parties (lngap_sessions::play): Alice
//! and the hub each hold only their own keys and run only their own
//! emulator; neither sees the other's state. Each learns the other's moves
//! by reading the links on chain: the hub reads Alice's claim, her input
//! words and her rounds' hashes; Alice reads the hub's choices; the hub
//! reads her final move and finds the rule that applies (BitVMX's own
//! verifier chooses it), its witness built from what it read.
//!
//! On the mock statement (a table of true returns):
//! - T, a true claim: the honest hub doesn't dispute; Alice wins by
//!   timeout;
//! - R, a true claim, the hub disputes anyway: the whole search, each side
//!   answering what it read; at the end nothing applies, and Alice's proof
//!   pays her;
//! - X, a false claim: the honest hub disputes and wins with the disprove
//!   its verdict names.
//!
//! The trace hashed as a jump list (the read and jump challenges):
//! - J, Alice's disputed step commits to a wrong long-jump hash (an
//!   otherwise valid step that would prove): the hub posts a path to the
//!   long jump and its `jump` verdict wins;
//! - L, Alice lies about a read (a value step L never wrote): the hub
//!   posts a path to step L and its `read` verdict wins;
//! - F, the hub forges a hash in that path: Alice finds it against her own
//!   history and challenges that hop; the hub can't reveal it; her timeout
//!   pays her.

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
use bitcoin::script::Builder;
use lngap_ladder::mover_at;
use lngap_ladder::rules::spends;
use lngap_ladder::script::{rule_wire, wots_wire, Msg};
use lngap_lamport::winternitz::{WotsParams, WotsSecret};
use lngap_sessions::contract::{sign_all, Check, Contract, Program, Spec};
use lngap_sessions::play::{move_wires, read_move, read_words, word_wires, Prover, Verdict, Verifier};
use lngap_sessions::session::Terms;
use lngap_ladder::ladder::TailOut;
use lngap_ladder::tail::{first_fields, second_fields, TailKeys, CHUNK};
use lngap_sessions::play::PathKind;
use lngap_sessions::statement::{input, write_program_with};
use emulator::executor::utils::{FailConfiguration, FailReads};
use lngap_zk::final_d60::{input_key_params, input_message};

/// A contract both parties opened: the shared part (the contract, the
/// pre-signed set with both signatures) and each side's own secrets.
struct Opened {
    program: Program,
    contract: Contract,
    set: HashMap<String, lngap_sessions::contract::Presign>,
    hub_sigs: HashMap<String, Vec<u8>>,
    alice_sigs: HashMap<String, Vec<u8>>,
    // Alice's
    alice_moves: HashMap<u32, Vec<WotsSecret>>,
    inputs: Vec<WotsSecret>,
    // the hub's
    hub: PartyKeys,
    hub_moves: HashMap<u32, Vec<WotsSecret>>,
    /// Under a jump list: the hub's path keys, Alice's choice keys.
    hub_path: Option<[Vec<WotsSecret>; 2]>,
    alice_hop: Option<[WotsSecret; 2]>,
    wallets: [FeeWallet; 2],
}

fn open(rt: &Regtest, dir: &Path, cid: u32, returns: &[(u32, u32)], jump: bool) -> Opened {
    let program = Program::load(&write_program_with(&dir.join(format!("p{cid}")), cid, returns, 2, jump).unwrap()).unwrap();
    let m = program.depths();
    let alice = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("2p/{cid}/alice")));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("2p/{cid}/hub")));
    let key = |who: &str, d: u32| -> Vec<WotsSecret> {
        program.field_bytes(d).into_iter().enumerate().map(|(f, n)| WotsSecret::from_entropy(WotsParams::for_bytes(n), Seed::from_label(&format!("2p/{cid}/{who}/move/{d}/{f}")).derive_bytes("wots"))).collect()
    };
    let alice_moves: HashMap<u32, Vec<WotsSecret>> = (1..=m).filter(|d| mover_at(*d) == Role::User).map(|d| (d, key("alice", d))).collect();
    let hub_moves: HashMap<u32, Vec<WotsSecret>> = (1..=m).filter(|d| mover_at(*d) == Role::Hub).map(|d| (d, key("hub", d))).collect();
    let inputs: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), Seed::from_label(&format!("2p/{cid}/input/{j}")).derive_bytes("wots"))).collect();
    let moves = (1..=m).map(|d| alice_moves.get(&d).or(hub_moves.get(&d)).unwrap().iter().map(|k| k.public()).collect()).collect();
    let terms = Terms { id: cid, unit: Amount::from_sat(1), bits: 21, low_bits: 9, deposit: 500_000, t_close: 5_000, reserve_alice: Amount::from_sat(20_000), reserve_hub: Amount::from_sat(if jump { 300_000 } else { 100_000 }) };
    let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::ZERO) };
    let tk = |who: &str, l: usize, f: usize, n: usize| WotsSecret::from_entropy(WotsParams::for_bytes(n as u32), Seed::from_label(&format!("2p/{cid}/{who}/tail/{l}/{f}")).derive_bytes("wots"));
    let hub_path: Option<[Vec<WotsSecret>; 2]> = jump.then(|| [first_fields().iter().enumerate().map(|(f, n)| tk("hub", 0, f, *n)).collect(), second_fields().iter().enumerate().map(|(f, n)| tk("hub", 1, f, *n)).collect()]);
    let alice_hop = jump.then(|| [tk("alice", 0, 0, 1), tk("alice", 1, 0, 1)]);
    let tail = hub_path.as_ref().zip(alice_hop.as_ref()).map(|(p, h)| TailKeys { path: [p[0].iter().map(|k| k.public()).collect(), p[1].iter().map(|k| k.public()).collect()], hop: [h[0].public(), h[1].public()] });
    let spec = Spec { terms, cid, params, pubs: [alice.public(), hub.public()], b_word: 0, checks: vec![Check { name: "memo".into(), word: 1, value: cid }], moves, inputs: inputs.iter().map(|k| k.public()).collect(), tail };
    let contract = Contract::new(spec, &program).unwrap();
    let (op, _) = rt.fund(&contract.tree().unwrap().script_pubkey(), contract.value()).unwrap();
    let presigned = contract.presign(op).unwrap();
    let (hub_sigs, alice_sigs) = (sign_all(&presigned, &hub.payment).unwrap(), sign_all(&presigned, &alice.payment).unwrap());
    let set = presigned.into_iter().map(|p| (p.name.clone(), p)).collect();
    let wallets = [FeeWallet::new(rt, &alice.payment, m as usize + 4, 2), FeeWallet::new(rt, &hub.payment, m as usize + 4, 2)];
    Opened { program, contract, set, hub_sigs, alice_sigs, alice_moves, inputs, hub, hub_moves, hub_path, alice_hop, wallets }
}

impl Opened {
    fn finish(&self, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        self.set[name].finish(wire, &self.hub_sigs[name], &self.alice_sigs[name])
    }
    /// Post a link, its poster paying with a child; the link as mined.
    fn post(&mut self, rt: &Regtest, name: &str, wire: Vec<Vec<u8>>, by: Role) -> Transaction {
        let tx = self.finish(name, wire);
        rt.send_raw(&tx).unwrap_or_else(|e| panic!("{name} at its floor: {e:#}"));
        let child = self.wallets[by.idx()].bump(&tx, 1);
        rt.send_raw(&child).unwrap_or_else(|e| panic!("{name}'s child: {e:#}"));
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
    fn key(&self, d: u32) -> &[lngap_lamport::winternitz::WotsPublic] {
        &self.contract.spec.moves[(d - 1) as usize]
    }
    /// A move signed with `keys`, field by field, as a link carries it (its
    /// last field first).
    fn sign_move(&self, d: u32, keys: &[WotsSecret], msg: &[u8]) -> Vec<Vec<u8>> {
        let fields = self.program.schedule.fields(d);
        (0..keys.len()).rev().flat_map(|f| { let (o, l) = fields[f]; wots_wire(&keys[f].sign(&msg[o..o + l]).unwrap()) }).collect()
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
    /// No rule applied, and Alice couldn't prove: the hub's timeout.
    Waited,
    /// The hub's path proved its verdict: everything to the hub.
    PathVerdict(String),
    /// Alice refuted a hop of the hub's path: her timeout paid her.
    HopRefuted(usize),
}

/// Alice claims `claim` (her input); the hub, honest or forced, answers.
/// Each side acts only on what it reads from the chain.
fn dispute(rt: &Regtest, dir: &Path, o: &mut Opened, claim: &[u8], force: ForceCondition, alice_fail: Option<FailConfiguration>, forge: bool) -> End {
    let m = o.contract.m();
    let p = o.contract.spec.params;
    let w = p.delta + p.delta_prime;
    // ----- Alice: execute, escalate (move 1 and her claim's words)
    let mut alice = Prover::start_with(&o.program, claim, &dir.join("alice"), alice_fail).unwrap();
    let words = lngap_zk::final_d60::input_words(claim);
    let claim_words = o.contract.claim_words();
    let mut wire: Vec<Vec<u8>> = claim_words.iter().rev().flat_map(|&k| wots_wire(&o.inputs[k].sign(&input_message(words[k])).unwrap())).collect();
    wire.extend(o.sign_move(1, &o.alice_moves[&1], alice.last()));
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
    let mut alice_read: Option<Vec<u8>> = None;
    for j in (2..=m).step_by(2) {
        let choice = hub.choose(alice_read.as_deref()).unwrap();
        let w = o.sign_move(j, &o.hub_moves[&j], &choice);
        o.post(rt, &Opened::link_name(j), w, Role::Hub);
        // Alice reads the hub's move and answers
        let read = read_move(&o.read(rt, &Opened::link_name(j)), o.key(j)).unwrap();
        let next = alice.answer(&read).unwrap();
        let w = o.sign_move(j + 1, &o.alice_moves[&(j + 1)], &next);
        o.post(rt, &Opened::link_name(j + 1), w, Role::User);
        alice_read = Some(read_move(&o.read(rt, &Opened::link_name(j + 1)), o.key(j + 1)).unwrap());
    }
    // ----- the hub reads Alice's final move and finds the rule that applies
    let last = alice_read.unwrap();
    let last_link = o.read(rt, &Opened::link_name(m));
    // a rule's witness from the chain: each message's signature as posted
    let reveal = |msg: &Msg| -> Vec<Vec<u8>> {
        match msg {
            Msg::Field(d, f) => move_wires(&o.read(rt, &Opened::link_name(*d)), o.key(*d)).unwrap()[*f].clone(),
            Msg::Word(k) => {
                let ws = word_wires(&esc, &keys, Some(o.key(1))).unwrap();
                ws[claim_words.iter().position(|j| j == k).expect("a claim word")].clone()
            }
            Msg::Path(..) | Msg::Hop(_) => unreachable!("the tail's rules are built below"),
        }
    };
    let wire_of = |name: &str, wit: &[u8]| -> Vec<Vec<u8>> {
        let rule = o.contract.rule(m, name).unwrap();
        rule_wire(wit, &rule.msgs.iter().map(reveal).collect::<Vec<_>>())
    };
    // Alice's proof, run on her move as read (the hub's check, and hers)
    let proves = |rec: &lngap_zk::game::Record| -> bool {
        let name = format!("prove_{}", lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap());
        let rule = o.contract.rule(m, &name).unwrap();
        let script = rule.script(Builder::new(), &|msg| o.contract.ladder_spec(&o.contract.ctx()).key(msg));
        spends(&script, wire_of(&name, &[])).0
    };
    let verdict = hub.verdict(&last, &proves).unwrap();
    let last_op = OutPoint { txid: last_link.compute_txid(), vout: 0 };
    let last_out = last_link.output[0].clone();
    match verdict {
        Verdict::Disprove(name, wit) => {
            let wire = wire_of(&name, &wit);
            let tree = o.contract.ladder(m).unwrap();
            let leaf_name = format!("disprove_{name}");
            let leaf = tree.leaf(&leaf_name).unwrap();
            let mut tx = build_spend(last_op, &leaf.timelock, vec![TxOut { value: last_out.value - p.presign_fee, script_pubkey: o.contract.spec.pubs[1].payout_spk.clone() }]);
            let mut wire = wire;
            wire.push(sig(&o.hub.payment, &tx, 0, std::slice::from_ref(&last_out), &leaf.script));
            tx.input[0].witness = tapscript_witness(&wire, &leaf.script, &tree.control_block(&leaf_name).unwrap());
            rt.mine(u64::from(p.delta)).unwrap();
            rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("{leaf_name}: {e:#}"));
            End::Disproved(name)
        }
        Verdict::Proved => {
            // Alice proves the last step: her final move re-revealed
            let rec = lngap_ladder::moves::View { s: &o.program.schedule, msgs: &alice.msgs }.record();
            let name = format!("prove_{}", lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap());
            let tx = o.finish(&name, wire_of(&name, &[]));
            let tx = o.wallets[0].pay(tx, &o.set[&name].prevout);
            rt.mine(u64::from(w)).unwrap();
            confirm(rt, &tx).unwrap_or_else(|e| panic!("{name}: {e}"));
            End::Proved
        }
        Verdict::Wait => {
            rt.mine(u64::from(w + p.delta_prime)).unwrap();
            let name = format!("timeout_{m}");
            let t = o.finish(&name, vec![]);
            let t = o.wallets[1].pay(t, &o.set[&name].prevout);
            confirm(rt, &t).unwrap();
            End::Waited
        }
        Verdict::ReadChallenge => panic!("a read challenge without a jump list isn't carried"),
        Verdict::Path { kind, y } => {
            // the hub posts its path over its own history (forged, if `forge`)
            let (mut path, pre_y) = hub.path(y).unwrap();
            if forge {
                let k = path.n() / 2;
                path.hashes[k][0] ^= 1;
            }
            let h_t = lngap_ladder::moves::View { s: &o.program.schedule, msgs: &hub.msgs }.step_hash();
            let (first, second) = path.messages(&h_t);
            let hp = o.hub_path.take().unwrap();
            let sign = |keys: &[WotsSecret], msg: &[u8], sizes: &[usize]| -> Vec<Vec<u8>> {
                let mut at = 0;
                let sigs: Vec<Vec<Vec<u8>>> = keys.iter().zip(sizes).map(|(k, n)| { let w = wots_wire(&k.sign(&msg[at..at + n]).unwrap()); at += n; w }).collect();
                sigs.into_iter().rev().flatten().collect()
            };
            o.post(rt, "path_0", sign(&hp[0], &first, &first_fields()), Role::Hub);
            let link = usize::from(path.n() > CHUNK);
            if link == 1 {
                o.post(rt, "path_1", sign(&hp[1], &second, &second_fields()), Role::Hub);
            }
            // Alice reads the path from the chain and checks it against her
            // own history
            let pk = o.contract.spec.tail.clone().unwrap();
            let read_first = read_move(&o.read(rt, "path_0"), &pk.path[0]).unwrap();
            let read_second = if link == 1 { read_move(&o.read(rt, "path_1"), &pk.path[1]).unwrap() } else { vec![] };
            let p_name = format!("path_{link}");
            let p_tx = o.read(rt, &p_name);
            let (p_op, p_out) = (OutPoint { txid: p_tx.compute_txid(), vout: 0 }, p_tx.output[0].clone());
            let tail_wire = |o: &Opened, rule: &lngap_ladder::rules::Rule, wit: &[u8]| -> Vec<Vec<u8>> {
                let reveals: Vec<Vec<Vec<u8>>> = rule
                    .msgs
                    .iter()
                    .map(|msg| match *msg {
                        Msg::Field(d, f) => move_wires(&o.read(rt, &Opened::link_name(d)), o.key(d)).unwrap()[f].clone(),
                        Msg::Path(l, f) => move_wires(&o.read(rt, &format!("path_{l}")), &pk.path[l]).unwrap()[f].clone(),
                        Msg::Hop(l) => move_wires(&o.read(rt, &format!("hop_{l}")), std::slice::from_ref(&pk.hop[l])).unwrap()[0].clone(),
                        Msg::Word(_) => unreachable!(),
                    })
                    .collect();
                rule_wire(wit, &reveals)
            };
            let hub_spend = |o: &Opened, tree: &lngap_btc::taptree::TapTree, op: OutPoint, out: &TxOut, leaf_name: &str, wire: Vec<Vec<u8>>| -> Transaction {
                let leaf = tree.leaf(leaf_name).unwrap();
                let mut tx = build_spend(op, &leaf.timelock, vec![TxOut { value: out.value - p.presign_fee, script_pubkey: o.contract.spec.pubs[1].payout_spk.clone() }]);
                let mut wire = wire;
                wire.push(sig(&o.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
                tx.input[0].witness = tapscript_witness(&wire, &leaf.script, &tree.control_block(leaf_name).unwrap());
                tx
            };
            match alice.check_path(&read_first, &read_second).unwrap() {
                Some(k) => {
                    // she challenges hop k; the hub can't reveal a forged hop
                    let hk = o.alice_hop.as_ref().unwrap()[link].sign(&[k as u8]).unwrap();
                    o.post(rt, &format!("hop_{link}"), wots_wire(&hk), Role::User);
                    let h_tx = o.read(rt, &format!("hop_{link}"));
                    let (h_op, h_out) = (OutPoint { txid: h_tx.compute_txid(), vout: 0 }, h_tx.output[0].clone());
                    let at = TailOut::Hop(link);
                    let rule = o.contract.tail_rule(at, &format!("hop_{k}")).unwrap();
                    let pre = hub.reveal(&path, k).unwrap();
                    let tree = o.contract.tail_tree(at).unwrap();
                    let reveal = hub_spend(o, &tree, h_op, &h_out, &format!("disprove_hop_{k}"), tail_wire(o, &rule, &pre));
                    rt.mine(u64::from(p.delta)).unwrap();
                    assert!(rt.test_accept(&reveal).is_err(), "a forged hop can't be revealed");
                    rt.mine(u64::from(w)).unwrap();
                    let name = format!("timeout_hop_{link}");
                    let t = o.finish(&name, vec![]);
                    let t = o.wallets[0].pay(t, &o.set[&name].prevout);
                    confirm(rt, &t).unwrap_or_else(|e| panic!("{name}: {e}"));
                    End::HopRefuted(k)
                }
                None => {
                    // the path is genuine: after her window, the hub's verdict
                    let name = match kind {
                        PathKind::Jump => "jump".to_string(),
                        PathKind::Read(r) => format!("read_{r}"),
                    };
                    let at = TailOut::Path(link);
                    let rule = o.contract.tail_rule(at, &name).unwrap();
                    let tree = o.contract.tail_tree(at).unwrap();
                    let tx = hub_spend(o, &tree, p_op, &p_out, &format!("disprove_{name}"), tail_wire(o, &rule, &pre_y));
                    rt.mine(u64::from(w)).unwrap();
                    rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("disprove_{name}: {e:#}"));
                    println!("TWOPARTY the hub's path: {} hops to step {y}, {} link(s); disprove_{name}: {} vB", path.n(), link + 1, tx.vsize());
                    End::PathVerdict(name)
                }
            }
        }
    }
}

/// A step of the honest execution reading an address written earlier: (the
/// step, which read, the address, the value, its last write).
fn a_written_read(program: &Program, claim: &[u8], dir: &Path) -> (u64, u8, u32, u32, u64) {
    let d = format!("{}/", dir.display());
    std::fs::create_dir_all(&d).unwrap();
    let (_, last, _) = emulator::decision::challenge::prover_execute(&program.pdf, claim.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = emulator::loader::program_definition::ProgramDefinition::from_config(&program.pdf).unwrap();
    let (_, trace) = pd.execute_helper(&d, &d, claim.to_vec(), Some((1..=last).collect()), None, false).unwrap();
    let never = bitvmx_cpu_definitions::constants::LAST_STEP_INIT;
    for (t, _) in trace.iter().rev() {
        for (r, rd) in [(2u8, &t.read_2), (1, &t.read_1)] {
            if rd.last_step != never && rd.last_step > 0 && t.step_number > rd.last_step + 2 {
                return (t.step_number, r, rd.address, rd.value, rd.last_step);
            }
        }
    }
    panic!("no read of a written address");
}

#[test]
fn two_parties_play_from_the_chain() {
    let rt = Regtest::start_standard().unwrap();
    let dir = std::env::temp_dir().join(format!("lngap-2p-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let b = 40_000u32;
    // the mock's table: Alice's return of b with memo cid is true
    for (cid, label, claim_b, force, want) in [
        (52u32, "T", b, ForceCondition::No, "Conceded"),
        (53, "R", b, ForceCondition::ValidInputStepAndHash, "Proved"),
        (54, "X", b + 1_000, ForceCondition::No, "Disproved"),
    ] {
        let mut o = open(&rt, &dir, cid, &[(b, cid)], false);
        let t = std::time::Instant::now();
        let honest = matches!(force, ForceCondition::No);
        let end = dispute(&rt, &dir.join(format!("d{cid}")), &mut o, &input(claim_b, cid), force, None, false);
        println!("TWOPARTY {label}: Alice claims {claim_b} (the table has {b}); the hub {}: {end:?} ({:.1?})", if honest { "plays honestly" } else { "disputes anyway" }, t.elapsed());
        assert!(format!("{end:?}").starts_with(want), "{label}: {end:?}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// The read and jump challenges (J4). Ignored for now: the hub's path
/// link carries more one-time signatures than one input's 1,000-item stack
/// holds (JUMPLIST_PLAN.md, PROGRESS).
#[test]
#[ignore]
fn the_read_and_jump_challenges() {
    let rt = Regtest::start_standard().unwrap();
    let dir = std::env::temp_dir().join(format!("lngap-2pj-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let b = 40_000u32;
    let claim = input(b, 55);
    let probe = open(&rt, &dir, 55, &[(b, 55)], true);
    let (rs, r, addr, value, ls) = a_written_read(&probe.program, &claim, &dir.join("probe"));
    // J: a wrong long-jump hash at the step after the read's (its write valid)
    let fail_j = FailConfiguration { fail_jump: Some(rs), ..Default::default() };
    // L: a lying read at step rs (the value step ls didn't write)
    let args: Vec<String> = [rs.to_string(), format!("{addr:#x}"), format!("{:#x}", value ^ 1), format!("{addr:#x}"), ls.to_string()].into();
    let fail_l = FailConfiguration::new_fail_reads(if r == 1 { FailReads::new(Some(&args), None) } else { FailReads::new(None, Some(&args)) });
    for (cid, label, fail, forge, want) in [
        (55u32, "J", fail_j.clone(), false, "PathVerdict(\"jump\")"),
        (56, "L", fail_l.clone(), false, "PathVerdict(\"read_"),
        (57, "F", fail_l, true, "HopRefuted"),
    ] {
        let mut o = open(&rt, &dir, cid, &[(b, cid)], true);
        let t = std::time::Instant::now();
        let end = dispute(&rt, &dir.join(format!("d{cid}")), &mut o, &input(b, cid), ForceCondition::ValidInputWrongStepOrHash, Some(fail), forge);
        println!("TWOPARTY {label} (a jump list; step {rs}'s read {r} of {addr:#x}, written at {ls}): {end:?} ({:.1?})", t.elapsed());
        assert!(format!("{end:?}").starts_with(want), "{label}: {end:?}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}
