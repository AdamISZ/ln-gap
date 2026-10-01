//! Z3 step 7: the search game end to end on regtest, through the PoS
//! graph (`Game::Zk`, D60/D61). hello-world in binary search (11 rounds,
//! 23 depths); the prover is the user (odd depths), the verifier the hub.
//! Real signed entries, sealed by the venue's roster (its registered
//! check: the state key, the bodies opening the heads, the input signed);
//! the pre-signed graph built by the instance; the node enforcing every
//! timelock.
//!
//! - P1, the proof wins: an honest execution, the verifier challenging
//!   anyway (BitVMX's forced challenge). The verifier claims absence at the
//!   last depth to force the final step out; the prover's refutation parks
//!   the pair; the verifier's disproves don't fire; the prover's
//!   `zk_prove_<class>` spends after delta + delta', not before.
//! - P2, the timeout wins: the prover faked a write at step 40. The search
//!   ends there; the proof is rejected, and the verifier's split pays
//!   after delta + 2 delta', not before.
//! - P3, a malformed round: the verifier's choice at depth 4 doesn't copy
//!   the endpoints. The prover claims absence at 4, the verifier's
//!   refutation parks its own malformed move, and the prover's
//!   `zk_choice` disprove pays.
//! - P4, a stall: the verifier never answers at depth 6; the prover's
//!   claim stands unrefuted and its timeout split pays after delta.
//! - P5, the window order (D59 amended): the prover's final record says a
//!   step other than the state's base. The step still executes, so the
//!   proof would pass, but it isn't spendable inside the verifier's
//!   window, and the verifier's `zk_record_step` disprove takes the pot
//!   first.

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use emulator::decision::challenge::ForceCondition;
use emulator::executor::utils::{FailConfiguration, FailExecute};
use emulator::loader::program_definition::ProgramDefinition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PresignedTx, Role};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsSecret, WotsSig};
use lngap_pos::graph::proposer_witness;
use lngap_pos::instance::{self, mover_at, Game, GameClock, PosInstance};
use lngap_pos::refute::{self, HEAD_CHUNKS, HEAD_CHUNK_START};
use lngap_pos::{Member, PosMiner, SealedBlock};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::{search, Behaviour, Searched};
use lngap_zk::family::{encode_entry, encode_inputs, ZkFamily};
use lngap_zk::final_d60::{input_key_params, input_message, input_words};
use lngap_zk::game::{final_witness, head, play, Entry, Record, Search, State};
use lngap_zk::nibble_witness;

const SEED: [u8; 32] = [0x3d; 32];
const GAME_ID: u16 = 1;
const VALID: [u8; 4] = [0x11; 4];
const FAKE_STEP: u64 = 40;

fn pdf() -> String {
    format!("{}/programs/hello-world-binary.yaml", env!("CARGO_MANIFEST_DIR"))
}

fn members() -> Vec<Member> {
    (0..5u8).map(|i| Member::new([SEED[0] + i; 32])).collect()
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf).unwrap().as_ref().to_vec()
}

fn sign_with(secret: &SecretKey, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tx(&Keypair::from_secret_key(SECP256K1, secret), tx, prev, leaf)
}

fn run_search(name: &str, prover: Behaviour, force: ForceCondition) -> Searched {
    let dir = std::env::temp_dir().join(format!("lngap-zkg-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let s = search(&pdf(), &VALID, &dir, &prover, &Behaviour::default(), force).unwrap().expect("the verifier challenges");
    let _ = std::fs::remove_dir_all(&dir);
    s
}

fn fake_trace(step: u64) -> bitvmx_cpu_definitions::trace::TraceRWStep {
    use bitvmx_cpu_definitions::trace::{TraceStep, TraceWrite};
    let dir = std::env::temp_dir().join(format!("lngap-zkg-{}-honest", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let d = format!("{}/", dir.display());
    emulator::decision::challenge::prover_execute(&pdf(), VALID.to_vec(), &d, &d, true, None, false).unwrap();
    let pd = ProgramDefinition::from_config(&pdf()).unwrap();
    let mut t = pd.get_trace_step(&d, &d, VALID.to_vec(), step, None).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let w = t.trace_step.get_write();
    t.trace_step = TraceStep::new(TraceWrite::new(w.address, w.value ^ 0x100), t.trace_step.get_pc().clone());
    t
}

/// The two parties, their keys and the instance; the venue; the graph.
struct World {
    user: PartyKeys,
    hub: PartyKeys,
    ks: [KeyStore; 2],
    input_keys: Vec<WotsSecret>,
    params: ChannelParams,
    pubs: [lngap_channel::PartyPubKeys; 2],
    inst: PosInstance,
    search: Search,
    miner: PosMiner,
    sealed: std::collections::HashMap<u32, SealedBlock>,
    graph: Vec<PresignedTx>,
    pair_sig: Option<WotsSig>,
}

impl World {
    fn open(rt: &Regtest, id: u32) -> World {
        let user = PartyKeys::from_seed(Role::User, Seed::from_label("zkg/user"));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("zkg/hub"));
        let mut ks = [KeyStore::new(Seed::from_label(&format!("zkg/user-ks/{id}"))), KeyStore::new(Seed::from_label(&format!("zkg/hub-ks/{id}")))];
        let rounds = ProgramDefinition::from_config(&pdf()).unwrap().nary_def().total_rounds() as u32;
        let search = Search { game_id: GAME_ID, rounds };
        let m = search.total();
        let info = ProgramInfo::load(&pdf()).unwrap();
        let offer_u = instance::gen_pos_keys(&mut ks[0], Role::User, id, 1, m, Game::Zk).unwrap();
        let offer_h = instance::gen_pos_keys(&mut ks[1], Role::Hub, id, 1, m, Game::Zk).unwrap();
        let keys = instance::collect_keys(&offer_u, &offer_h, m).unwrap();
        let input_keys: Vec<WotsSecret> = (0..info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0xa0 + j as u8 + id as u8; 32])).collect();
        let family = ZkFamily::new(search, info, input_keys.iter().map(|k| k.public()).collect());
        let mut miner = PosMiner::new(SEED, members());
        let registry = miner.registry(id, m).unwrap();
        let t0 = rt.mtp().unwrap();
        let clock = GameClock { t0, ell: 60, margin: 60 };
        let inst = PosInstance::new(id, Amount::from_sat(600_000), t0 + 100_000, GAME_ID, Game::Zk, clock, keys, registry).unwrap().with_family(family.clone()).unwrap();
        miner.register(id, m, inst.authorship()).unwrap();
        // the venue readouts and the proofs are tens of kvB: the pre-sign
        // fee must clear the relay floor for them
        let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::from_sat(600_000)) };
        let pubs = [user.public(), hub.public()];
        let _ = &family;
        let mut w = World { user, hub, ks, input_keys, params, pubs, inst, search, miner, sealed: Default::default(), graph: vec![], pair_sig: None };
        let ctx = w.ctx();
        let tree = w.inst.tree(&ctx).unwrap();
        let (c_op, c_prev) = rt.fund(&tree.script_pubkey(), w.inst.value).unwrap();
        w.graph = w.inst.graph(&ctx, c_op, &c_prev).unwrap();
        w
    }
    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] }
    }
    fn payment(&self, r: Role) -> &Keypair {
        if r == Role::User {
            &self.user.payment
        } else {
            &self.hub.payment
        }
    }
    fn payout(&self, r: Role) -> ScriptBuf {
        self.pubs[r.idx()].payout_spk.clone()
    }
    fn skel(&self, label: &str) -> &PresignedTx {
        self.graph.iter().find(|p| p.label == label).unwrap_or_else(|| panic!("no skeleton {label}"))
    }
    /// The mover signs and the venue seals entry `e` (with the input at
    /// depth 1).
    fn seal(&mut self, e: &Entry) {
        let id = self.inst.id;
        let mover = mover_at(e.depth);
        let sig = self.ks[mover.idx()].sign_wots(&instance::state_label(id, 1, e.depth), &e.head[4..]).unwrap();
        let mut body = e.body();
        if e.depth == 1 {
            let words = input_words(&VALID);
            let sigs: Vec<_> = words.iter().zip(&self.input_keys).map(|(w, k)| k.sign(&input_message(*w)).unwrap()).collect();
            body.extend(encode_inputs(&words, &sigs));
        }
        let sealer = self.miner.default_sealer(id, e.depth).unwrap();
        let block = self.miner.seal_entry(id, e.depth, sealer, &encode_entry(&e.head, &sig, &body)).unwrap_or_else(|err| panic!("depth {}: {err}", e.depth));
        assert_eq!(block.header.head(), e.head);
        self.sealed.insert(e.depth, block);
    }
    fn head(&self, d: u32) -> [u8; 48] {
        self.sealed[&d].header.head()
    }
    /// Broadcast a pre-signed 2-of-2 skeleton (the claim, a split).
    fn two_of_two(&self, label: &str, extra: Vec<Vec<u8>>) -> Transaction {
        let p = self.skel(label);
        let mut tx = p.tx.clone();
        let sig_u = sign_tx(&self.user.payment, &tx, &p.prevouts[0], &p.leaf.script);
        let sig_h = sign_tx(&self.hub.payment, &tx, &p.prevouts[0], &p.leaf.script);
        let mut w = extra;
        w.push(sig_h);
        w.push(sig_u);
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        tx
    }
    fn claim(&self, rt: &Regtest, d: u32) {
        rt.make_time_final(self.inst.claim_from(d)).unwrap();
        let tx = self.two_of_two(&format!("absent_{d}"), vec![]);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the claim at {d} must mine: {e}"));
        println!("  claim absent_{d}: {} vB", tx.vsize());
    }
    /// The mover's refutation at `d`: the readout of heads d-1 and d, the
    /// pair reveal, the new head's authorship, the proposer, the mover.
    fn refute(&mut self, rt: &Regtest, d: u32) -> (OutPoint, TxOut) {
        let id = self.inst.id;
        let p = self.skel(&format!("absent_{d}/refute")).clone();
        let mut tx = p.tx.clone();
        let a_prev = p.prevouts[0].clone();
        let mover = mover_at(d);
        let new_head = self.head(d);
        let auth = self.ks[mover.idx()].sign_wots(&instance::state_label(id, 1, d), &new_head[4..]).unwrap();
        let new_block = self.sealed[&d].clone();
        let sigs_new: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|j| sign_with(&new_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script)).collect();
        let mut w = if d >= 2 {
            let prev_head = self.head(d - 1);
            let pair = self.ks[mover.idx()].sign_wots(&instance::refute_label(id, 1, d), &[prev_head.as_slice(), new_head.as_slice()].concat()).unwrap();
            let prev_block = &self.sealed[&(d - 1)];
            let sigs_prev: Vec<Vec<u8>> = (0..HEAD_CHUNKS).map(|j| sign_with(&prev_block.attestation.secrets[HEAD_CHUNK_START + j], &tx, &a_prev, &p.leaf.script)).collect();
            self.pair_sig = Some(pair.clone());
            refute::refute_witness_pair(&sigs_prev, &sigs_new, &pair, &[&auth])
        } else {
            let pair = self.ks[mover.idx()].sign_wots(&instance::refute_label(id, 1, d), &new_head).unwrap();
            self.pair_sig = Some(pair.clone());
            refute::refute_witness(&sigs_new, &pair, &auth)
        };
        w.extend(proposer_witness(sign_with(&new_block.proposer_secret, &tx, &a_prev, &p.leaf.script), new_block.proposer));
        w.push(sign_tx(self.payment(mover), &tx, &a_prev, &p.leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &p.leaf.script, &p.control_block);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the refutation at {d} must mine: {e}"));
        println!("  refutation at {d}: {} vB", tx.vsize());
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone())
    }
    /// A runtime spend of the refuted output at `d` through `leaf`: the
    /// witness `below` the pair reveal, `above` it, then `who`'s
    /// signature; paid to `who`.
    fn spend(&self, d: u32, p_op: OutPoint, p_prev: &TxOut, leaf: &str, below: Vec<Vec<u8>>, above: Vec<Vec<u8>>, who: Role) -> Transaction {
        let ctx = self.ctx();
        let tree = self.inst.refuted_tree(&ctx, d).unwrap();
        let l = tree.leaf(leaf).unwrap_or_else(|_| panic!("no leaf {leaf}"));
        let mut tx = lngap_btc::tx::build_spend(p_op, &l.timelock, vec![TxOut { value: p_prev.value - self.params.presign_fee, script_pubkey: self.payout(who) }]);
        let sig = sign_tx(self.payment(who), &tx, p_prev, &l.script);
        let mut w = below;
        w.extend(refute::wots_wire(self.pair_sig.as_ref().expect("the refutation went first")));
        w.extend(above);
        w.push(sig);
        tx.input[0].witness = tapscript_witness(&w, &l.script, &tree.control_block(leaf).unwrap());
        tx
    }
    fn timeout_witness(&mut self, d: u32, code: u8) -> Vec<Vec<u8>> {
        let id = self.inst.id;
        let claimant = mover_at(d).other();
        let reveal = self.ks[claimant.idx()].reveal_uint(&instance::ccode_label(id, 1, d), u32::from(code)).unwrap();
        let mut w = reveal.consumption_order();
        w.reverse();
        w
    }
}

/// The prove leaf's name for the final record's class.
fn prove_name(r: &Record) -> String {
    let k = lngap_zk::guard::key_of(r.read.opcode, r.read.micro).expect("a decodable class");
    format!("zk_prove_{k}")
}

/// Seal a whole played game, then force the final step out.
fn final_dispute(rt: &Regtest, w: &mut World, entries: &[Entry]) -> (OutPoint, TxOut) {
    for e in entries {
        w.seal(e);
    }
    let m = w.search.depths();
    rt.mine(u64::from(w.params.to_self_delay) + 2).unwrap();
    // the verifier (claimant at the prover's depths) claims the last move
    // absent; the prover answers by parking it
    w.claim(rt, m);
    w.refute(rt, m)
}

#[test]
fn zk_game_on_regtest() {
    let rt = Regtest::start().unwrap();
    let a = run_search("A", Behaviour::default(), ForceCondition::ValidInputStepAndHash);
    let fake = fake_trace(FAKE_STEP);
    let b_fail = FailConfiguration { fail_execute: Some(FailExecute { step: FAKE_STEP, fake_trace: fake }), ..Default::default() };
    let b = run_search("B", Behaviour { fail: Some(b_fail) }, ForceCondition::ValidInputWrongStepOrHash);
    let (delta, delta_p) = (ChannelParams::regtest(Amount::ONE_BTC).delta, ChannelParams::regtest(Amount::ONE_BTC).delta_prime);

    // ===== P1: the honest prover's proof wins =====
    {
        println!("P1: honest execution, the final step challenged (step {})", a.step);
        let mut w = World::open(&rt, 1);
        let entries = play(&a, &w.search).unwrap();
        let (p_op, p_prev) = final_dispute(&rt, &mut w, &entries);
        let m = w.search.depths();
        let last = entries.last().unwrap();
        let (state, record) = (last.state, last.record.unwrap());
        rt.mine(u64::from(delta) + 1).unwrap();
        // the verifier's disproves hold on the honest step
        let claim = entries[0].claim.unwrap();
        for (name, below) in [
            ("disprove_zk_record_step", final_witness(&state, &record)),
            ("disprove_zk_halt_exit", [nibble_witness(&record.to_bytes()), nibble_witness(&claim.to_bytes())].concat()),
            ("disprove_zk_halt_hash", [nibble_witness(&state.to_bytes()), nibble_witness(&claim.to_bytes())].concat()),
        ] {
            let tx = w.spend(m, p_op, &p_prev, name, below, vec![], Role::Hub);
            assert!(rt.test_accept(&tx).is_err(), "{name} must not fire on the honest step");
        }
        // the proof waits out the verifier's window
        let proof = w.spend(m, p_op, &p_prev, &prove_name(&record), final_witness(&state, &record), vec![], Role::User);
        let err = rt.test_accept(&proof).expect_err("not in the verifier's window");
        println!("  the proof inside the verifier's window: rejected ({err})");
        rt.mine(u64::from(delta_p)).unwrap();
        let (txid, h) = rt.send_and_confirm(&proof).unwrap();
        println!("  {} proves step {}: {txid} at {h}, {} vB. The prover wins.", prove_name(&record), a.step, proof.vsize());
    }

    // ===== P2: a faked write; the verifier's split wins by timeout =====
    {
        println!("P2: the prover faked a write at step {FAKE_STEP} (disputed step {})", b.step);
        let mut w = World::open(&rt, 2);
        let entries = play(&b, &w.search).unwrap();
        let (p_op, p_prev) = final_dispute(&rt, &mut w, &entries);
        let m = w.search.depths();
        let last = entries.last().unwrap();
        let (state, record) = (last.state, last.record.unwrap());
        rt.mine(u64::from(delta + delta_p) + 1).unwrap();
        let proof = w.spend(m, p_op, &p_prev, &prove_name(&record), final_witness(&state, &record), vec![], Role::User);
        let err = rt.test_accept(&proof).expect_err("a faked write doesn't prove");
        println!("  the proof: rejected ({err})");
        let split = w.two_of_two(&format!("absent_{m}/refuted/split_HubWins"), vec![]);
        assert!(rt.test_accept(&split).is_err(), "the verifier's split waits out the prover's window");
        rt.mine(u64::from(delta_p)).unwrap();
        rt.mine_with(&[split.clone()]).unwrap_or_else(|e| panic!("the verifier's split must mine: {e}"));
        println!("  the verifier's split after delta + 2 delta': {} vB. The verifier wins.", split.vsize());
    }

    // ===== P3: a malformed round, disproved by zk_choice =====
    {
        println!("P3: the verifier's choice at depth 4 doesn't copy the endpoints");
        let mut w = World::open(&rt, 3);
        let entries = play(&a, &w.search).unwrap();
        let bad = State { lo: [0x42; 20], ..entries[3].state };
        let bad4 = Entry { state: bad, head: head(GAME_ID, 4, mover_at(4), &bad.digest(), &bad.claim), ..entries[3].clone() };
        for e in entries[..3].iter().chain([&bad4]) {
            w.seal(e);
        }
        rt.mine(u64::from(w.params.to_self_delay) + 2).unwrap();
        w.claim(&rt, 4);
        let (p_op, p_prev) = w.refute(&rt, 4);
        let below = [nibble_witness(&entries[2].state.to_bytes()), nibble_witness(&bad.to_bytes())].concat();
        let tx = w.spend(4, p_op, &p_prev, "disprove_zk_choice", below, vec![], Role::User);
        assert!(rt.test_accept(&tx).is_err(), "not before delta");
        rt.mine(u64::from(delta) + 1).unwrap();
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("zk_choice must mine: {e}"));
        println!("  zk_choice disproves it: {} vB. The prover wins.", tx.vsize());
    }

    // ===== P4: a stall at depth 6 =====
    {
        println!("P4: the verifier never answers at depth 6");
        let mut w = World::open(&rt, 4);
        let entries = play(&a, &w.search).unwrap();
        for e in &entries[..5] {
            w.seal(e);
        }
        rt.mine(u64::from(w.params.to_self_delay) + 2).unwrap();
        w.claim(&rt, 6);
        let wit = w.timeout_witness(6, 0);
        let split = w.two_of_two("absent_6/split_UserWins", wit);
        assert!(rt.test_accept(&split).is_err(), "the timeout waits out delta");
        rt.mine(u64::from(delta) + 1).unwrap();
        rt.mine_with(&[split.clone()]).unwrap_or_else(|e| panic!("the timeout split must mine: {e}"));
        println!("  the prover's timeout split: {} vB. The prover wins.", split.vsize());
    }

    // ===== P5: a record whose step isn't the base: disproved in the
    // verifier's window, before the proof could spend =====
    {
        println!("P5: the prover's final record names the wrong step");
        let mut w = World::open(&rt, 5);
        let mut entries = play(&a, &w.search).unwrap();
        let n = entries.len();
        let r = Record { step: entries[n - 1].record.unwrap().step + 1, ..entries[n - 1].record.unwrap() };
        entries[n - 1] = w.search.final_move(&entries[n - 2], r);
        let (p_op, p_prev) = final_dispute(&rt, &mut w, &entries);
        let m = w.search.depths();
        let state = entries[n - 1].state;
        let proof = w.spend(m, p_op, &p_prev, &prove_name(&r), final_witness(&state, &r), vec![], Role::User);
        rt.mine(u64::from(delta) + 1).unwrap();
        assert!(rt.test_accept(&proof).is_err(), "the proof can't race the verifier's window");
        let tx = w.spend(m, p_op, &p_prev, "disprove_zk_record_step", final_witness(&state, &r), vec![], Role::Hub);
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("zk_record_step must mine: {e}"));
        println!("  zk_record_step disproves it inside the verifier's window: {} vB. The verifier wins.", tx.vsize());
    }
}

/// The read challenge (D62) end to end on regtest: phases 1 and 2 sealed
/// (47 depths), the verifier forcing the prover's terminal move out with an
/// absence claim at 47, the prover parking it, then:
///
/// - R1 (a faked read): the verifier's `zk_read_value_2`, with its write
///   at step 600 as witness, takes the pot;
/// - R2 (the same with lying hashes): the verifier's `zk_correct_hash`;
/// - R3 (an honest prover, the challenge forced): no read leaf fires, and
///   the prover's split pays after delta + delta'.
#[test]
fn read_challenge_on_regtest() {
    use bitvmx_cpu_definitions::challenge::ChallengeType;
    use emulator::decision::challenge::ForceChallenge;
    use emulator::executor::utils::FailReads;
    use lngap_zk::dispute::search_with_read;
    use lngap_zk::game::play_read;
    use lngap_zk::Step;

    let strs = |v: &[&str]| -> Vec<String> { v.iter().map(|x| x.to_string()).collect() };
    let fail_read_2 = FailConfiguration::new_fail_reads(FailReads::new(None, Some(&strs(&["1106", "0xaa000000", "0x11111100", "0xaa000000", "600"]))));
    let fail_write = FailConfiguration::new_fail_write(emulator::executor::utils::FailWrite::new(&strs(&["600", "0xaa000000", "0x11111100", "0xaa000000"])));
    let rt = Regtest::start().unwrap();
    let (delta, delta_p) = (ChannelParams::regtest(Amount::ONE_BTC).delta, ChannelParams::regtest(Amount::ONE_BTC).delta_prime);
    let cases = [
        ("R1", Behaviour { fail: Some(fail_read_2.clone()) }, Behaviour::default(), ForceCondition::ValidInputWrongStepOrHash, ForceChallenge::No),
        ("R2", Behaviour { fail: Some(fail_read_2) }, Behaviour { fail: Some(fail_write) }, ForceCondition::ValidInputWrongStepOrHash, ForceChallenge::No),
        ("R3", Behaviour::default(), Behaviour::default(), ForceCondition::ValidInputStepAndHash, ForceChallenge::ReadValueNArySearch),
    ];
    for (i, (name, prover, prover_read, fc, force)) in cases.into_iter().enumerate() {
        let dir = std::env::temp_dir().join(format!("lngap-zkg-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let (s, r) = search_with_read(&pdf(), &VALID, &dir, &prover, &prover_read, &Behaviour::default(), fc, force, ForceChallenge::No).unwrap().unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        let r = r.expect("a read challenge");
        let mut w = World::open(&rt, 10 + i as u32);
        let p1 = play(&s, &w.search).unwrap();
        let p2 = play_read(&r, &w.search, &p1).unwrap();
        for e in p1.iter().chain(&p2) {
            w.seal(e);
        }
        let m = w.search.total();
        println!("{name}: {} moves sealed; BitVMX chose {}", p1.len() + p2.len(), format!("{:?}", r.challenge).split(' ').next().unwrap());
        rt.mine(u64::from(w.params.to_self_delay) + 2).unwrap();
        // the verifier claims the prover's terminal move absent; the prover
        // parks it
        w.claim(&rt, m);
        let (p_op, p_prev) = w.refute(&rt, m);
        rt.mine(u64::from(delta) + 1).unwrap();
        let rec1 = p1.last().unwrap().record.unwrap();
        let s2 = p2[p2.len() - 2].state;
        let write_of = |t: &bitvmx_cpu_definitions::trace::TraceStep| Step {
            write_addr: t.get_write().address,
            write_value: t.get_write().value,
            pc: t.get_pc().get_address(),
            micro: t.get_pc().get_micro(),
        };
        let read_value = |w: &World, sel: u8, wr: &Step| {
            w.spend(
                m,
                p_op,
                &p_prev,
                &format!("disprove_zk_read_value_{sel}"),
                [nibble_witness(&rec1.to_bytes()), nibble_witness(&s2.to_bytes()), nibble_witness(&wr.to_bytes())].concat(),
                vec![],
                Role::Hub,
            )
        };
        match &r.challenge {
            ChallengeType::ReadValue { trace, read_selector, .. } if name != "R3" => {
                let tx = read_value(&w, *read_selector as u8, &write_of(trace));
                rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("{name}: zk_read_value must mine: {e}"));
                println!("  zk_read_value_{read_selector} (W = step {}'s write): {} vB. The verifier wins.", r.step + 1, tx.vsize());
            }
            ChallengeType::CorrectHash { trace, verifier_hash, .. } => {
                let mut wit = hex::decode(verifier_hash).unwrap();
                wit.extend_from_slice(&write_of(trace).to_bytes());
                let tx = w.spend(m, p_op, &p_prev, "disprove_zk_correct_hash", [nibble_witness(&s2.to_bytes()), nibble_witness(&wit)].concat(), vec![], Role::Hub);
                rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("{name}: zk_correct_hash must mine: {e}"));
                println!("  zk_correct_hash at step {}: {} vB. The verifier wins.", r.step + 1, tx.vsize());
            }
            ChallengeType::ReadValue { trace, .. } => {
                for sel in [1, 2] {
                    assert!(rt.test_accept(&read_value(&w, sel, &write_of(trace))).is_err(), "{name}: read_value_{sel} must not fire on an honest prover");
                }
                rt.mine(u64::from(delta_p)).unwrap();
                let split = w.two_of_two(&format!("absent_{m}/refuted/split_UserWins"), vec![]);
                rt.mine_with(&[split.clone()]).unwrap_or_else(|e| panic!("{name}: the prover's split must mine: {e}"));
                println!("  no read leaf fires; the prover's split: {} vB. The prover wins.", split.vsize());
            }
            c => panic!("{name}: unexpected {c:?}"),
        }
    }
}
