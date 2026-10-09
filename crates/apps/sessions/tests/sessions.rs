//! LN-GAP v3 on regtest (research/lngap_v3.pdf): sessions over a toy L2,
//! no venue, on lngap_sessions::contract. The contract output carries `fold`, `default` and `escalate`; a
//! dispute is BitVMX's search played on the ladder from move 1.
//!
//! The fast test runs the withdrawal statement mocked by a BitVMX program
//! (`guest/`):
//! - F, the cooperative withdrawal: activation by a hashlocked transfer,
//!   a return of b on the L2, the hub's check, the fold: nothing on chain;
//! - H8: the session output carries only `default` and `escalate`;
//! - R, the hub refuses a valid claim: Alice escalates (move 1 and her
//!   signed input words); the whole search on the ladder; her pre-signed
//!   proof pays the binary-decomposed b and both reserves;
//! - X, Alice claims a return that isn't on the L2: the search on the
//!   ladder; her execution halts with exit 1; `halt_exit` gives the hub
//!   everything;
//! - S, the hub has disappeared: Alice escalates; nobody answers; the
//!   timeout pays b and both reserves; A6, had she signed two values of b,
//!   the hub takes a bit output and the reserve output with `equiv_b`;
//! - P, Alice probes: a false claim, abandoned when the hub answers; the
//!   hub's timeout takes everything, her reserve included;
//! - M, Alice's words sign another session's memo: the hub's `memo` check
//!   on the first ladder output takes everything;
//! - E1, off-chain play, then Alice disappears: the hub escalates,
//!   replays the moves made from the signatures it holds, and wins by
//!   timeout (an honest absentee loses her reserve);
//! - Q, a cheating replay: the hub escalates after off-chain play and
//!   posts its own move 2 altered, then Alice's move 3 (which no longer
//!   follows from it, so the hub could disprove it after delta); Alice
//!   shows the hub's two signatures at depth 2 with `equiv_d_2` at once
//!   and takes everything;
//! - D, the default: no withdrawal by T_close; the pre-signed default
//!   returns Alice's reserve and pays the hub.
//!
//! The opt-in test runs R, X and the input checks on the real statement
//! program, BitVMX's Groth16 verifier (59 depths), and measures a whole
//! dispute on chain.
//!
//! Run with `--test-threads=1` or 2.

use std::collections::HashMap;
use std::time::Instant;

use bitcoin::hashes::Hash;
use bitcoin::key::Keypair;
use bitcoin::secp256k1::SECP256K1;
use bitcoin::{Amount, OutPoint, Transaction, TxOut};
use emulator::decision::challenge::ForceCondition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, Role};
use lngap_lamport::winternitz::{WotsParams, WotsPublic, WotsSecret, WotsSig};
use lngap_pos::instance::mover_at;
use lngap_pos::rebut::wots_wire;
use lngap_sessions::contract::{move_bytes, move_message, Check, Contract, Presign, Program, Spec, GAME_ID};
use lngap_sessions::l2::{Op, HUB, L2};
use lngap_sessions::session::{bit_tree, reserve_tree, Terms};
use lngap_sessions::statement::{input, write_program};
use lngap_zk::dispute::{search, Behaviour};
use lngap_zk::final_d60::{input_key_params, input_message, input_words};
use lngap_zk::game::{final_witness, play, Entry, Search};
use lngap_zk::nibble_witness;


mod common;
use common::{confirm, sig, FeeWallet};

// -------------------------------------------------------------- session

/// One contract between Alice (the user, the prover) and the hub, built by
/// lngap_sessions::contract (the code lichen runs); both parties' keys are
/// here, so the test plays either side.
struct Session {
    terms: Terms,
    /// The contract's number (labels, keys); the memo `c` is `terms.id`.
    cid: u32,
    user: PartyKeys,
    hub: PartyKeys,
    contract: Contract,
    /// Alice's input-word keys, one per word of the statement's input.
    input_secrets: Vec<WotsSecret>,
    /// The move keys (lean moves), by depth: depth `d`'s mover signs its
    /// head with `moves[d - 1]`. Held as secrets so that a test can make a
    /// party equivocate.
    moves: Vec<WotsSecret>,
    pdf: String,
    /// The claim: the input's words (what Alice signs), the search's heads
    /// and entries.
    words: Vec<u32>,
    heads: Vec<[u8; 48]>,
    entries: Vec<Entry>,
    /// The pre-signed set (once funded), by name.
    set: HashMap<String, Presign>,
    /// Alice's fee coins and the hub's (set when the contract is funded).
    wallets: Vec<FeeWallet>,
}

impl Session {
    fn new(terms: Terms, pdf: &str) -> Session {
        let checks = vec![Check { name: "memo".into(), word: 1, value: terms.id }];
        Session::with(terms, terms.id, pdf, 0, checks)
    }
    /// A contract on any statement program: contract number `cid`, `b` in
    /// input word `b_word`, the input-word `checks`.
    fn with(terms: Terms, cid: u32, pdf: &str, b_word: usize, checks: Vec<Check>) -> Session {
        let id = cid;
        let user = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("sess/{id}/alice")));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("sess/{id}/hub")));
        let program = Program::load(pdf).unwrap();
        let m = program.depths();
        let moves: Vec<WotsSecret> = (1..=m).map(|d| WotsSecret::from_entropy(WotsParams::for_bytes(move_bytes(d, m)), Seed::from_label(&format!("sess/{id}/move/{d}")).derive_bytes("wots"))).collect();
        let input_secrets: Vec<WotsSecret> = (0..program.info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x60u8.wrapping_add(j as u8).wrapping_add(id as u8); 32])).collect();
        // the runtime spends' fee comes from the output they take
        let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::from_sat(20_000_000)) };
        let spec = Spec {
            terms,
            cid,
            params,
            pubs: [user.public(), hub.public()],
            b_word,
            checks,
            moves: moves.iter().map(|k| k.public()).collect(),
            inputs: input_secrets.iter().map(|k| k.public()).collect(),
        };
        let contract = Contract::new(spec, &program).unwrap();
        Session { terms, cid, user, hub, contract, input_secrets, moves, pdf: pdf.to_string(), words: vec![], heads: vec![], entries: vec![], set: HashMap::new(), wallets: vec![] }
    }
    fn m(&self) -> u32 {
        self.contract.m()
    }
    fn params(&self) -> &ChannelParams {
        &self.contract.spec.params
    }
    fn pubs(&self) -> &[PartyPubKeys; 2] {
        &self.contract.spec.pubs
    }
    fn ctx(&self) -> CommitCtx<'_> {
        self.contract.ctx()
    }
    fn b_key(&self) -> WotsPublic {
        self.contract.b_key().clone()
    }
    /// Alice's signature on her claimed `b`.
    fn b_sig(&self, b: u32) -> WotsSig {
        self.input_secrets[self.contract.spec.b_word].sign(&input_message(b)).unwrap()
    }
    /// Play the search on Alice's claim `(b, c)` (the mock statement).
    fn play(&mut self, b: u32) {
        self.play_input(&input(b, self.terms.id), &format!("b = {b}"));
    }
    /// Play the search on the statement program run on `inp`: BitVMX's
    /// parties, the hub challenging; the game's entries.
    fn play_input(&mut self, inp: &[u8], what: &str) {
        let dir = std::env::temp_dir().join(format!("lngap-sess-{}-{}", std::process::id(), self.cid));
        let _ = std::fs::remove_dir_all(&dir);
        let s = search(&self.pdf, inp, &dir, &Behaviour::default(), &Behaviour::default(), ForceCondition::ValidInputStepAndHash).unwrap().expect("the hub challenges");
        let _ = std::fs::remove_dir_all(&dir);
        let rounds = self.m().div_ceil(2) - 1;
        self.entries = play(&s, &Search { game_id: GAME_ID, rounds }).unwrap();
        self.heads = self.entries.iter().map(|e| e.head).collect();
        self.words = input_words(inp);
        println!("SESS {}: Alice claims {what}: the program {:?} at step {}", self.cid, s.claim.0, s.claim.1);
    }
    /// Fund the contract output (`fold`, `default`, `escalate`; nothing
    /// either side can spend alone before a withdrawal starts) and build the
    /// pre-signed set against it. The contract output's tree.
    fn fund_session(&mut self, rt: &Regtest) -> TapTree {
        let tree = self.contract.tree().unwrap();
        let (op, _) = rt.fund(&tree.script_pubkey(), self.contract.value()).unwrap();
        self.set = self.contract.presign(op).unwrap().into_iter().map(|p| (p.name.clone(), p)).collect();
        let n = self.m() as usize + 4;
        self.wallets = vec![FeeWallet::new(rt, &self.user.payment, n, 2), FeeWallet::new(rt, &self.hub.payment, n, 2)];
        tree
    }
    fn ladder(&self, j: u32) -> TapTree {
        self.contract.ladder(j).unwrap()
    }
    /// Move `d`: its head (and at depth 1 the claim block, at the last the
    /// record) signed with depth `d`'s key (lean moves).
    fn move_sig(&self, d: u32) -> WotsSig {
        let mut e = self.entries[(d - 1) as usize].clone();
        e.head = self.heads[(d - 1) as usize];
        self.moves[(d - 1) as usize].sign(&move_message(&e)).unwrap()
    }
    /// What the rules at the ladder output after move `d` read: moves
    /// `d - 1` and `d` re-revealed, wire order.
    fn file_wire(&self, d: u32) -> Vec<Vec<u8>> {
        let mut w = if d >= 2 { wots_wire(&self.move_sig(d - 1)) } else { vec![] };
        w.extend(wots_wire(&self.move_sig(d)));
        w
    }
    /// Alice's signature on input word `j` (her claim's value).
    fn word_sig(&self, j: usize) -> WotsSig {
        self.input_secrets[j].sign(&input_message(self.words[j])).unwrap()
    }
    /// Signed input words, wire order (last word first).
    fn words_wire(&self, words: &[usize]) -> Vec<Vec<u8>> {
        words.iter().rev().flat_map(|&k| wots_wire(&self.word_sig(k))).collect()
    }
    /// What a link's witness carries below the signatures: `escalate`,
    /// move 1 with the claim's words; `inputs`, the rest of the input;
    /// `move_<j>`, move `j`.
    fn link_wire(&self, name: &str) -> Vec<Vec<u8>> {
        match name {
            "escalate" => [self.words_wire(&self.contract.claim_words()), wots_wire(&self.move_sig(1))].concat(),
            "inputs" => self.words_wire(&self.contract.rest_words()),
            _ => wots_wire(&self.move_sig(name.trim_start_matches("move_").parse().unwrap())),
        }
    }
    /// A pre-signed transaction of the set, both signatures made now, `wire`
    /// below them.
    fn finish(&self, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let p = &self.set[name];
        p.finish(wire, &p.sign(&self.hub.payment).unwrap(), &p.sign(&self.user.payment).unwrap())
    }
    /// Broadcast a link of the chain: its poster `by` bumps it with a
    /// child (one-parent-one-child package); the child.
    fn broadcast_link(&mut self, rt: &Regtest, tx: &Transaction, by: Role) -> Transaction {
        assert!(rt.test_accept(tx).is_err(), "a link carries no fee of its own");
        let child = self.wallets[by.idx()].bump(tx, 1);
        rt.submit_package(&[tx.clone(), child.clone()]).unwrap_or_else(|e| panic!("{}: the package: {e:#}", self.cid));
        rt.mine(1).unwrap();
        assert!(rt.confirmations(&tx.compute_txid()).unwrap().is_some(), "the link is mined");
        child
    }
    /// Post the link `name`, by `by`: its output, and the link with its
    /// child's size.
    fn post_link(&mut self, rt: &Regtest, name: &str, by: Role) -> (OutPoint, TxOut, Transaction, usize) {
        let tx = self.finish(name, self.link_wire(name));
        let child = self.broadcast_link(rt, &tx, by);
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone(), tx, child.vsize())
    }
    /// Post move `j >= 2`, by `by`.
    fn post(&mut self, rt: &Regtest, j: u32, by: Role) -> (OutPoint, TxOut, Transaction) {
        let (op, out, tx, _) = self.post_link(rt, &format!("move_{j}"), by);
        (op, out, tx)
    }
    /// Escalate, by `by`, after the contract's `to_self_delay`: move 1 with
    /// the claim's words, then (if any are left) the rest of the input.
    /// The ladder output after move 1, and the escalation.
    fn escalate(&mut self, rt: &Regtest, by: Role) -> (OutPoint, TxOut, Transaction) {
        rt.mine(u64::from(self.params().to_self_delay)).unwrap();
        let (mut op, mut out, esc, _) = self.post_link(rt, "escalate", by);
        if self.set.contains_key("inputs") {
            let (o, t, tx, _) = self.post_link(rt, "inputs", by);
            println!("SESS {}: the rest of the input ({} words): {} vB", self.cid, self.contract.rest_words().len(), tx.vsize());
            (op, out) = (o, t);
        }
        (op, out, esc)
    }
    /// A transaction that ends the chain, both signatures made now, `wire`
    /// below them; `payer` adds the fee.
    fn terminal(&mut self, name: &str, wire: Vec<Vec<u8>>, payer: Role) -> Transaction {
        let tx = self.finish(name, wire);
        let prevout = self.set[name].prevout.clone();
        self.wallets[payer.idx()].pay(tx, &prevout)
    }
    /// A runtime spend by the hub of `(op, out)` under `tree`'s leaf
    /// `name`, `wire` below its signature: everything to the hub.
    fn hub_takes(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
        let mut tx = build_spend(op, &leaf.timelock, vec![TxOut { value: out.value - self.params().presign_fee, script_pubkey: self.pubs()[1].payout_spk.clone() }]);
        let mut w = wire;
        w.push(sig(&self.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
        tx
    }
    /// A runtime spend by Alice, as `hub_takes`.
    fn alice_takes(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
        let mut tx = build_spend(op, &leaf.timelock, vec![TxOut { value: out.value - self.params().presign_fee, script_pubkey: self.pubs()[0].payout_spk.clone() }]);
        let mut w = wire;
        w.push(sig(&self.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
        tx
    }
    /// Spend bit output `i` of a payout `tx` with Alice's signature on `b`:
    /// by Alice if the bit is set, else by the hub.
    fn spend_bit(&self, rt: &Regtest, tx: &Transaction, i: u32, b: u32) -> Transaction {
        let tree = bit_tree(&self.ctx(), i, &self.b_key()).unwrap();
        let set = (b >> i) & 1 == 1;
        let (name, who, kp) = if set { (format!("alice_bit_{i}"), Role::User, &self.user.payment) } else { (format!("hub_bit_{i}"), Role::Hub, &self.hub.payment) };
        let leaf = tree.leaf(&name).unwrap();
        let prev = tx.output[i as usize].clone();
        let op = OutPoint { txid: tx.compute_txid(), vout: i };
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs()[who.idx()].payout_spk.clone() }]);
        let mut w = wots_wire(&self.b_sig(b));
        w.push(sig(kp, &s, 0, std::slice::from_ref(&prev), &leaf.script));
        s.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(&name).unwrap());
        // the other side's leaf fails on the same signature
        let (other, okp) = if set { (format!("hub_bit_{i}"), &self.hub.payment) } else { (format!("alice_bit_{i}"), &self.user.payment) };
        let oleaf = tree.leaf(&other).unwrap();
        let mut o = s.clone();
        let mut ow = wots_wire(&self.b_sig(b));
        ow.push(sig(okp, &o, 0, std::slice::from_ref(&prev), &oleaf.script));
        o.input[0].witness = tapscript_witness(&ow, &oleaf.script, &tree.control_block(&other).unwrap());
        assert!(rt.test_accept(&o).is_err(), "bit {i}: {other} must fail on b = {b}");
        if set {
            // Alice's leaf waits delta (the hub's equivocation window)
            rt.mine(u64::from(self.params().delta)).unwrap();
        }
        rt.mine_with(std::slice::from_ref(&s)).unwrap_or_else(|e| panic!("bit {i}: {name}: {e:#}"));
        s
    }
    /// Alice takes the reserve output of a payout `tx`, after `delta`.
    fn spend_reserve(&self, rt: &Regtest, tx: &Transaction) -> Transaction {
        let tree = reserve_tree(&self.ctx(), &self.terms, &self.b_key()).unwrap();
        let leaf = tree.leaf("alice_reserve").unwrap();
        let i = self.terms.bits;
        let prev = tx.output[i as usize].clone();
        assert_eq!(prev.value, self.terms.reserves(), "the reserve output holds both reserves");
        let op = OutPoint { txid: tx.compute_txid(), vout: i };
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs()[0].payout_spk.clone() }]);
        let w = vec![sig(&self.user.payment, &s, 0, std::slice::from_ref(&prev), &leaf.script)];
        s.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block("alice_reserve").unwrap());
        let confs = rt.confirmations(&tx.compute_txid()).ok().flatten().unwrap_or(0);
        if confs < self.params().delta.into() {
            assert!(rt.test_accept(&s).is_err(), "the reserve waits delta");
            rt.mine(u64::from(self.params().delta)).unwrap();
        }
        rt.mine_with(std::slice::from_ref(&s)).unwrap_or_else(|e| panic!("alice_reserve: {e:#}"));
        s
    }
    /// The hub takes output `i` of a payout `tx` (a bit output, or `K`,
    /// the reserve output) with two different signatures on `b` (Alice
    /// equivocated). Dry.
    fn equiv(&self, tx: &Transaction, i: u32, b1: u32, b2: u32) -> Transaction {
        let tree = if i < self.terms.bits { bit_tree(&self.ctx(), i, &self.b_key()).unwrap() } else { reserve_tree(&self.ctx(), &self.terms, &self.b_key()).unwrap() };
        let name = format!("equiv_b_{i}");
        let leaf = tree.leaf(&name).unwrap();
        let prev = tx.output[i as usize].clone();
        let op = OutPoint { txid: tx.compute_txid(), vout: i };
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs()[1].payout_spk.clone() }]);
        let mut w = [wots_wire(&self.b_sig(b1)), wots_wire(&self.b_sig(b2))].concat();
        w.push(sig(&self.hub.payment, &s, 0, std::slice::from_ref(&prev), &leaf.script));
        s.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(&name).unwrap());
        s
    }
    /// The whole search on chain, from the escalation to the final step
    /// (Alice's record at depth `m`): the chain was pre-signed whole when
    /// the contract was funded; each link is broadcast by its poster with a
    /// child that pays its fee. The ladder output after the last move and
    /// the dispute's size so far, children included.
    fn play_on_chain(&mut self, rt: &Regtest) -> (OutPoint, TxOut, u64) {
        rt.mine(u64::from(self.params().to_self_delay)).unwrap();
        let mut links = vec![("escalate".to_string(), Role::User)];
        if self.set.contains_key("inputs") {
            links.push(("inputs".to_string(), Role::User));
        }
        links.extend((2..=self.m()).map(|j| (format!("move_{j}"), mover_at(j))));
        let (mut alice, mut hub) = (0u64, 0u64);
        let mut last = None;
        for (name, by) in links {
            let (op, out, tx, child) = self.post_link(rt, &name, by);
            if name == "escalate" || name == "inputs" {
                println!("SESS {}: {name}: {} vB, its child {child} vB", self.cid, tx.vsize());
            }
            *(if by == Role::User { &mut alice } else { &mut hub }) += (tx.vsize() + child) as u64;
            last = Some((op, out));
        }
        println!("SESS {}: the chain pre-signed at funding, each link posted with its child: Alice's {alice} vB, the hub's {hub} vB", self.cid);
        let (op, out) = last.unwrap();
        (op, out, alice + hub)
    }
    /// The final step at the last ladder output: Alice's pre-signed proof.
    fn prove_last(&mut self) -> (Transaction, String) {
        let last = self.entries.last().unwrap().clone();
        let rec = last.record.unwrap();
        let class = lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap();
        let wire = [final_witness(&last.state, &rec), self.file_wire(self.m())].concat();
        (self.terminal(&format!("prove_{class}"), wire, Role::User), format!("zk_prove_{class}"))
    }
    /// The hub's `halt_exit` disprove at the last ladder output.
    fn halt_exit(&self, op: OutPoint, out: &TxOut) -> Transaction {
        let m = self.m();
        let last = self.entries.last().unwrap().clone();
        let (rec, cl) = (last.record.unwrap(), self.entries[0].claim.unwrap());
        self.hub_takes(&self.ladder(m), op, out, "disprove_zk_halt_exit", [nibble_witness(&rec.to_bytes()), nibble_witness(&cl.to_bytes()), self.file_wire(m)].concat())
    }
    /// The hub's input-word check `name` on the first ladder output: with
    /// Alice's signature on word `j` as posted.
    fn check(&self, op: OutPoint, out: &TxOut, name: &str, j: usize) -> Transaction {
        self.hub_takes(&self.ladder(1), op, out, name, wots_wire(&self.word_sig(j)))
    }
}

fn terms(id: u32, t_close: u32) -> Terms {
    Terms { id, unit: Amount::from_sat(100_000), bits: 4, low_bits: 0, deposit: 10, t_close, reserve_alice: Amount::from_sat(200_000), reserve_hub: Amount::from_sat(300_000) }
}

#[test]
fn sessions_on_regtest() {
    let rt = Regtest::start().unwrap();
    let mut l2 = L2::new(Keypair::from_seckey_slice(SECP256K1, &[0x5e; 32]).unwrap());
    l2.submit(Op::Mint { amount: 1_000 }).unwrap();
    let dir = std::env::temp_dir().join(format!("lngap-sess-prog-{}", std::process::id()));

    // ===== F: activation and a cooperative withdrawal =====
    {
        let t = terms(41, 0);
        let s = b"alice's session secret".to_vec();
        let hash = bitcoin::hashes::hash160::Hash::hash(&s).to_byte_array();
        let lock = l2.submit(Op::Lock { to: "alice".into(), amount: t.deposit, hash }).unwrap();
        l2.seal();
        l2.submit(Op::Claim { id: lock, preimage: s.clone() }).unwrap();
        l2.seal();
        // the hub learns s from the L2 and activates the contract
        assert_eq!(l2.balance("alice"), t.deposit);
        l2.submit(Op::Return { from: "alice".into(), amount: 5, memo: t.id }).unwrap();
        l2.seal();
        assert!(l2.is_final_return(5, t.id), "the hub's check of the withdrawal");
        let (alice, hub) = (t.unit * 5 + t.reserve_alice, t.v_max() - t.unit * 5 + t.reserve_hub);
        println!("SESS F: activated (s revealed on the L2), returned 5, folded: Alice {alice}, hub {hub} (each with its reserve back); nothing on chain");
    }
    let t_close = rt.height().unwrap() + 400;
    // Alice's returns on the L2 (R, S, E1, M); X's and P's claims have none
    for (b, c) in [(9u32, 42u32), (12, 44), (3, 48), (5, 47)] {
        l2.submit(Op::Transfer { from: HUB.into(), to: "alice".into(), amount: b }).unwrap();
        l2.submit(Op::Return { from: "alice".into(), amount: b, memo: c }).unwrap();
    }
    l2.seal();
    let returns = l2.final_returns();
    let pdf = |id: u32| write_program(&dir.join(id.to_string()), id, &returns).unwrap();
    let rounds = Program::load(&pdf(42)).unwrap().rounds;
    let mk = |id: u32| Session::new(terms(id, t_close), &pdf(id));
    let (mut r, mut x, mut s, mut df, mut p, mut mm, mut e) = (mk(42), mk(43), mk(44), mk(45), mk(46), mk(47), mk(48));
    let mut q = mk(49);
    let m = r.m();
    println!("SESS the statement: {rounds} rounds, {m} depths; V_max {} in {} bits of {}; reserves {} (Alice) and {} (the hub)", r.terms.v_max(), r.terms.bits, r.terms.unit, r.terms.reserve_alice, r.terms.reserve_hub);
    assert!(!l2.is_final_return(6, 43));
    r.play(9);
    x.play(6);
    s.play(12);
    p.play(6);
    mm.play(5);
    e.play(3);
    q.play(7);
    for sess in [&mut r, &mut x, &mut df, &mut p, &mut mm, &mut e, &mut q] {
        sess.fund_session(&rt);
    }
    let cs = s.fund_session(&rt);
    let (delta, w) = (r.params().delta, r.params().delta + r.params().delta_prime);

    // ===== H8: nothing either side can spend alone before a withdrawal =====
    {
        let names: Vec<&str> = cs.leaves().iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names, vec!["fold", "default", "escalate"], "H8");
        println!("SESS H8: the contract output carries only {names:?} (fold: both sign): no claim exists before a withdrawal starts");
    }

    // ===== R: the hub refuses a valid claim; the whole search on chain =====
    {
        let (_, _, vb) = r.play_on_chain(&rt);
        let (proof, name) = r.prove_last();
        assert!(rt.test_accept(&proof).is_err(), "R: the proof waits out the hub's window");
        rt.mine(u64::from(w)).unwrap();
        confirm(&rt, &proof).unwrap_or_else(|e| panic!("R: the pre-signed proof: {e}"));
        println!("SESS R: {name} (pre-signed) pays b = 9 in {} bit outputs and both reserves: {} vB; the dispute: {} vB", r.terms.bits, proof.vsize(), vb + proof.vsize() as u64);
        for i in 0..r.terms.bits {
            r.spend_bit(&rt, &proof, i, 9);
        }
        r.spend_reserve(&rt, &proof);
        println!("SESS R: Alice took bits 0 and 3 (9 x {}) and the reserves, the hub bits 1 and 2", r.terms.unit);
    }

    // ===== X: a false claim; halt_exit =====
    {
        let (op, out, vb) = x.play_on_chain(&rt);
        let tx = x.halt_exit(op, &out);
        rt.mine(u64::from(delta)).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("X: halt_exit must fire: {e:#}"));
        assert_eq!(tx.output.len(), 1, "X: everything to the hub");
        println!("SESS X: the execution halted with exit 1; disprove_zk_halt_exit: {} vB; the hub takes everything, both reserves included; the dispute: {} vB", tx.vsize(), vb + tx.vsize() as u64);
    }

    // ===== S, A6: the hub has disappeared =====
    {
        let (_, _, tx) = s.escalate(&rt, Role::User);
        println!("SESS S: Alice escalates: {} vB", tx.vsize());
        let split = s.terminal("timeout_1", vec![], Role::User);
        assert!(rt.test_accept(&split).is_err(), "S: not before the hub's window ends");
        rt.mine(u64::from(w)).unwrap();
        confirm(&rt, &split).unwrap_or_else(|e| panic!("S: the timeout: {e}"));
        println!("SESS S: the hub never answered; the timeout pays b = 12 and both reserves: {} vB", split.vsize());
        // A6: had Alice also signed b = 13, the hub takes a bit of hers (bit 2
        // is set in 12) and the reserve output before her delay runs out
        let (eq_bit, eq_res) = (s.equiv(&split, 2, 12, 13), s.equiv(&split, s.terms.bits, 12, 13));
        rt.mine_with(&[eq_bit.clone(), eq_res.clone()]).unwrap_or_else(|e| panic!("A6: equiv_b: {e:#}"));
        println!("SESS A6: two signatures on b: the hub takes bit 2 ({} vB) and the reserves ({} vB) with equiv_b", eq_bit.vsize(), eq_res.vsize());
        for i in [0, 1, 3] {
            s.spend_bit(&rt, &split, i, 12);
        }
    }

    // ===== P: Alice probes; the hub answers; she abandons =====
    {
        p.escalate(&rt, Role::User);
        p.post(&rt, 2, Role::Hub);
        let split = p.terminal("timeout_2", vec![], Role::Hub);
        assert!(rt.test_accept(&split).is_err(), "P: not before Alice's window ends");
        rt.mine(u64::from(w)).unwrap();
        confirm(&rt, &split).unwrap_or_else(|e| panic!("P: the hub's timeout: {e}"));
        println!("SESS P: a false claim of b = 6, abandoned after the hub's answer; the hub's timeout takes everything, her reserve included: {} vB", split.vsize());
    }

    // ===== M: Alice's words sign another session's memo =====
    {
        mm.words[1] = 99;
        let (op, out, _) = mm.escalate(&rt, Role::User);
        let tx = mm.check(op, &out, "memo", 1);
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("M: the memo check: {e:#}"));
        println!("SESS M: Alice's claim signs memo 99 for session 47; the hub's memo check takes everything: {} vB", tx.vsize());
        // the right memo gives the hub nothing
        mm.words[1] = 47;
        let honest = mm.check(op, &out, "memo", 1);
        assert!(rt.test_accept(&honest).is_err());
    }

    // ===== E1: off-chain play, then Alice disappears; the hub replays =====
    {
        // four moves were played off-chain; Alice never sends move 5; the
        // hub escalates and replays moves 1 to 4 from the signatures it holds
        e.escalate(&rt, Role::Hub);
        for j in 2..=4 {
            e.post(&rt, j, Role::Hub);
        }
        let split = e.terminal("timeout_4", vec![], Role::Hub);
        rt.mine(u64::from(w)).unwrap();
        confirm(&rt, &split).unwrap_or_else(|e| panic!("E1: the hub's timeout: {e}"));
        println!("SESS E1: Alice stopped after 4 moves; the hub escalated, replayed them, and its timeout takes everything (her claim was valid; her absence loses it): {} vB", split.vsize());
    }

    // ===== Q: a cheating replay; equiv_d =====
    {
        // moves 1 to 3 were played off-chain; Alice holds the hub's
        // signature on its true move 2. The hub escalates and replays, but
        // posts move 2 altered, then Alice's move 3 as she signed it.
        let honest_2 = q.move_sig(2);
        q.escalate(&rt, Role::Hub);
        let true_2 = q.heads[1];
        q.heads[1][4 + 3] ^= 1; // the state digest's fourth byte
        let altered_2 = q.move_sig(2);
        q.post(&rt, 2, Role::Hub);
        let (op, out, _) = q.post(&rt, 3, Role::Hub);
        // move 3 no longer copies move 2's state: the hub could disprove it
        // after delta (the file: the altered move 2, Alice's move 3)
        let l3 = q.ladder(3);
        let copied = q.hub_takes(&l3, op, &out, "disprove_zk_copied", q.file_wire(3));
        q.heads[1] = true_2;
        // but Alice shows the hub's two signatures at depth 2 first
        let eq = q.alice_takes(&l3, op, &out, "equiv_d_2", [wots_wire(&honest_2), wots_wire(&altered_2)].concat());
        rt.mine(u64::from(delta)).unwrap();
        rt.test_accept(&copied).unwrap_or_else(|e| panic!("Q: the hub's disprove of move 3 would be valid: {e:#}"));
        rt.mine_with(std::slice::from_ref(&eq)).unwrap_or_else(|e| panic!("Q: equiv_d_2: {e:#}"));
        println!("SESS Q: the hub replayed an altered move 2 (its disprove of Alice's move 3 would be valid, {} vB); Alice's equiv_d_2 takes everything first: {} vB", copied.vsize(), eq.vsize());
    }

    // ===== D: no withdrawal by T_close; the pre-signed default =====
    {
        let bare = df.finish("default", vec![]);
        let prevout = df.set["default"].prevout.clone();
        let tx = df.wallets[1].pay(bare.clone(), &prevout);
        assert!(rt.test_accept(&tx).is_err(), "D: not before T_close");
        rt.mine_to_height(t_close).unwrap();
        let why = rt.test_accept(&bare).expect_err("D: a pre-signed transaction carries no fee of its own");
        println!("SESS fees: a pre-signed transaction alone is refused ({why}); its broadcaster adds a fee input");
        confirm(&rt, &tx).unwrap_or_else(|e| panic!("D: the default: {e}"));
        assert_eq!(tx.output[0].value, df.terms.reserve_alice);
        println!("SESS D: the default after T_close returns Alice's reserve and pays the hub: {} vB", tx.vsize());
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// The verifier ELF as shipped (GPL, not vendored): BitVMX-CPU's built
/// copy, from the Cargo checkout.
fn groth16_verifier_elf() -> std::path::PathBuf {
    let home = std::env::var("CARGO_HOME").map(std::path::PathBuf::from).unwrap_or_else(|_| std::path::PathBuf::from(std::env::var("HOME").unwrap()).join(".cargo"));
    let checkouts = home.join("git/checkouts");
    for d in std::fs::read_dir(&checkouts).unwrap().flatten() {
        if !d.file_name().to_string_lossy().starts_with("bitvmx-cpu-") {
            continue;
        }
        for rev in std::fs::read_dir(d.path()).unwrap().flatten() {
            let elf = rev.path().join("docker-riscv32/verifier/build/zkverifier-new-mul.elf");
            if rev.file_name().to_string_lossy().starts_with("299009c") && elf.exists() {
                return elf;
            }
        }
    }
    panic!("BitVMX-CPU 299009c not found under {}", checkouts.display());
}

/// The pinned guest's image id (r0/guests/README.md), as the input's
/// words 1 to 8.
const IMAGE_ID: &str = "4beda75466ff0db4aa6c6fe9512140368ad287c695f0ff162775db93039aa639";

/// Opt-in: sessions on the REAL statement program, BitVMX's Groth16
/// verifier (59 depths), with a real proof of the withdrawal guest
/// (tests/data). Two BitVMX searches (about 9 minutes each in release),
/// then two whole disputes on chain.
///
/// - R: Alice's valid claim (b = 9, memo 42), the hub refuses: she
///   escalates with her signed input words; all 59 moves on the ladder;
///   her pre-signed proof pays b = 9 in bits, read from the input's word
///   41, and both reserves;
/// - X: the same proof with b changed to 10: the whole search on chain,
///   the verifier halts with failure, and the hub's `halt_exit` wins;
/// - I: Alice's words sign a different image id (another program's
///   proof): the hub's `image_1` check on the first ladder output takes
///   everything;
/// - M: Alice's words sign memo 43 for this session (42): the `memo` check.
#[test]
#[ignore]
fn sessions_on_the_groth16_verifier() {
    let rt = Regtest::start().unwrap();
    let dir = std::env::temp_dir().join(format!("lngap-sess-real-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::copy(groth16_verifier_elf(), dir.join("zkverifier.elf")).unwrap();
    std::fs::write(dir.join("groth16.yaml"), "elf: zkverifier.elf\nnary_search: 2\nmax_steps: 536870912\ninput_section_name: .input\ninputs:\n  - size: 172\n    owner: prover\n").unwrap();
    let pdf = dir.join("groth16.yaml").display().to_string();
    let valid = hex::decode(include_str!("data/withdraw-9-42.hex").trim()).unwrap();
    let words = input_words(&valid);
    assert_eq!(words.len(), 43, "length, image id, proof, b, c");
    let (b_word, c_word) = (41, 42);
    assert_eq!((words[0], words[b_word], words[c_word]), (2, 9, 42));
    let id_words = input_words(&hex::decode(IMAGE_ID).unwrap());
    assert_eq!(&words[1..9], id_words.as_slice(), "the proof is of the pinned guest");
    let mut tampered = valid.clone();
    tampered[164] = 10; // b, word 41's low byte
    let rounds = Program::load(&pdf).unwrap().rounds;

    let t_close = rt.height().unwrap() + 2_000;
    let check = |name: &str, word: usize, value: u32| Check { name: name.into(), word, value };
    let checks: Vec<Check> = [check("journal_len", 0, 2), check("memo", c_word, 42)].into_iter().chain((1..9).map(|j| check(&format!("image_{j}"), j, id_words[j - 1]))).collect();
    let t = Instant::now();
    let mk = |cid| Session::with(terms(42, t_close), cid, &pdf, b_word, checks.clone());
    let (mut r, mut x, mut i, mut mm) = (mk(61), mk(62), mk(63), mk(64));
    let m = r.m();
    println!("SESS [real] the Groth16 verifier: {rounds} rounds, {m} depths; four sessions' keys and families in {:.1?}", t.elapsed());
    let t = Instant::now();
    r.play_input(&valid, "b = 9 (a valid proof)");
    x.play_input(&tampered, "b = 10 (the proof is for 9)");
    println!("SESS [real] both searches in {:.0?}", t.elapsed());
    // I and M claim on the valid proof's search, with one word changed
    for s in [&mut i, &mut mm] {
        (s.heads, s.entries, s.words) = (r.heads.clone(), r.entries.clone(), r.words.clone());
    }
    let t = Instant::now();
    for sess in [&mut r, &mut x, &mut i, &mut mm] {
        sess.fund_session(&rt);
    }
    println!("SESS [real] four contracts funded, their pre-signed sets built ({} transactions each) in {:.1?}", r.set.len(), t.elapsed());
    let (delta, w) = (r.params().delta, r.params().delta + r.params().delta_prime);

    // ===== I: a different image id; M: another contract's memo =====
    for (s, name, j, bad) in [(&mut i, "image_1", 1usize, id_words[0] ^ 1), (&mut mm, "memo", c_word, 43)] {
        s.words[j] = bad;
        let (op, out, esc) = s.escalate(&rt, Role::User);
        let tx = s.check(op, &out, name, j);
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("{name}: {e:#}"));
        println!("SESS [real] {}: escalate {} vB; Alice's words sign {name} = {bad:#x}; the hub's check takes everything: {} vB", if name == "memo" { "M" } else { "I" }, esc.vsize(), tx.vsize());
    }

    // ===== R: the hub refused a valid claim; the whole search on chain =====
    {
        let t = Instant::now();
        let (_, _, vb) = r.play_on_chain(&rt);
        let (proof, name) = r.prove_last();
        rt.mine(u64::from(w)).unwrap();
        confirm(&rt, &proof).unwrap_or_else(|e| panic!("R: the proof: {e}"));
        println!("SESS [real] R: {name} pays b = 9 (input word 41) in bits and both reserves: {} vB; the whole dispute: {} vB in {} transactions ({:.0?})", proof.vsize(), vb + proof.vsize() as u64, m + 1, t.elapsed());
        for k in 0..r.terms.bits {
            r.spend_bit(&rt, &proof, k, 9);
        }
        r.spend_reserve(&rt, &proof);
    }

    // ===== X: the proof is for 9, Alice claims 10: halt_exit =====
    {
        let (op, out, vb) = x.play_on_chain(&rt);
        let tx = x.halt_exit(op, &out);
        rt.mine(u64::from(delta)).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("X: halt_exit must fire: {e:#}"));
        println!("SESS [real] X: the verifier halted with failure; disprove_zk_halt_exit: {} vB. The hub wins; the whole dispute: {} vB", tx.vsize(), vb + tx.vsize() as u64);
    }
    let _ = std::fs::remove_dir_all(&dir);
}
