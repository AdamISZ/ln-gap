//! LN-GAP v3 on regtest (research/lngap_v3.pdf): sessions over a toy L2,
//! no venue. The session contract carries `default` and `escalate`; a
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
//! - D, the default: no withdrawal by T_close; the pre-signed default
//!   returns Alice's reserve and pays the hub.
//!
//! The opt-in test runs R, X and the input checks on the real statement
//! program, BitVMX's Groth16 verifier (59 depths), and measures a whole
//! dispute on chain.
//!
//! Run with `--test-threads=1` or 2.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Instant;

use bitcoin::hashes::Hash;
use bitcoin::key::Keypair;
use bitcoin::secp256k1::SECP256K1;
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use emulator::decision::challenge::ForceCondition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::TapTree;
use lngap_btc::tx::build_spend;
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, Role};
use lngap_contract::{Contract, Outcome};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsPublic, WotsSecret, WotsSig};
use lngap_pos::blackjack::auth_message;
use lngap_pos::instance::{self, mover_at, PosDepthKeys};
use lngap_pos::rebut::{wots_wire, wots_wire_tied};
use lngap_pos::ttt::Layout;
use lngap_sessions::l2::{Op, HUB, L2};
use lngap_sessions::session::{bit_tree, default_leaf, default_outputs, input_word_leaf, payout, reserve_tree, Terms};
use lngap_sessions::statement::{input, write_program};
use lngap_tictactoe::TicTacToe;
use lngap_v25::{escalate_leaf_with, ladder_leaves, ZkDated};
use lngap_zk::challenges::ProgramInfo;
use lngap_zk::dispute::{search, Behaviour};
use lngap_zk::family::ZkFamily;
use lngap_zk::final_d60::{input_key_params, input_message, input_words};
use lngap_zk::game::{final_witness, play, Entry, Search};
use lngap_zk::nibble_witness;

const GAME_ID: u16 = 1;
const SEQ: u64 = 1;

fn sig(kp: &Keypair, tx: &Transaction, input: usize, prevouts: &[TxOut], leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, input, prevouts, leaf).unwrap().as_ref().to_vec()
}

// -------------------------------------------------------------- session

/// One session contract between Alice (the user, the prover) and the hub.
struct Session {
    terms: Terms,
    /// The contract's number (labels, keys); the memo `c` is `terms.id`.
    cid: u32,
    /// The input word that carries `b`, and the input-word checks on the
    /// first ladder output: (leaf name, word, the value it must have).
    b_word: usize,
    checks: Vec<(String, usize, u32)>,
    user: PartyKeys,
    hub: PartyKeys,
    ks: [KeyStore; 2],
    params: ChannelParams,
    pubs: [PartyPubKeys; 2],
    keys: Vec<PosDepthKeys>,
    family: Arc<ZkFamily>,
    /// Alice's input-word keys, one per word of the statement's input.
    input_secrets: Vec<WotsSecret>,
    outcomes: Vec<Outcome>,
    pdf: String,
    /// The claim: the input's words (what Alice signs), the search's heads
    /// and entries.
    words: Vec<u32>,
    heads: Vec<[u8; 48]>,
    entries: Vec<Entry>,
    ladders: HashMap<u32, TapTree>,
}

/// The session contract's output: its tree, outpoint, output.
struct Funded {
    tree: TapTree,
    op: OutPoint,
    out: TxOut,
}

impl Session {
    fn new(terms: Terms, pdf: &str, rounds: u32) -> Session {
        let checks = vec![("memo".to_string(), 1, terms.id)];
        Session::with(terms, terms.id, pdf, rounds, 0, checks)
    }
    /// A session on any statement program: contract number `cid`, `b` in
    /// input word `b_word`, the input-word `checks`.
    fn with(terms: Terms, cid: u32, pdf: &str, rounds: u32, b_word: usize, checks: Vec<(String, usize, u32)>) -> Session {
        let id = cid;
        let user = PartyKeys::from_seed(Role::User, Seed::from_label(&format!("sess/{id}/alice")));
        let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label(&format!("sess/{id}/hub")));
        let mut ks = [KeyStore::new(Seed::from_label(&format!("sess/{id}/alice-ks"))), KeyStore::new(Seed::from_label(&format!("sess/{id}/hub-ks")))];
        let search = Search { game_id: GAME_ID, rounds };
        let m = search.depths();
        let ou = instance::gen_pos_keys(&mut ks[0], Role::User, id, SEQ, m, instance::Game::Zk).unwrap();
        let oh = instance::gen_pos_keys(&mut ks[1], Role::Hub, id, SEQ, m, instance::Game::Zk).unwrap();
        let keys = instance::collect_keys(&ou, &oh, m).unwrap();
        let info = ProgramInfo::load(pdf).unwrap();
        let input_secrets: Vec<WotsSecret> = (0..info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x60u8.wrapping_add(j as u8).wrapping_add(id as u8); 32])).collect();
        let family = ZkFamily::new(search, info, input_secrets.iter().map(|k| k.public()).collect());
        let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::from_sat(20_000_000)) };
        let pubs = [user.public(), hub.public()];
        Session {
            terms,
            cid,
            b_word,
            checks,
            user,
            hub,
            ks,
            params,
            pubs,
            keys,
            family,
            input_secrets,
            outcomes: Contract::outcomes(&TicTacToe),
            pdf: pdf.to_string(),
            words: vec![],
            heads: vec![],
            entries: vec![],
            ladders: HashMap::new(),
        }
    }
    fn m(&self) -> u32 {
        self.keys.len() as u32
    }
    fn g(&self) -> ZkDated<'_> {
        ZkDated { family: self.family.as_ref(), prove_presigned: true }
    }
    fn ctx(&self) -> CommitCtx<'_> {
        CommitCtx { params: &self.params, keys: &self.pubs, broadcaster: Role::Hub, seq: SEQ, rev_hash: [0u8; 20] }
    }
    fn b_key(&self) -> WotsPublic {
        self.input_secrets[self.b_word].public()
    }
    /// Alice's signature on her claimed `b` (input word `b_word`).
    fn b_sig(&self, b: u32) -> WotsSig {
        self.input_secrets[self.b_word].sign(&input_message(b)).unwrap()
    }
    /// The input words `escalate` puts on chain: `b`'s and the checked
    /// ones.
    fn claim_words(&self) -> Vec<usize> {
        let mut w: Vec<usize> = self.checks.iter().map(|c| c.1).chain([self.b_word]).collect();
        w.sort_unstable();
        w.dedup();
        w
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
    /// The session contract: `default` (pre-signed, after `T_close`) and
    /// `escalate` (move 1 with Alice's signed claim words, into the
    /// ladder). Nothing else: a force-close gives neither side anything to
    /// spend before a withdrawal starts.
    fn fund_session(&mut self, rt: &Regtest) -> Funded {
        let ctx = self.ctx();
        let l1 = Layout::at(1, GAME_ID, mover_at(1));
        let words: Vec<WotsPublic> = self.claim_words().iter().map(|&j| self.input_secrets[j].public()).collect();
        let leaves = vec![default_leaf(&ctx, self.terms.t_close), escalate_leaf_with(&self.g(), &ctx, &l1, &self.keys[0], &words)];
        let tree = TapTree::new(leaves).unwrap();
        let (op, out) = rt.fund(&tree.script_pubkey(), self.value()).unwrap();
        Funded { tree, op, out }
    }
    /// `V_max`, both reserves, and the pre-signed fees of a whole search.
    fn value(&self) -> Amount {
        self.terms.v_max() + self.terms.reserves() + self.params.presign_fee * u64::from(self.m() + 3)
    }
    /// The ladder output after move `j`; the first one also carries the
    /// hub's input-word checks.
    fn ladder(&mut self, j: u32) -> TapTree {
        if let Some(t) = self.ladders.get(&j) {
            return t.clone();
        }
        let ctx = self.ctx();
        let mut leaves = ladder_leaves(&self.g(), &ctx, GAME_ID, j, &self.keys, &self.outcomes);
        if j == 1 {
            leaves.extend(self.checks.iter().map(|(name, w, v)| input_word_leaf(&ctx, name, &self.input_secrets[*w].public(), *v)));
        }
        let t = TapTree::new(leaves).unwrap();
        self.ladders.insert(j, t.clone());
        t
    }
    /// The pair reveal at `d` and both heads' authorship, wire order.
    fn post_wire(&mut self, d: u32) -> (Vec<Vec<u8>>, WotsSig) {
        let id = self.cid;
        let (new, mv) = (self.heads[(d - 1) as usize], mover_at(d));
        let new_auth = self.ks[mv.idx()].sign_wots(&instance::state_label(id, SEQ, d), &auth_message(&new)).unwrap();
        let mut w = vec![];
        let pair = if d == 1 {
            self.ks[mv.idx()].sign_wots(&instance::rebut_label(id, SEQ, d), &new).unwrap()
        } else {
            let prev = self.heads[(d - 2) as usize];
            let prior_auth = self.ks[mover_at(d - 1).idx()].sign_wots(&instance::state_label(id, SEQ, d - 1), &auth_message(&prev)).unwrap();
            w.extend(wots_wire_tied(&prior_auth));
            self.ks[mv.idx()].sign_wots(&instance::rebut_label(id, SEQ, d), &[prev.as_slice(), new.as_slice()].concat()).unwrap()
        };
        w.extend(wots_wire_tied(&new_auth));
        w.extend(wots_wire(&pair));
        (w, pair)
    }
    /// Alice's signature on input word `j` (her claim's value).
    fn word_sig(&self, j: usize) -> WotsSig {
        self.input_secrets[j].sign(&input_message(self.words[j])).unwrap()
    }
    /// Post move `j`: for move 1, `escalate` from the session contract
    /// `c`, with the claim words; otherwise `post` from the ladder output
    /// at `j - 1`. An escalation after off-chain play replays the moves
    /// made, each posted with the signatures the poster holds.
    fn post(&mut self, rt: &Regtest, j: u32, op: OutPoint, out: &TxOut, c: Option<&Funded>) -> (OutPoint, TxOut, Transaction) {
        let (tree, name) = match c {
            Some(c) => (c.tree.clone(), "escalate"),
            None => (self.ladder(j - 1), "post"),
        };
        let leaf = tree.leaf(name).unwrap();
        let t_out = TxOut { value: out.value - self.params.presign_fee, script_pubkey: self.ladder(j).script_pubkey() };
        let mut tx = build_spend(op, &leaf.timelock, vec![t_out.clone()]);
        let mut w = vec![];
        if c.is_some() {
            for &k in self.claim_words().iter().rev() {
                w.extend(wots_wire(&self.word_sig(k)));
            }
        }
        w.extend(self.post_wire(j).0);
        w.push(sig(&self.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        w.push(sig(&self.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("{}: posting move {j}: {e:#}", self.cid));
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, t_out, tx)
    }
    /// Escalate, after the contract's `to_self_delay`.
    fn escalate(&mut self, rt: &Regtest, c: &Funded) -> (OutPoint, TxOut, Transaction) {
        rt.mine(u64::from(self.params.to_self_delay)).unwrap();
        self.post(rt, 1, c.op, &c.out, Some(c))
    }
    /// A 2-of-2 spend of `(op, out)` under `tree`'s leaf `name`, `wire`
    /// below the signatures, paying `b` in bits and both reserves to Alice.
    fn pay_b(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let outs = payout(&self.ctx(), &self.terms, &self.b_key(), out.value, self.params.presign_fee).unwrap();
        self.presigned(tree, op, out, name, wire, outs)
    }
    /// A 2-of-2 spend paying everything to the hub (Alice lost).
    fn pay_hub(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str) -> Transaction {
        let outs = vec![TxOut { value: out.value - self.params.presign_fee, script_pubkey: self.pubs[1].payout_spk.clone() }];
        self.presigned(tree, op, out, name, vec![], outs)
    }
    fn presigned(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>, outs: Vec<TxOut>) -> Transaction {
        let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
        let mut tx = build_spend(op, &leaf.timelock, outs);
        let mut w = wire;
        w.push(sig(&self.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        w.push(sig(&self.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
        tx
    }
    /// A runtime spend by the hub of `(op, out)` under `tree`'s leaf
    /// `name`, `wire` below its signature: everything to the hub.
    fn hub_takes(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
        let mut tx = build_spend(op, &leaf.timelock, vec![TxOut { value: out.value - self.params.presign_fee, script_pubkey: self.pubs[1].payout_spk.clone() }]);
        let mut w = wire;
        w.push(sig(&self.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
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
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs[who.idx()].payout_spk.clone() }]);
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
            rt.mine(u64::from(self.params.delta)).unwrap();
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
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs[0].payout_spk.clone() }]);
        let w = vec![sig(&self.user.payment, &s, 0, std::slice::from_ref(&prev), &leaf.script)];
        s.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block("alice_reserve").unwrap());
        let confs = rt.confirmations(&tx.compute_txid()).ok().flatten().unwrap_or(0);
        if confs < self.params.delta.into() {
            assert!(rt.test_accept(&s).is_err(), "the reserve waits delta");
            rt.mine(u64::from(self.params.delta)).unwrap();
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
        let mut s = build_spend(op, &leaf.timelock, vec![TxOut { value: prev.value - Amount::from_sat(1_000), script_pubkey: self.pubs[1].payout_spk.clone() }]);
        let mut w = [wots_wire(&self.b_sig(b1)), wots_wire(&self.b_sig(b2))].concat();
        w.push(sig(&self.hub.payment, &s, 0, std::slice::from_ref(&prev), &leaf.script));
        s.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(&name).unwrap());
        s
    }
    /// The whole search on chain, from the escalation to the final step
    /// (Alice's record at depth `m`): the ladder output there and the
    /// dispute's total size so far.
    fn play_on_chain(&mut self, rt: &Regtest, c: &Funded) -> (OutPoint, TxOut, u64) {
        let (mut op, mut out, tx) = self.escalate(rt, c);
        let mut vb = tx.vsize() as u64;
        println!("SESS {}: escalate (move 1 and {} signed input words): {} vB", self.cid, self.claim_words().len(), tx.vsize());
        let (mut alice, mut hub) = (0u64, 0u64);
        for j in 2..=self.m() {
            let (o, t, tx) = self.post(rt, j, op, &out, None);
            if mover_at(j) == Role::User {
                alice += tx.vsize() as u64;
            } else {
                hub += tx.vsize() as u64;
            }
            (op, out) = (o, t);
        }
        vb += alice + hub;
        println!("SESS {}: moves 2 to {} posted: Alice's {alice} vB, the hub's {hub} vB", self.cid, self.m());
        (op, out, vb)
    }
    /// The final step at the last ladder output: Alice's pre-signed proof.
    fn prove_last(&mut self, op: OutPoint, out: &TxOut) -> (Transaction, String) {
        let m = self.m();
        let tree = self.ladder(m);
        let pair = self.post_wire(m).1;
        let last = self.entries.last().unwrap().clone();
        let rec = last.record.unwrap();
        let class = lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap();
        let name = format!("zk_prove_{class}");
        (self.pay_b(&tree, op, out, &name, [final_witness(&last.state, &rec), wots_wire(&pair)].concat()), name)
    }
    /// The hub's `halt_exit` disprove at the last ladder output.
    fn halt_exit(&mut self, op: OutPoint, out: &TxOut) -> Transaction {
        let m = self.m();
        let tree = self.ladder(m);
        let pair = self.post_wire(m).1;
        let last = self.entries.last().unwrap().clone();
        let (rec, cl) = (last.record.unwrap(), self.entries[0].claim.unwrap());
        self.hub_takes(&tree, op, out, "disprove_zk_halt_exit", [nibble_witness(&rec.to_bytes()), nibble_witness(&cl.to_bytes()), wots_wire(&pair)].concat())
    }
    /// The hub's input-word check `name` on the first ladder output: with
    /// Alice's signature on word `j` as posted.
    fn check(&mut self, op: OutPoint, out: &TxOut, name: &str, j: usize) -> Transaction {
        let tree = self.ladder(1);
        self.hub_takes(&tree, op, out, name, wots_wire(&self.word_sig(j)))
    }
}

fn terms(id: u32, t_close: u32) -> Terms {
    Terms { id, unit: Amount::from_sat(100_000), bits: 4, deposit: 10, t_close, reserve_alice: Amount::from_sat(200_000), reserve_hub: Amount::from_sat(300_000) }
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
    let rounds = emulator::loader::program_definition::ProgramDefinition::from_config(&pdf(42)).unwrap().nary_def().total_rounds() as u32;
    let mk = |id: u32| Session::new(terms(id, t_close), &pdf(id), rounds);
    let (mut r, mut x, mut s, mut df, mut p, mut mm, mut e) = (mk(42), mk(43), mk(44), mk(45), mk(46), mk(47), mk(48));
    let m = r.m();
    println!("SESS the statement: {rounds} rounds, {m} depths; V_max {} in {} bits of {}; reserves {} (Alice) and {} (the hub)", r.terms.v_max(), r.terms.bits, r.terms.unit, r.terms.reserve_alice, r.terms.reserve_hub);
    assert!(!l2.is_final_return(6, 43));
    r.play(9);
    x.play(6);
    s.play(12);
    p.play(6);
    mm.play(5);
    e.play(3);
    let (cr, cx, cs, cd, cp, cm, ce) = (r.fund_session(&rt), x.fund_session(&rt), s.fund_session(&rt), df.fund_session(&rt), p.fund_session(&rt), mm.fund_session(&rt), e.fund_session(&rt));
    let (delta, w) = (r.params.delta, r.params.delta + r.params.delta_prime);

    // ===== H8: the session output carries only default and escalate =====
    {
        let names: Vec<&str> = cs.tree.leaves().iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names, vec!["default", "escalate"], "H8");
        println!("SESS H8: the session output carries only {names:?}: no claim exists before a withdrawal starts");
    }

    // ===== R: the hub refuses a valid claim; the whole search on chain =====
    {
        let (op, out, vb) = r.play_on_chain(&rt, &cr);
        let (proof, name) = r.prove_last(op, &out);
        assert!(rt.test_accept(&proof).is_err(), "R: the proof waits out the hub's window");
        rt.mine(u64::from(w)).unwrap();
        rt.mine_with(std::slice::from_ref(&proof)).unwrap_or_else(|e| panic!("R: the pre-signed proof: {e:#}"));
        println!("SESS R: {name} (pre-signed) pays b = 9 in {} bit outputs and both reserves: {} vB; the dispute: {} vB", r.terms.bits, proof.vsize(), vb + proof.vsize() as u64);
        for i in 0..r.terms.bits {
            r.spend_bit(&rt, &proof, i, 9);
        }
        r.spend_reserve(&rt, &proof);
        println!("SESS R: Alice took bits 0 and 3 (9 x {}) and the reserves, the hub bits 1 and 2", r.terms.unit);
    }

    // ===== X: a false claim; halt_exit =====
    {
        let (op, out, vb) = x.play_on_chain(&rt, &cx);
        let tx = x.halt_exit(op, &out);
        rt.mine(u64::from(delta)).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("X: halt_exit must fire: {e:#}"));
        assert_eq!(tx.output.len(), 1, "X: everything to the hub");
        println!("SESS X: the execution halted with exit 1; disprove_zk_halt_exit: {} vB; the hub takes everything, both reserves included; the dispute: {} vB", tx.vsize(), vb + tx.vsize() as u64);
    }

    // ===== S, A6: the hub has disappeared =====
    {
        let (op, out, tx) = s.escalate(&rt, &cs);
        println!("SESS S: Alice escalates: {} vB", tx.vsize());
        let l1 = s.ladder(1);
        let split = s.pay_b(&l1, op, &out, "split_UserWins", vec![]);
        assert!(rt.test_accept(&split).is_err(), "S: not before the hub's window ends");
        rt.mine(u64::from(w)).unwrap();
        rt.mine_with(std::slice::from_ref(&split)).unwrap_or_else(|e| panic!("S: the timeout: {e:#}"));
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
        let (op, out, _) = p.escalate(&rt, &cp);
        let (op, out, _) = p.post(&rt, 2, op, &out, None);
        let l2t = p.ladder(2);
        let split = p.pay_hub(&l2t, op, &out, "split_HubWins");
        assert!(rt.test_accept(&split).is_err(), "P: not before Alice's window ends");
        rt.mine(u64::from(w)).unwrap();
        rt.mine_with(std::slice::from_ref(&split)).unwrap_or_else(|e| panic!("P: the hub's timeout: {e:#}"));
        println!("SESS P: a false claim of b = 6, abandoned after the hub's answer; the hub's timeout takes everything, her reserve included: {} vB", split.vsize());
    }

    // ===== M: Alice's words sign another session's memo =====
    {
        mm.words[1] = 99;
        let (op, out, _) = mm.escalate(&rt, &cm);
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
        let (mut op, mut out, _) = e.escalate(&rt, &ce);
        for j in 2..=4 {
            (op, out, _) = e.post(&rt, j, op, &out, None);
        }
        let l4 = e.ladder(4);
        let split = e.pay_hub(&l4, op, &out, "split_HubWins");
        rt.mine(u64::from(w)).unwrap();
        rt.mine_with(std::slice::from_ref(&split)).unwrap_or_else(|e| panic!("E1: the hub's timeout: {e:#}"));
        println!("SESS E1: Alice stopped after 4 moves; the hub escalated, replayed them, and its timeout takes everything (her claim was valid; her absence loses it): {} vB", split.vsize());
    }

    // ===== D: no withdrawal by T_close; the pre-signed default =====
    {
        let outs = default_outputs(&df.ctx(), &df.terms, cd.out.value, Amount::from_sat(2_000)).unwrap();
        let tx = df.presigned(&cd.tree, cd.op, &cd.out, "default", vec![], outs);
        assert!(rt.test_accept(&tx).is_err(), "D: not before T_close");
        rt.mine_to_height(t_close).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("D: the default: {e:#}"));
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
    let rounds = emulator::loader::program_definition::ProgramDefinition::from_config(&pdf).unwrap().nary_def().total_rounds() as u32;

    let t_close = rt.height().unwrap() + 2_000;
    let checks: Vec<(String, usize, u32)> = [("journal_len".to_string(), 0, 2), ("memo".to_string(), c_word, 42)]
        .into_iter()
        .chain((1..9).map(|j| (format!("image_{j}"), j, id_words[j - 1])))
        .collect();
    let t = Instant::now();
    let mk = |cid| Session::with(terms(42, t_close), cid, &pdf, rounds, b_word, checks.clone());
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
    let (cr, cx, ci, cm) = (r.fund_session(&rt), x.fund_session(&rt), i.fund_session(&rt), mm.fund_session(&rt));
    println!("SESS [real] four session contracts in {:.1?}", t.elapsed());
    let (delta, w) = (r.params.delta, r.params.delta + r.params.delta_prime);

    // ===== I: a different image id; M: another session's memo =====
    for (s, c, name, j, bad) in [(&mut i, &ci, "image_1", 1usize, id_words[0] ^ 1), (&mut mm, &cm, "memo", c_word, 43)] {
        s.words[j] = bad;
        let (op, out, esc) = s.escalate(&rt, c);
        let tx = s.check(op, &out, name, j);
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("{name}: {e:#}"));
        println!("SESS [real] {}: escalate {} vB; Alice's words sign {name} = {bad:#x}; the hub's check takes everything: {} vB", if name == "memo" { "M" } else { "I" }, esc.vsize(), tx.vsize());
    }

    // ===== R: the hub refused a valid claim; the whole search on chain =====
    {
        let t = Instant::now();
        let (op, out, vb) = r.play_on_chain(&rt, &cr);
        let (proof, name) = r.prove_last(op, &out);
        rt.mine(u64::from(w)).unwrap();
        rt.mine_with(std::slice::from_ref(&proof)).unwrap_or_else(|e| panic!("R: the proof: {e:#}"));
        println!("SESS [real] R: {name} pays b = 9 (input word 41) in bits and both reserves: {} vB; the whole dispute: {} vB in {} transactions ({:.0?})", proof.vsize(), vb + proof.vsize() as u64, m + 1, t.elapsed());
        for k in 0..r.terms.bits {
            r.spend_bit(&rt, &proof, k, 9);
        }
        r.spend_reserve(&rt, &proof);
    }

    // ===== X: the proof is for 9, Alice claims 10: halt_exit =====
    {
        let (op, out, vb) = x.play_on_chain(&rt, &cx);
        let tx = x.halt_exit(op, &out);
        rt.mine(u64::from(delta)).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("X: halt_exit must fire: {e:#}"));
        println!("SESS [real] X: the verifier halted with failure; disprove_zk_halt_exit: {} vB. The hub wins; the whole dispute: {} vB", tx.vsize(), vb + tx.vsize() as u64);
    }
    let _ = std::fs::remove_dir_all(&dir);
}
