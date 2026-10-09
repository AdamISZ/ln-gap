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
use std::sync::Arc;
use std::time::Instant;

use bitcoin::hashes::Hash;
use bitcoin::key::Keypair;
use bitcoin::secp256k1::SECP256K1;
use bitcoin::opcodes::all::OP_CHECKSIG;
use bitcoin::script::Builder;
use bitcoin::{Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut};
use emulator::decision::challenge::ForceCondition;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::{sign_tapscript, sign_tapscript_acp};
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, PartyPubKeys, Role};
use lngap_contract::{Contract, Outcome};
use lngap_lamport::keystore::KeyStore;
use lngap_lamport::winternitz::{WotsParams, WotsPublic, WotsSecret, WotsSig};
use lngap_pos::instance::{self, mover_at, PosDepthKeys};
use lngap_pos::rebut::wots_wire;
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

// ----------------------------------------------------------------- fees

/// The feerate the parties pay, sat/vB.
const FEERATE: u64 = 2;
/// Fee coins: small for moves and timeouts, large for the final proof.
const SMALL: Amount = Amount::from_sat(20_000);
const LARGE: Amount = Amount::from_sat(200_000);

/// A party's fee coins. No pre-signed transaction pays a fee of its own;
/// whoever broadcasts one pays, so each side pays for its own moves:
/// - a link of the ladder's chain (escalate, a move) must keep its txid,
///   since the next link is signed against it: it is a TRUC (v3)
///   transaction with a zero-value pay-to-anchor output, and its poster
///   bumps it with a child spending the anchor and a coin of its own
///   (one-parent-one-child package relay);
/// - a transaction that ends the chain (a timeout, a proof, the default),
///   whose outputs only runtime spends use, is signed ALL|ANYONECANPAY and
///   its broadcaster adds a coin as an input; it may be large (the proof
///   is about 59 kvB, beyond TRUC's 10 kvB). The signatures fix its
///   outputs, so that coin has no change: a party keeps coins of fitting
///   sizes.
struct FeeWallet {
    kp: Keypair,
    tree: TapTree,
    coins: Vec<(OutPoint, TxOut)>,
}

impl FeeWallet {
    /// `small` small coins and `large` large ones, from one funding coin
    /// fanned out (two blocks).
    fn new(rt: &Regtest, kp: &Keypair, small: usize, large: usize) -> FeeWallet {
        let script = Builder::new().push_x_only_key(&kp.x_only_public_key().0).push_opcode(OP_CHECKSIG).into_script();
        let tree = TapTree::new(vec![Leaf::new("fee".to_string(), script, Timelock::NONE)]).unwrap();
        let spk = tree.script_pubkey();
        let total = SMALL * small as u64 + LARGE * large as u64;
        let (op, out) = rt.fund(&spk, total + Amount::from_sat(20_000)).unwrap();
        let outs: Vec<TxOut> = std::iter::repeat_n(SMALL, small).chain(std::iter::repeat_n(LARGE, large)).map(|v| TxOut { value: v, script_pubkey: spk.clone() }).collect();
        let mut tx = build_spend(op, &Timelock::NONE, outs);
        let leaf = tree.leaf("fee").unwrap();
        let w = vec![sig(kp, &tx, 0, std::slice::from_ref(&out), &leaf.script)];
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block("fee").unwrap());
        rt.mine_with(std::slice::from_ref(&tx)).unwrap();
        let txid = tx.compute_txid();
        let coins = tx.output.iter().enumerate().map(|(i, o)| (OutPoint { txid, vout: i as u32 }, o.clone())).collect();
        FeeWallet { kp: *kp, tree, coins }
    }
    /// A TRUC child of `parent` (whose output `anchor` is its pay-to-anchor)
    /// paying `FEERATE` on the pair, its change back to this wallet.
    fn bump(&mut self, parent: &Transaction, anchor: u32) -> Transaction {
        let need = Amount::from_sat((parent.vsize() as u64 + 200) * FEERATE);
        let i = self.coins.iter().enumerate().filter(|(_, c)| c.1.value >= need + Amount::from_sat(1_000)).min_by_key(|(_, c)| c.1.value).map(|(i, _)| i).expect("a fee coin large enough");
        let (op, coin) = self.coins.remove(i);
        let a_op = OutPoint { txid: parent.compute_txid(), vout: anchor };
        let change = TxOut { value: coin.value - need, script_pubkey: coin.script_pubkey.clone() };
        let mut tx = lngap_btc::tx::build_tx(&[(a_op, Sequence::ENABLE_RBF_NO_LOCKTIME), (op, Sequence::ENABLE_RBF_NO_LOCKTIME)], vec![change.clone()], bitcoin::absolute::LockTime::ZERO);
        tx.version = bitcoin::transaction::Version(3);
        let leaf = self.tree.leaf("fee").unwrap();
        let w = vec![sig(&self.kp, &tx, 1, &[parent.output[anchor as usize].clone(), coin], &leaf.script)];
        tx.input[1].witness = tapscript_witness(&w, &leaf.script, &self.tree.control_block("fee").unwrap());
        self.coins.push((OutPoint { txid: tx.compute_txid(), vout: 0 }, change));
        tx
    }
    /// Add a fee input to `tx` (input 0 spends `prevout`): the smallest coin
    /// that pays `FEERATE` on the grown transaction.
    fn pay(&mut self, mut tx: Transaction, prevout: &TxOut) -> Transaction {
        let need = Amount::from_sat((tx.vsize() as u64 + 110) * FEERATE);
        let i = self.coins.iter().enumerate().filter(|(_, c)| c.1.value >= need).min_by_key(|(_, c)| c.1.value).map(|(i, _)| i).expect("a fee coin large enough");
        let (op, coin) = self.coins.remove(i);
        tx.input.push(TxIn { previous_output: op, script_sig: ScriptBuf::new(), sequence: Sequence::ENABLE_RBF_NO_LOCKTIME, witness: Default::default() });
        let leaf = self.tree.leaf("fee").unwrap();
        let w = vec![sig(&self.kp, &tx, 1, &[prevout.clone(), coin], &leaf.script)];
        tx.input[1].witness = tapscript_witness(&w, &leaf.script, &self.tree.control_block("fee").unwrap());
        tx
    }
}

/// Broadcast through the mempool (fee policy applies) and mine it.
fn confirm(rt: &Regtest, tx: &Transaction) -> std::result::Result<(), String> {
    rt.send_raw(tx).map_err(|e| format!("{e:#}"))?;
    rt.mine(1).map_err(|e| format!("{e:#}"))?;
    match rt.confirmations(&tx.compute_txid()) {
        Ok(Some(_)) => Ok(()),
        _ => Err("not mined".into()),
    }
}

/// The 2-of-2 signature of a pre-signed transaction: ALL|ANYONECANPAY.
fn presig(kp: &Keypair, tx: &Transaction, prevout: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript_acp(kp, tx, 0, prevout, leaf).unwrap()
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
    params: ChannelParams,
    pubs: [PartyPubKeys; 2],
    keys: Vec<PosDepthKeys>,
    family: Arc<ZkFamily>,
    /// Alice's input-word keys, one per word of the statement's input.
    input_secrets: Vec<WotsSecret>,
    /// The move keys (lean moves), by depth: depth `d`'s mover signs its
    /// head with `moves[d - 1]`. Held as secrets so that a test can make a
    /// party equivocate.
    moves: Vec<WotsSecret>,
    outcomes: Vec<Outcome>,
    pdf: String,
    /// The claim: the input's words (what Alice signs), the search's heads
    /// and entries.
    words: Vec<u32>,
    heads: Vec<[u8; 48]>,
    entries: Vec<Entry>,
    ladders: HashMap<u32, TapTree>,
    /// Alice's fee coins and the hub's (set when the contract is funded).
    wallets: Vec<FeeWallet>,
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
        // the depth keys' other fields (the venue's); the move keys replace
        // the rebuttal keys below
        let search = Search { game_id: GAME_ID, rounds };
        let m = search.depths();
        let ou = instance::gen_pos_keys(&mut ks[0], Role::User, id, SEQ, m, instance::Game::Zk).unwrap();
        let oh = instance::gen_pos_keys(&mut ks[1], Role::Hub, id, SEQ, m, instance::Game::Zk).unwrap();
        let mut keys = instance::collect_keys(&ou, &oh, m).unwrap();
        // lean moves: each depth's key signs that move's head alone
        let moves: Vec<WotsSecret> = (1..=m).map(|d| WotsSecret::from_entropy(WotsParams::for_bytes(48), Seed::from_label(&format!("sess/{id}/move/{d}")).derive_bytes("wots"))).collect();
        for (k, mv) in keys.iter_mut().zip(&moves) {
            k.rebut = mv.public();
        }
        let info = ProgramInfo::load(pdf).unwrap();
        let input_secrets: Vec<WotsSecret> = (0..info.input_words).map(|j| WotsSecret::from_entropy(input_key_params(), [0x60u8.wrapping_add(j as u8).wrapping_add(id as u8); 32])).collect();
        let family = ZkFamily::lean(search, info, input_secrets.iter().map(|k| k.public()).collect(), moves.iter().map(|k| k.public()).collect());
        let params = ChannelParams { presign_fee: Amount::from_sat(80_000), ..ChannelParams::regtest(Amount::from_sat(20_000_000)) };
        let pubs = [user.public(), hub.public()];
        Session {
            terms,
            cid,
            b_word,
            checks,
            user,
            hub,
            params,
            pubs,
            keys,
            family,
            input_secrets,
            moves,
            outcomes: Contract::outcomes(&TicTacToe),
            pdf: pdf.to_string(),
            words: vec![],
            heads: vec![],
            entries: vec![],
            ladders: HashMap::new(),
            wallets: vec![],
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
        let n = self.m() as usize + 4;
        self.wallets = vec![FeeWallet::new(rt, &self.user.payment, n, 2), FeeWallet::new(rt, &self.hub.payment, n, 2)];
        Funded { tree, op, out }
    }
    /// `V_max` and both reserves: the contract funds no fees.
    fn value(&self) -> Amount {
        self.terms.v_max() + self.terms.reserves()
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
    /// Move `d`: its head signed with depth `d`'s key (lean moves).
    fn move_sig(&self, d: u32) -> WotsSig {
        self.moves[(d - 1) as usize].sign(&self.heads[(d - 1) as usize]).unwrap()
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
    /// Post move `j`: for move 1, `escalate` from the session contract
    /// `c`, with the claim words; otherwise `post` from the ladder output
    /// at `j - 1`. An escalation after off-chain play replays the moves
    /// made, each posted with the signatures the poster holds.
    /// Link `j` of the ladder's chain, pre-signed: a TRUC transaction at
    /// zero fee spending `(op, out)` (for move 1 the contract output `c`,
    /// through `escalate`; else the ladder output after move `j - 1`) into
    /// the ladder output after move `j`, plus a zero-value anchor. Its txid
    /// is fixed by `op`, so the next link can be signed against it at once.
    /// The witness carries the move (and for move 1 the claim words) below
    /// the 2-of-2 signatures; the txid doesn't cover it.
    fn ladder_tx(&mut self, j: u32, op: OutPoint, out: &TxOut, c: Option<&Funded>) -> Transaction {
        let (tree, name) = match c {
            Some(c) => (c.tree.clone(), "escalate"),
            None => (self.ladder(j - 1), "post"),
        };
        let leaf = tree.leaf(name).unwrap();
        let t_out = TxOut { value: out.value, script_pubkey: self.ladder(j).script_pubkey() };
        let anchor = TxOut { value: Amount::ZERO, script_pubkey: ScriptBuf::new_p2a() };
        let mut tx = build_spend(op, &leaf.timelock, vec![t_out, anchor]);
        tx.version = bitcoin::transaction::Version(3);
        let mut w = vec![];
        if c.is_some() {
            for &k in self.claim_words().iter().rev() {
                w.extend(wots_wire(&self.word_sig(k)));
            }
        }
        w.extend(wots_wire(&self.move_sig(j)));
        w.push(sig(&self.hub.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        w.push(sig(&self.user.payment, &tx, 0, std::slice::from_ref(out), &leaf.script));
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &tree.control_block(name).unwrap());
        tx
    }
    /// Broadcast a link of the chain: its poster `by` bumps it with a
    /// child (one-parent-one-child package); the parent and child.
    fn broadcast_link(&mut self, rt: &Regtest, tx: &Transaction, by: Role) -> Transaction {
        assert!(rt.test_accept(tx).is_err(), "a link carries no fee of its own");
        let child = self.wallets[by.idx()].bump(tx, 1);
        rt.submit_package(&[tx.clone(), child.clone()]).unwrap_or_else(|e| panic!("{}: the package: {e:#}", self.cid));
        rt.mine(1).unwrap();
        assert!(rt.confirmations(&tx.compute_txid()).unwrap().is_some(), "the link is mined");
        child
    }
    /// Post move `j` from `(op, out)` (or escalate from `c`), by `by`.
    fn post(&mut self, rt: &Regtest, j: u32, op: OutPoint, out: &TxOut, c: Option<&Funded>, by: Role) -> (OutPoint, TxOut, Transaction) {
        let tx = self.ladder_tx(j, op, out, c);
        self.broadcast_link(rt, &tx, by);
        (OutPoint { txid: tx.compute_txid(), vout: 0 }, tx.output[0].clone(), tx)
    }
    /// The whole chain, pre-signed before anything is broadcast: move 1
    /// through `escalate`, then each move against the previous link's
    /// (already known) txid.
    fn presign_chain(&mut self, c: &Funded) -> Vec<Transaction> {
        let mut chain = vec![self.ladder_tx(1, c.op, &c.out, Some(c))];
        for j in 2..=self.m() {
            let prev = chain.last().unwrap();
            let (op, out) = (OutPoint { txid: prev.compute_txid(), vout: 0 }, prev.output[0].clone());
            chain.push(self.ladder_tx(j, op, &out, None));
        }
        chain
    }
    /// Escalate, by `by`, after the contract's `to_self_delay`.
    fn escalate(&mut self, rt: &Regtest, c: &Funded, by: Role) -> (OutPoint, TxOut, Transaction) {
        rt.mine(u64::from(self.params.to_self_delay)).unwrap();
        self.post(rt, 1, c.op, &c.out, Some(c), by)
    }
    /// A 2-of-2 spend of `(op, out)` under `tree`'s leaf `name`, `wire`
    /// below the signatures, paying `b` in bits and both reserves to Alice.
    /// Alice, its beneficiary, pays the fee.
    fn pay_b(&mut self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let outs = payout(&self.ctx(), &self.terms, &self.b_key(), out.value, Amount::ZERO).unwrap();
        let tx = self.presigned(tree, op, out, name, wire, outs);
        self.wallets[0].pay(tx, out)
    }
    /// A 2-of-2 spend paying everything to the hub (Alice lost); the hub
    /// pays the fee.
    fn pay_hub(&mut self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str) -> Transaction {
        let outs = vec![TxOut { value: out.value, script_pubkey: self.pubs[1].payout_spk.clone() }];
        let tx = self.presigned(tree, op, out, name, vec![], outs);
        self.wallets[1].pay(tx, out)
    }
    /// A pre-signed 2-of-2 spend at zero fee, signed ALL|ANYONECANPAY.
    fn presigned(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>, outs: Vec<TxOut>) -> Transaction {
        let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
        let mut tx = build_spend(op, &leaf.timelock, outs);
        let mut w = wire;
        w.push(presig(&self.hub.payment, &tx, out, &leaf.script));
        w.push(presig(&self.user.payment, &tx, out, &leaf.script));
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
    /// A runtime spend by Alice, as `hub_takes`.
    fn alice_takes(&self, tree: &TapTree, op: OutPoint, out: &TxOut, name: &str, wire: Vec<Vec<u8>>) -> Transaction {
        let leaf = tree.leaf(name).unwrap_or_else(|_| panic!("no leaf {name}"));
        let mut tx = build_spend(op, &leaf.timelock, vec![TxOut { value: out.value - self.params.presign_fee, script_pubkey: self.pubs[0].payout_spk.clone() }]);
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
    /// Every link is pre-signed first (its txid predicted), then each is
    /// broadcast by its mover with a child that pays its fee; the sizes
    /// count both.
    fn play_on_chain(&mut self, rt: &Regtest, c: &Funded) -> (OutPoint, TxOut, u64) {
        let chain = self.presign_chain(c);
        rt.mine(u64::from(self.params.to_self_delay)).unwrap();
        let child = self.broadcast_link(rt, &chain[0], Role::User);
        let mut vb = (chain[0].vsize() + child.vsize()) as u64;
        println!("SESS {}: escalate (move 1 and {} signed input words): {} vB, its child {} vB", self.cid, self.claim_words().len(), chain[0].vsize(), child.vsize());
        let (mut alice, mut hub) = (0u64, 0u64);
        for (k, tx) in chain.iter().enumerate().skip(1) {
            let j = k as u32 + 1;
            let child = self.broadcast_link(rt, tx, mover_at(j));
            let n = (tx.vsize() + child.vsize()) as u64;
            if mover_at(j) == Role::User {
                alice += n;
            } else {
                hub += n;
            }
        }
        vb += alice + hub;
        println!("SESS {}: moves 2 to {} pre-signed, then posted with their children: Alice's {alice} vB, the hub's {hub} vB", self.cid, self.m());
        let last = chain.last().unwrap();
        (OutPoint { txid: last.compute_txid(), vout: 0 }, last.output[0].clone(), vb)
    }
    /// The final step at the last ladder output: Alice's pre-signed proof.
    fn prove_last(&mut self, op: OutPoint, out: &TxOut) -> (Transaction, String) {
        let m = self.m();
        let tree = self.ladder(m);
        let last = self.entries.last().unwrap().clone();
        let rec = last.record.unwrap();
        let class = lngap_zk::guard::key_of(rec.read.opcode, rec.read.micro).unwrap();
        let name = format!("zk_prove_{class}");
        (self.pay_b(&tree, op, out, &name, [final_witness(&last.state, &rec), self.file_wire(m)].concat()), name)
    }
    /// The hub's `halt_exit` disprove at the last ladder output.
    fn halt_exit(&mut self, op: OutPoint, out: &TxOut) -> Transaction {
        let m = self.m();
        let tree = self.ladder(m);
        let last = self.entries.last().unwrap().clone();
        let (rec, cl) = (last.record.unwrap(), self.entries[0].claim.unwrap());
        self.hub_takes(&tree, op, out, "disprove_zk_halt_exit", [nibble_witness(&rec.to_bytes()), nibble_witness(&cl.to_bytes()), self.file_wire(m)].concat())
    }
    /// The hub's input-word check `name` on the first ladder output: with
    /// Alice's signature on word `j` as posted.
    fn check(&mut self, op: OutPoint, out: &TxOut, name: &str, j: usize) -> Transaction {
        let tree = self.ladder(1);
        self.hub_takes(&tree, op, out, name, wots_wire(&self.word_sig(j)))
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
    let rounds = emulator::loader::program_definition::ProgramDefinition::from_config(&pdf(42)).unwrap().nary_def().total_rounds() as u32;
    let mk = |id: u32| Session::new(terms(id, t_close), &pdf(id), rounds);
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
    let (cr, cx, cs, cd, cp, cm, ce) = (r.fund_session(&rt), x.fund_session(&rt), s.fund_session(&rt), df.fund_session(&rt), p.fund_session(&rt), mm.fund_session(&rt), e.fund_session(&rt));
    let cq = q.fund_session(&rt);
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
        let (op, out, vb) = x.play_on_chain(&rt, &cx);
        let tx = x.halt_exit(op, &out);
        rt.mine(u64::from(delta)).unwrap();
        rt.mine_with(std::slice::from_ref(&tx)).unwrap_or_else(|e| panic!("X: halt_exit must fire: {e:#}"));
        assert_eq!(tx.output.len(), 1, "X: everything to the hub");
        println!("SESS X: the execution halted with exit 1; disprove_zk_halt_exit: {} vB; the hub takes everything, both reserves included; the dispute: {} vB", tx.vsize(), vb + tx.vsize() as u64);
    }

    // ===== S, A6: the hub has disappeared =====
    {
        let (op, out, tx) = s.escalate(&rt, &cs, Role::User);
        println!("SESS S: Alice escalates: {} vB", tx.vsize());
        let l1 = s.ladder(1);
        let split = s.pay_b(&l1, op, &out, "split_UserWins", vec![]);
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
        let (op, out, _) = p.escalate(&rt, &cp, Role::User);
        let (op, out, _) = p.post(&rt, 2, op, &out, None, Role::Hub);
        let l2t = p.ladder(2);
        let split = p.pay_hub(&l2t, op, &out, "split_HubWins");
        assert!(rt.test_accept(&split).is_err(), "P: not before Alice's window ends");
        rt.mine(u64::from(w)).unwrap();
        confirm(&rt, &split).unwrap_or_else(|e| panic!("P: the hub's timeout: {e}"));
        println!("SESS P: a false claim of b = 6, abandoned after the hub's answer; the hub's timeout takes everything, her reserve included: {} vB", split.vsize());
    }

    // ===== M: Alice's words sign another session's memo =====
    {
        mm.words[1] = 99;
        let (op, out, _) = mm.escalate(&rt, &cm, Role::User);
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
        let (mut op, mut out, _) = e.escalate(&rt, &ce, Role::Hub);
        for j in 2..=4 {
            (op, out, _) = e.post(&rt, j, op, &out, None, Role::Hub);
        }
        let l4 = e.ladder(4);
        let split = e.pay_hub(&l4, op, &out, "split_HubWins");
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
        let (op, out, _) = q.escalate(&rt, &cq, Role::Hub);
        let true_2 = q.heads[1];
        q.heads[1][4 + 3] ^= 1; // the state digest's fourth byte
        let altered_2 = q.move_sig(2);
        let (op, out, _) = q.post(&rt, 2, op, &out, None, Role::Hub);
        let (op, out, _) = q.post(&rt, 3, op, &out, None, Role::Hub);
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
        let outs = default_outputs(&df.ctx(), &df.terms, cd.out.value, Amount::ZERO).unwrap();
        let bare = df.presigned(&cd.tree, cd.op, &cd.out, "default", vec![], outs);
        let tx = df.wallets[1].pay(bare.clone(), &cd.out);
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
        let (op, out, esc) = s.escalate(&rt, c, Role::User);
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
        confirm(&rt, &proof).unwrap_or_else(|e| panic!("R: the proof: {e}"));
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
