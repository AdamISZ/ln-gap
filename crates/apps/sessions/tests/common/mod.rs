//! Shared by the sessions tests: fee coins and the mempool.
#![allow(dead_code)]

use bitcoin::key::Keypair;
use bitcoin::opcodes::all::OP_CHECKSIG;
use bitcoin::script::Builder;
use bitcoin::{Amount, OutPoint, ScriptBuf, Sequence, Transaction, TxIn, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;

pub fn sig(kp: &Keypair, tx: &Transaction, input: usize, prevouts: &[TxOut], leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, input, prevouts, leaf).unwrap().as_ref().to_vec()
}

// ----------------------------------------------------------------- fees

/// The feerate the parties pay, sat/vB.
pub const FEERATE: u64 = 2;
/// Fee coins: small for moves and timeouts, large for the final proof.
pub const SMALL: Amount = Amount::from_sat(20_000);
pub const LARGE: Amount = Amount::from_sat(200_000);

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
pub struct FeeWallet {
    kp: Keypair,
    tree: TapTree,
    coins: Vec<(OutPoint, TxOut)>,
}

impl FeeWallet {
    /// `small` small coins and `large` large ones, from one funding coin
    /// fanned out (two blocks).
    pub fn new(rt: &Regtest, kp: &Keypair, small: usize, large: usize) -> FeeWallet {
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
    pub fn bump(&mut self, parent: &Transaction, anchor: u32) -> Transaction {
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
    pub fn pay(&mut self, mut tx: Transaction, prevout: &TxOut) -> Transaction {
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
pub fn confirm(rt: &Regtest, tx: &Transaction) -> std::result::Result<(), String> {
    rt.send_raw(tx).map_err(|e| format!("{e:#}"))?;
    rt.mine(1).map_err(|e| format!("{e:#}"))?;
    match rt.confirmations(&tx.compute_txid()) {
        Ok(Some(_)) => Ok(()),
        _ => Err("not mined".into()),
    }
}

