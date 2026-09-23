//! Step 5 of POS_FACTCHAIN_PLAN.md (D38): the validator bond on regtest.
//!
//! A venue attester posts a bond UTXO whose taptree carries the reclaim
//! (CLTV), burn (the fixed-R key-leak mirror), and per-(slot, chunk)
//! possession-pair slash leaves (bond.rs). The scenario equivocates the
//! venue at a covered slot and plays the watcher by hand:
//!
//! - the SLASH spend: two possession proofs at the equivocated chunk take
//!   the bond to the watcher (the always-on path — no nonce-discipline
//!   assumption), once the evidence race has opened (`race_from`, D46);
//! - the BURN spend as the fee RACE (D46): the equivocation reuses the
//!   chunk's nonce, so the cheater itself extracts the group key
//!   (`extract_group_key`) first and broadcasts a low-fee self-payment
//!   through the mirror leaf; the watcher's spend — one zero-value
//!   OP_RETURN output, the whole bond as fee — replaces it in the
//!   mempool (RBF), and the block carries the watcher's: the value went
//!   to the miner, the cheater got nothing;
//! - negatives: evidence spends before `race_from` are rejected (no head
//!   start), the same value twice is not evidence, a sig under the wrong
//!   value fails, a wrong preimage fails, the reclaim is locked until
//!   expiry and then pays the validator back.
//!
//! Deliberately a self-contained fixture here, not a harness world: no
//! channel is involved, so the channel `Harness` is the wrong tool. The
//! watcher/validator plumbing (who observes the equivocation — the client
//! already names it, `Observation::Equivocation` — and who files the
//! spend) is left for later, per the step's scope.

use bitcoin::hashes::Hash;
use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, ScriptBuf, Transaction, TxOut};
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_channel::Role;
use lngap_contract::Contract;
use lngap_ec_wots::{chunk_value, extract_group_key, slash_any_witness, snum, Attestation, Attester, EpochTable};
use lngap_factchain::slot::SlotEntry;
use lngap_factchain::{entry_head, entry_root, Header};
use lngap_pos::bond::{bond_tree, BondSpec};
use lngap_pos::{PosClient, PosMiner, SealedBlock, HEADER_CHUNKS};
use lngap_tictactoe::{Board, TicTacToe};

/// The venue's attester seed (the single key standing in for the FROST
/// group key, per the ec-wots design).
const SEED: [u8; 32] = [0x5A; 32];
/// The slot the venue equivocates at.
const SLOT: u32 = 1;

fn sign_with(secret: &SecretKey, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(&Keypair::from_secret_key(SECP256K1, secret), tx, 0, std::slice::from_ref(prev), leaf)
        .unwrap()
        .as_ref()
        .to_vec()
}

/// The venue seals SLOT carrying the user's X@4 — then equivocates: a
/// second block at SLOT carrying X@0, attested under the same epoch table
/// (the fixed-R discipline: the chunk's nonce is shared, so the key leaks).
/// Returns the slot's table, both headers, and both attestations.
fn equivocation() -> (EpochTable, Vec<u8>, Vec<u8>, Attestation, Attestation) {
    let attester = Attester::new_fixed_r(SEED);
    let (gen, _t0) = lngap_pos::genesis(&attester);
    let mut miner = PosMiner::new_fixed_r(SEED, gen.header.digest(), 0);
    let state_u32 = |b: &Board| lngap_lamport::bits_to_uint(&TicTacToe.state_bits(b));
    let entry = |mv: u8| {
        let new = TicTacToe.transition(&Board::empty(), &mv, Role::User).unwrap();
        SlotEntry {
            game_id: 1,
            depth: SLOT as u8,
            mover: Role::User.idx() as u8,
            mv,
            state: state_u32(&new),
            sigs: vec![[0x11; 20]; 21],
        }
        .encode()
    };
    // block A through the miner (an honest seal), block B by hand
    miner.submit(entry(4));
    let (block_a, table) = miner.seal_next(SLOT).unwrap();
    let eb = entry(0);
    let header_b = Header::new(&gen.header.digest(), &entry_root(&eb), &entry_head(&eb), SLOT);
    let hdr_b = header_b.as_bytes().to_vec();
    let att_b = miner.attester().attest(&table, header_b.as_bytes());
    let hdr_a = block_a.header.as_bytes().to_vec();
    // both attestations open the same slot's table; the client names the event
    let mut client = PosClient::from_checkpoint(0, gen.header.digest());
    client.verify_and_append(&block_a, &table).unwrap();
    let block_b = SealedBlock {
        header: header_b,
        entry: eb,
        attestation: att_b,
    };
    assert!(
        matches!(
            client.observe(&block_b, &table),
            Ok(lngap_pos::Observation::Equivocation(_))
        ),
        "the second attested header at slot {SLOT} is the equivocation"
    );
    let SealedBlock { attestation: att_b, .. } = block_b;
    (table, hdr_a, hdr_b, block_a.attestation, att_b)
}

/// The skeleton-with-witness, NOT broadcast (for negatives).
fn dry(tx: &Transaction, w: Vec<Vec<u8>>, leaf: &ScriptBuf, cb: &bitcoin::taproot::ControlBlock) -> Transaction {
    let mut tx = tx.clone();
    tx.input[0].witness = tapscript_witness(&w, leaf, cb);
    tx
}

#[test]
fn bond_slash_burn_reclaim() {
    let rt = Regtest::start().unwrap();
    let (table, hdr_a, hdr_b, att_a, att_b) = equivocation();
    // the watcher finds the equivocation chunk: the headers differ there
    let j = (0..HEADER_CHUNKS)
        .find(|&j| chunk_value(&hdr_a, j) != chunk_value(&hdr_b, j))
        .expect("two different headers differ at some chunk");
    let (v_a, v_b) = (chunk_value(&hdr_a, j), chunk_value(&hdr_b, j));
    let attester = Attester::new_fixed_r(SEED); // the fixture's registry view
    let r_x = attester.nonce_point(SLOT as u64, j, v_a); // registry data

    let validator = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[9u8; 32]).unwrap());
    let (val_x, _) = validator.x_only_public_key();
    let watcher = Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[8u8; 32]).unwrap());
    let (watch_x, _) = watcher.x_only_public_key();
    let watcher_spk = ScriptBuf::new_p2tr(SECP256K1, watch_x, None);
    let value = Amount::from_sat(100_000);
    let h0 = rt.height().unwrap();
    let spec = BondSpec {
        value,
        validator: val_x,
        expiry: h0 + 50,
        race_window: 42, // the race opens at h0 + 8: late relative to a real bond's life, early enough for the fixture

        burn_mirror: attester.burn_mirror().to_byte_array(),
    };
    let tree = bond_tree(&spec, &[(SLOT, &table)]).unwrap();
    let bond_spk = tree.script_pubkey();
    let fee = Amount::from_sat(500);

    // ============ slash: the possession pair takes bond A ==============
    {
        let (b_op, b_prev) = rt.fund(&bond_spk, value).unwrap();
        let name = format!("slash_{SLOT}_{j}");
        let l = tree.leaf(&name).unwrap();
        let mk = || {
            build_spend(
                b_op,
                &l.timelock,
                vec![TxOut {
                    value: b_prev.value - fee,
                    script_pubkey: watcher_spk.clone(),
                }],
            )
        };
        // before the race opens the evidence is not spendable — by anyone,
        // the cheater included: no head start (D46)
        let tx = mk();
        let sig_a = sign_with(&att_a.secrets[j], &tx, &b_prev, &l.script);
        let sig_b = sign_with(&att_b.secrets[j], &tx, &b_prev, &l.script);
        let early = dry(&tx, slash_any_witness(sig_a, v_a, sig_b, v_b), &l.script, &tree.control_block(&name).unwrap());
        assert!(rt.test_accept(&early).is_err(), "the slash must wait for the race to open");
        rt.mine(u64::from(spec.race_from() - rt.height().unwrap())).unwrap();
        let tx = mk();
        let sig_a = sign_with(&att_a.secrets[j], &tx, &b_prev, &l.script);
        let sig_b = sign_with(&att_b.secrets[j], &tx, &b_prev, &l.script);
        let tx = dry(&tx, slash_any_witness(sig_a, v_a, sig_b, v_b), &l.script, &tree.control_block(&name).unwrap());
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the slash must mine: {e}"));
        println!("REGTEST 5: slash spend: {} vB", tx.vsize());
    }

    // ============ burn: the fee race on bond B (D46) ====================
    {
        let (b_op, b_prev) = rt.fund(&bond_spk, value).unwrap();
        let x = extract_group_key(&attester.group_key(), SLOT as u64, j, v_a, v_b, &r_x, &att_a.secrets[j], &att_b.secrets[j])
            .unwrap();
        // the public correctness check: the extracted key IS the group key
        assert_eq!(
            Keypair::from_secret_key(SECP256K1, &x).x_only_public_key().0,
            attester.group_key(),
            "the equivocation must leak the group key itself"
        );
        let l = tree.leaf("burn").unwrap();
        let cb = tree.control_block("burn").unwrap();
        let cheater_spk = ScriptBuf::new_p2tr(SECP256K1, val_x, None);
        // the CHEATER moves first: it knows the key before anyone, and
        // spends the bond back to itself with a token fee
        let self_pay = build_spend(
            b_op,
            &l.timelock,
            vec![TxOut {
                value: b_prev.value - fee,
                script_pubkey: cheater_spk,
            }],
        );
        let self_pay = dry(&self_pay, vec![x.secret_bytes().to_vec()], &l.script, &cb);
        let self_txid = rt.send_raw(&self_pay).expect("the cheater's self-payment enters the mempool");
        // the WATCHER answers with the burn: one zero-value OP_RETURN
        // output, the whole bond as fee — it replaces the self-payment.
        // (The OP_RETURN carries a few bytes: with an empty one the
        // transaction is 61 bytes and Core refuses it as `tx-size-small`,
        // the 64-byte-transaction guard, whatever the standardness flags.)
        let burn = build_spend(
            b_op,
            &l.timelock,
            vec![TxOut {
                value: Amount::ZERO,
                script_pubkey: ScriptBuf::new_op_return(b"lngap-bond-burn"),
            }],
        );
        let burn = dry(&burn, vec![x.secret_bytes().to_vec()], &l.script, &cb);
        let burn_txid = rt.send_raw_any_fee(&burn).expect("the full-fee burn replaces the self-payment");
        let mempool = rt.mempool().unwrap();
        assert!(mempool.contains(&burn_txid) && !mempool.contains(&self_txid), "RBF: the burn evicts the cheater's spend");
        rt.mine(1).unwrap();
        assert!(!rt.is_unspent(&b_op).unwrap(), "the bond is spent");
        assert!(rt.confirmations(&burn_txid).unwrap().is_some(), "the burn confirmed");
        assert!(rt.confirmations(&self_txid).is_err() || rt.confirmations(&self_txid).unwrap().is_none(), "the self-payment never confirmed");
        println!("REGTEST 5: burn by fee race: {} vB, {} sat to the miner", burn.vsize(), b_prev.value.to_sat());
    }

    // ============ negatives + the reclaim path on bond C ===============
    {
        let (b_op, b_prev) = rt.fund(&bond_spk, value).unwrap();
        let name = format!("slash_{SLOT}_{j}");
        let l = tree.leaf(&name).unwrap();
        let mk = || {
            build_spend(
                b_op,
                &l.timelock,
                vec![TxOut {
                    value: b_prev.value - fee,
                    script_pubkey: watcher_spk.clone(),
                }],
            )
        };
        // the same value twice is NOT evidence: v1 == v2 fails the gate
        let t = mk();
        let s1 = sign_with(&att_a.secrets[j], &t, &b_prev, &l.script);
        let s1b = sign_with(&att_a.secrets[j], &t, &b_prev, &l.script);
        let w = vec![s1b, snum(v_a), s1, snum(v_a)];
        let bad = dry(&t, w, &l.script, &tree.control_block(&name).unwrap());
        assert!(rt.test_accept(&bad).is_err(), "the same value twice must not slash");
        // a sig under the wrong value fails its possession proof
        let t = mk();
        let sig_wrong_a = sign_with(&att_a.secrets[j], &t, &b_prev, &l.script); // secret for v_a
        let sig_wrong_b = sign_with(&att_b.secrets[j], &t, &b_prev, &l.script); // for v_b
        let w = slash_any_witness(sig_wrong_a, v_b, sig_wrong_b, v_a); // presented swapped
        let bad = dry(&t, w, &l.script, &tree.control_block(&name).unwrap());
        assert!(rt.test_accept(&bad).is_err(), "a wrong-value possession must fail");
        // a wrong preimage does not open the burn mirror
        let l = tree.leaf("burn").unwrap();
        let t = build_spend(
            b_op,
            &l.timelock,
            vec![TxOut {
                value: b_prev.value - fee,
                script_pubkey: ScriptBuf::new_op_return(&[]),
            }],
        );
        let bad = dry(&t, vec![[0x42; 32].to_vec()], &l.script, &tree.control_block("burn").unwrap());
        assert!(rt.test_accept(&bad).is_err(), "a wrong preimage must not burn");
        // the reclaim is locked until expiry
        let l = tree.leaf("reclaim").unwrap();
        let mk_reclaim = || {
            build_spend(
                b_op,
                &l.timelock,
                vec![TxOut {
                    value: b_prev.value - fee,
                    script_pubkey: ScriptBuf::new_p2tr(SECP256K1, val_x, None),
                }],
            )
        };
        let t = mk_reclaim();
        let sig = sign_with(&SecretKey::from_slice(&[9u8; 32]).unwrap(), &t, &b_prev, &l.script);
        let bad = dry(&t, vec![sig], &l.script, &tree.control_block("reclaim").unwrap());
        assert!(rt.test_accept(&bad).is_err(), "the bond cannot be reclaimed before expiry");
        rt.mine(u64::from(spec.expiry - rt.height().unwrap())).unwrap();
        let t = mk_reclaim();
        let sig = sign_with(&SecretKey::from_slice(&[9u8; 32]).unwrap(), &t, &b_prev, &l.script);
        let tx = dry(&t, vec![sig], &l.script, &tree.control_block("reclaim").unwrap());
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the reclaim must mine after expiry: {e}"));
        println!("REGTEST 5: reclaim spend: {} vB", tx.vsize());
    }
}
