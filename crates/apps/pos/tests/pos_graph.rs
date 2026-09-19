//! The PoS absence-claim graph on regtest (plan step 4): the three paths of
//! the claim/refute/dispute dance for one depth, with the node enforcing the
//! real timelocks. Claimant = Hub, mover = User (depth 1).

use bitcoin::key::Keypair;
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::{Amount, OutPoint, ScriptBuf, Transaction, TxOut};
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_btc::sighash::sign_tapscript;
use lngap_btc::taptree::{Leaf, TapTree};
use lngap_btc::tx::{build_spend, Timelock};
use lngap_btc::witness::tapscript_witness;
use lngap_channel::{ChannelParams, CommitCtx, PartyKeys, Role};
use lngap_contract::toy::CoinFlip;
use lngap_contract::{Program, CODE_BITS};
use lngap_ec_wots::{Attester, EpochTable};
use lngap_factchain::slot::SlotEntry;
use lngap_lamport::{uint_to_bits, Reveal, SecretKey as LamportSecret};
use lngap_pos::graph::{absent_leaf, claim_tree, refuted_tree};
use lngap_pos::refute::{refute_key, refute_witness, HEAD_CHUNK_START, HEAD_CHUNKS};
use lngap_pos::PosMiner;

const SEED: [u8; 32] = [7u8; 32];

fn sink() -> ScriptBuf {
    TapTree::new(vec![Leaf::new(
        "x",
        bitcoin::script::Builder::new().push_int(1).into_script(),
        Timelock::NONE,
    )])
    .unwrap()
    .script_pubkey()
}

/// A slot-1 block whose entry's head carries the move `mv`.
fn sealed_move(mv: u8) -> (lngap_pos::SealedBlock, EpochTable) {
    let attester = Attester::new(SEED);
    let (gen, _t0) = lngap_pos::genesis(&attester);
    let mut miner = PosMiner::new(SEED, gen.header.digest(), 0);
    let entry = SlotEntry {
        game_id: 1,
        depth: 1,
        mover: 0,
        mv,
        state: 0x12345,
        sigs: vec![[0x11; 20]; 21],
    };
    miner.submit(entry.encode());
    miner.seal_next(1).unwrap()
}

fn sign_with(secret: &SecretKey, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    let kp = Keypair::from_secret_key(SECP256K1, secret);
    sign_tapscript(&kp, tx, 0, std::slice::from_ref(prev), leaf)
        .unwrap()
        .as_ref()
        .to_vec()
}

fn sign_tx(kp: &Keypair, tx: &Transaction, prev: &TxOut, leaf: &ScriptBuf) -> Vec<u8> {
    sign_tapscript(kp, tx, 0, std::slice::from_ref(prev), leaf)
        .unwrap()
        .as_ref()
        .to_vec()
}

/// Consumption-order items to wire order (bottom of stack first).
fn wire(mut consumption: Vec<Vec<u8>>) -> Vec<Vec<u8>> {
    consumption.reverse();
    consumption
}

struct Setup {
    user: PartyKeys,
    hub: PartyKeys,
    params: ChannelParams,
    claim_from: u32,
}

struct Path {
    c_tree: TapTree,
    a_tree: TapTree,
    p_tree: TapTree,
    mover_code: LamportSecret,
    claimant_code: LamportSecret,
    refute_sk: lngap_lamport::winternitz::WotsSecret,
}

/// The funded contract output C carrying the depth-1 absence claim, and the
/// two follow-on trees.
fn open(rt: &Regtest, s: &Setup, table: &EpochTable) -> (Path, OutPoint, TxOut) {
    let outcomes = CoinFlip.outcomes();
    let refute_sk = refute_key([9u8; 32]);
    let mover_code = LamportSecret::from_entropy(CODE_BITS, [21u8; 32]);
    let claimant_code = LamportSecret::from_entropy(CODE_BITS, [22u8; 32]);
    let pubs = [s.user.public(), s.hub.public()];
    let ctx = CommitCtx { params: &s.params, keys: &pubs, broadcaster: Role::User, seq: 1, rev_hash: [0u8; 20] };

    let c_tree = TapTree::new(vec![absent_leaf(&pubs[1].payment, s.claim_from)]).unwrap();
    let a_tree = claim_tree(&ctx, table, &refute_sk.public(), &outcomes, &claimant_code.public()).unwrap();
    let p_tree = refuted_tree(&ctx, &refute_sk.public(), &pubs[1].payment, &outcomes, &mover_code.public()).unwrap();
    let (op, prev) = rt.fund(&c_tree.script_pubkey(), Amount::from_sat(200_000)).unwrap();
    (Path { c_tree, a_tree, p_tree, mover_code, claimant_code, refute_sk }, op, prev)
}

/// Spend C by the absence claim, producing the claim output A. Returns the
/// claim tx and A's prevout.
fn claim(rt: &Regtest, s: &Setup, p: &Path, c_op: OutPoint, c_prev: &TxOut) -> (Transaction, OutPoint, TxOut) {
    let leaf = p.c_tree.leaf("absent").unwrap();
    let mut tx = build_spend(
        c_op,
        &leaf.timelock,
        vec![TxOut { value: Amount::from_sat(190_000), script_pubkey: p.a_tree.script_pubkey() }],
    );
    let sig = sign_tx(&s.hub.payment, &tx, c_prev, &leaf.script);
    tx.input[0].witness = tapscript_witness(&[sig], &leaf.script, &p.c_tree.control_block("absent").unwrap());
    rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the absence claim must mine: {e}"));
    let a_op = OutPoint { txid: tx.compute_txid(), vout: 0 };
    let a_prev = tx.output[0].clone();
    (tx, a_op, a_prev)
}

/// The split witness (both payment signatures plus the code reveal), wire
/// order. Consumption order is sig_a (user) first per two_of_two_verify.
fn split_witness(
    s: &Setup,
    tx: &Transaction,
    prev: &TxOut,
    leaf: &ScriptBuf,
    code_key: &LamportSecret,
    code: u8,
) -> Vec<Vec<u8>> {
    let sig_u = sign_tx(&s.user.payment, tx, prev, leaf);
    let sig_h = sign_tx(&s.hub.payment, tx, prev, leaf);
    let reveal: Reveal = code_key.reveal_bits(&uint_to_bits(u32::from(code), CODE_BITS)).unwrap();
    let mut consumption = vec![sig_u, sig_h];
    consumption.extend(reveal.consumption_order());
    wire(consumption)
}

#[test]
fn pos_graph_three_paths() {
    let rt = Regtest::start().unwrap();
    let user = PartyKeys::from_seed(Role::User, Seed::from_label("pos-graph/user"));
    let hub = PartyKeys::from_seed(Role::Hub, Seed::from_label("pos-graph/hub"));
    let params = ChannelParams::regtest(Amount::from_sat(200_000));
    let claim_from = rt.height().unwrap() + 2;
    let s = Setup { user, hub, params, claim_from };

    // ================= path 1: the timeout split (Bob never refutes) ====
    {
        let (_block, table) = sealed_move(5);
        let (p, c_op, c_prev) = open(&rt, &s, &table);
        rt.mine(2).unwrap(); // past claim_from
        let (_ctx_tx, a_op, a_prev) = claim(&rt, &s, &p, c_op, &c_prev);

        // too-early split must fail (CSV window not met)
        let o = &CoinFlip.outcomes()[0];
        let leaf = p.a_tree.leaf(&format!("split_{}", o.name)).unwrap();
        let early = build_spend(a_op, &leaf.timelock, vec![TxOut { value: Amount::from_sat(180_000), script_pubkey: sink() }]);
        let w = split_witness(&s, &early, &a_prev, &leaf.script, &p.claimant_code, o.code);
        let mut early = early;
        early.input[0].witness = tapscript_witness(&w, &leaf.script, &p.a_tree.control_block(&leaf_name(&p, o)).unwrap());
        assert!(rt.test_accept(&early).is_err(), "the split must wait out the window");

        rt.mine(u64::from(s.params.delta) + 1).unwrap();
        let tx = build_spend(a_op, &leaf.timelock, vec![TxOut { value: Amount::from_sat(180_000), script_pubkey: sink() }]);
        let w = split_witness(&s, &tx, &a_prev, &leaf.script, &p.claimant_code, o.code);
        let mut tx = tx;
        tx.input[0].witness = tapscript_witness(&w, &leaf.script, &p.a_tree.control_block(&format!("split_{}", o.name)).unwrap());
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the timeout split must mine: {e}"));
        println!("REGTEST pos-graph timeout split: {} vB", tx.vsize());
    }

    // ================= path 2: refutation, then the disprove fires ======
    {
        let (block, table) = sealed_move(9); // the venue attested an ILLEGAL move
        let head = block.header.head();
        let (p, c_op, c_prev) = open(&rt, &s, &table);
        rt.mine(2).unwrap();
        let (_c, a_op, a_prev) = claim(&rt, &s, &p, c_op, &c_prev);

        // Bob refutes: the readout of the slot's attested head + the tie
        let leaf = p.a_tree.leaf("refute").unwrap();
        let mut rtx = build_spend(a_op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(180_000), script_pubkey: p.p_tree.script_pubkey() }]);
        let head_sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&block.attestation.secrets[HEAD_CHUNK_START + j], &rtx, &a_prev, &leaf.script))
            .collect();
        let commit_sig = p.refute_sk.sign(&head).unwrap();
        let w = refute_witness(&head, &head_sigs, &commit_sig);
        rtx.input[0].witness = tapscript_witness(&w, &leaf.script, &p.a_tree.control_block("refute").unwrap());
        rt.mine_with(&[rtx.clone()]).unwrap_or_else(|e| panic!("the refutation must mine: {e}"));
        let p_op = OutPoint { txid: rtx.compute_txid(), vout: 0 };
        let p_prev = rtx.output[0].clone();

        // Alice disproves the parked tuple after delta
        rt.mine(u64::from(s.params.delta) + 1).unwrap();
        let dleaf = p.p_tree.leaf("disprove").unwrap();
        let mut dtx = build_spend(p_op, &dleaf.timelock, vec![TxOut { value: Amount::from_sat(170_000), script_pubkey: sink() }]);
        let dsig = sign_tx(&s.hub.payment, &dtx, &p_prev, &dleaf.script);
        let mut w = lngap_pos::refute::disprove_witness(&commit_sig);
        w.push(dsig);
        dtx.input[0].witness = tapscript_witness(&w, &dleaf.script, &p.p_tree.control_block("disprove").unwrap());
        rt.mine_with(&[dtx.clone()]).unwrap_or_else(|e| panic!("the disprove of the parked illegal move must mine: {e}"));
        println!("REGTEST pos-graph: refute {} vB, disprove {} vB", rtx.vsize(), dtx.vsize());
    }

    // ================= path 3: refutation stands, the mover splits ======
    {
        let (block, table) = sealed_move(5); // a legal move
        let head = block.header.head();
        let (p, c_op, c_prev) = open(&rt, &s, &table);
        rt.mine(2).unwrap();
        let (_c, a_op, a_prev) = claim(&rt, &s, &p, c_op, &c_prev);

        let leaf = p.a_tree.leaf("refute").unwrap();
        let mut rtx = build_spend(a_op, &Timelock::NONE, vec![TxOut { value: Amount::from_sat(180_000), script_pubkey: p.p_tree.script_pubkey() }]);
        let head_sigs: Vec<Vec<u8>> = (0..HEAD_CHUNKS)
            .map(|j| sign_with(&block.attestation.secrets[HEAD_CHUNK_START + j], &rtx, &a_prev, &leaf.script))
            .collect();
        let commit_sig = p.refute_sk.sign(&head).unwrap();
        let w = refute_witness(&head, &head_sigs, &commit_sig);
        rtx.input[0].witness = tapscript_witness(&w, &leaf.script, &p.a_tree.control_block("refute").unwrap());
        rt.mine_with(&[rtx.clone()]).unwrap_or_else(|e| panic!("the refutation must mine: {e}"));
        let p_op = OutPoint { txid: rtx.compute_txid(), vout: 0 };
        let p_prev = rtx.output[0].clone();

        // the disprove cannot fire on the legal tuple
        rt.mine(u64::from(s.params.delta) + 1).unwrap();
        let dleaf = p.p_tree.leaf("disprove").unwrap();
        let dtx = build_spend(p_op, &dleaf.timelock, vec![TxOut { value: Amount::from_sat(170_000), script_pubkey: sink() }]);
        let dsig = sign_tx(&s.hub.payment, &dtx, &p_prev, &dleaf.script);
        let mut w = lngap_pos::refute::disprove_witness(&commit_sig);
        w.push(dsig);
        let mut dtx = dtx;
        dtx.input[0].witness = tapscript_witness(&w, &dleaf.script, &p.p_tree.control_block("disprove").unwrap());
        assert!(rt.test_accept(&dtx).is_err(), "a legal move's tuple must not be disprovable");

        // the mover's split after delta + delta'
        rt.mine(u64::from(s.params.delta_prime) + 1).unwrap();
        let o = &CoinFlip.outcomes()[1];
        let sleaf = p.p_tree.leaf(&format!("split_{}", o.name)).unwrap();
        let tx = build_spend(p_op, &sleaf.timelock, vec![TxOut { value: Amount::from_sat(170_000), script_pubkey: sink() }]);
        let w = split_witness(&s, &tx, &p_prev, &sleaf.script, &p.mover_code, o.code);
        let mut tx = tx;
        tx.input[0].witness = tapscript_witness(&w, &sleaf.script, &p.p_tree.control_block(&format!("split_{}", o.name)).unwrap());
        rt.mine_with(&[tx.clone()]).unwrap_or_else(|e| panic!("the refuted split must mine: {e}"));
        println!("REGTEST pos-graph refuted split: {} vB", tx.vsize());
    }
}

fn leaf_name(p: &Path, o: &lngap_contract::Outcome) -> String {
    let _ = p;
    format!("split_{}", o.name)
}
