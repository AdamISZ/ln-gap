//! Phase 2b of the SPV dispute path: real regtest data through the
//! register-file claim. The hub claims a ledger entry anchored (OP_RETURN)
//! in the last block of a valid header chain from a checkpoint; the user checks
//! the claim's predicates natively and disputes what fails: a header that
//! does not link, a header without proof of work, a wrong Merkle sibling,
//! a wrong ledger sibling. The user may also refute the hub's chain with a
//! heavier one (a fork scenario), itself disputable by the hub.

use std::sync::Arc;

use bitcoin::hashes::Hash;
use bitcoin::Amount;
use bitcoincore_rpc::RpcApi;
use lngap_btc::keys::Seed;
use lngap_btc::regtest::Regtest;
use lngap_channel::Role;
use lngap_contract::{ClaimData, ClaimSpec, Program, ProgramRegistry};
use lngap_harness::Harness;
use lngap_spv::chain::{anchor_bytes, anchor_tx, p2tr_spk, sign_keypath, MerklePath, RawHeader};
use lngap_spv::claim::first_failing_step;
use lngap_spv::ledger::{entry_bytes, key_of, Ledger};
use lngap_spv::{AnchorClaim, HeaderChainClaim, Spv};

const STAKE: Amount = Amount::from_sat(50_000);
const K: u64 = 1_000;
fn sat(n: u64) -> Amount {
    Amount::from_sat(n)
}

/// Regtest data for the claims: the hub's chain of `m` headers after the
/// checkpoint (with the anchor in the last), and the "real" chain of `m + 1`
/// headers from the same checkpoint (a fork if `fork`, else the hub's
/// chain plus one block).
struct World {
    rt: Arc<Regtest>,
    hub_claim: AnchorClaim,
    real_chain: HeaderChainClaim,
}

impl World {
    fn new(m: usize, fork: bool) -> World {
        let rt = Arc::new(Regtest::start().unwrap());
        let rpc = &rt.rpc;
        // the previous anchor: a plain P2TR output of the hub's anchor key
        let anchor_kp = Seed::from_label("hub-anchor").keypair("anchor");
        let anchor_key = anchor_kp.x_only_public_key().0;
        let (prev_op, prev_txout) = rt.fund(&p2tr_spk(&anchor_key), sat(20_000)).unwrap();
        // the ledger
        let mut ledger = Ledger::default();
        ledger.insert(b"alice", &[0xa1; 32]);
        ledger.insert(b"bob", &[0xb0; 32]);
        ledger.insert(b"carol", &[0xca; 32]);
        let root = ledger.root();
        let key = key_of(b"bob");
        let entry = entry_bytes(b"bob", &[0xb0; 32]);
        // the checkpoint: the tip before the anchor block
        let cp_height = rt.height().unwrap();
        let cp_hash = rpc.get_block_hash(u64::from(cp_height)).unwrap();
        let cp = RawHeader::from_header(&rpc.get_block_header(&cp_hash).unwrap());
        // m - 1 blocks, then the anchor transaction in the m-th (the claim's last header)
        rt.mine(m as u64 - 1).unwrap();
        let mut tx = anchor_tx(prev_op, &root, p2tr_spk(&anchor_key), sat(19_000));
        sign_keypath(&mut tx, &prev_txout, &anchor_kp).unwrap();
        let anchor_height = rt.mine_with(&[tx.clone()]).unwrap();
        assert_eq!(anchor_height, cp_height + m as u32);
        let headers_of = |from: u32, to: u32| -> Vec<RawHeader> {
            (from..=to).map(|h| RawHeader::from_header(&rpc.get_block_header(&rpc.get_block_hash(u64::from(h)).unwrap()).unwrap())).collect()
        };
        let hub_headers = headers_of(cp_height + 1, cp_height + m as u32);
        let txids = rt.block_txids(anchor_height).unwrap();
        let index = txids.iter().position(|t| *t == tx.compute_txid()).unwrap();
        let merkle = MerklePath::for_tx(&txids, index);
        assert_eq!(merkle.root(&tx.compute_txid().to_byte_array()), hub_headers[m - 1].merkle_root());
        let real_headers = if fork {
            // orphan the hub's chain and mine a longer one from the checkpoint
            let first = rpc.get_block_hash(u64::from(cp_height + 1)).unwrap();
            rpc.invalidate_block(&first).unwrap();
            rt.mine(m as u64 + 1).unwrap();
            let h = headers_of(cp_height + 1, cp_height + m as u32 + 1);
            rpc.reconsider_block(&first).unwrap();
            assert_eq!(rt.height().unwrap(), cp_height + m as u32 + 1, "the longer chain stays active");
            h
        } else {
            rt.mine(1).unwrap();
            headers_of(cp_height + 1, cp_height + m as u32 + 1)
        };
        let nbits = cp.nbits();
        let hub_claim = AnchorClaim {
            chain: HeaderChainClaim { checkpoint: cp.digest(), nbits, headers: hub_headers },
            prev_anchor: prev_op,
            anchor_tx: anchor_bytes(&tx),
            merkle,
            entry,
            ledger: ledger.path(key),
        };
        let real_chain = HeaderChainClaim { checkpoint: cp.digest(), nbits, headers: real_headers };
        World { rt, hub_claim, real_chain }
    }

    /// A harness whose `spv` program carries the hub's claim and the user's refutation.
    fn harness(&self, label: &str, hub: (ClaimSpec, ClaimData), user: (ClaimSpec, ClaimData)) -> Harness {
        let prog = Arc::new(Spv { hub, user }) as Arc<dyn Program>;
        let mut h = Harness::with_regtest(self.rt.clone(), label, ProgramRegistry::new().with(prog)).unwrap();
        // the hub presents its claim on-chain (the user is non-cooperative from the start)
        h.hub.queue_moves(1, vec![vec![true]]);
        let msgs = h.hub.open_contract(1, Spv::NAME, [STAKE, STAKE]).unwrap();
        h.bus(msgs).unwrap();
        h.user.faults.stop_from_seq = Some(1);
        h
    }
}

fn roles(h: &Harness) -> Vec<String> {
    h.roles_seen()
}

fn output_of(h: &Harness, f: impl Fn(&str) -> bool) -> Amount {
    let s = h.seen.iter().find(|s| f(&s.role)).unwrap();
    h.rt.get_tx(&s.txid).unwrap().output[0].value
}

fn sizes(h: &Harness) -> String {
    h.seen.iter().map(|s| format!("{} {} vB", s.role, s.vsize)).collect::<Vec<_>>().join("; ")
}

fn disproof(h: &Harness) -> Option<String> {
    roles(h).into_iter().find(|r| r.starts_with("cpred_") || r.starts_with("simple_") || r.starts_with("round_") || r.starts_with("sched_") || r.starts_with("block_") || r.starts_with("ccopy_") || r.starts_with("ckeep_") || r.starts_with("re_"))
}

#[test]
fn honest_anchor_claim_is_accepted() {
    let w = World::new(3, false);
    let hub = w.hub_claim.build();
    assert_eq!(first_failing_step(&hub.0, &hub.1), None, "the honest claim is valid");
    eprintln!("CLAIM {} steps, {} rounds", hub.0.steps.len(), hub.0.rounds());
    let mut h = w.harness("p3-honest", hub, w.real_chain.build());
    h.step_until(120, |h| roles(h).iter().any(|r| r.starts_with("split_"))).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.contains(&"move_1".to_string()) && r.contains(&"split_1_HubWins".to_string()), "{r:?}");
    assert!(!r.iter().any(|x| x == "dispute"));
    assert!(h.user.narrative().iter().any(|l| l.contains("claimed end state") && l.contains("correct")));
    println!("{}", h.narrative());
}

/// The hub's second header does not link to the first: the link predicate
/// of its first compression fails and the user disproves it with `cpred`.
#[test]
fn header_that_does_not_link_is_disproved() {
    let w = World::new(3, false);
    let mut claim = w.hub_claim.clone();
    claim.chain.headers[1].0[4] ^= 1;
    let hub = claim.build();
    let (step, name) = first_failing_step(&hub.0, &hub.1).expect("invalid");
    assert_eq!(name, "hdr_c1");
    assert_eq!(step, 4, "header 2's first compression");
    let mut h = w.harness("p3-badlink", hub, w.real_chain.build());
    h.step_until(400, |h| disproof(h).is_some()).unwrap();
    h.steps(2).unwrap();
    let d = disproof(&h).unwrap();
    assert!(d.starts_with("cpred_hdr_c1"), "{d}");
    assert!(h.user.narrative().iter().any(|l| l.contains("a predicate of step 4 (hdr_c1) fails")));
    assert_eq!(h.balance(Role::User), sat(50_000 - K) + output_of(&h, |r| r == d));
    println!("{}", h.narrative());
    println!("SIZES {}", sizes(&h));
}

/// The hub's second header links but was not mined: its hash exceeds the
/// target and the `target` check step is disproved with a simple leaf.
#[test]
fn header_without_proof_of_work_is_disproved() {
    let w = World::new(3, false);
    let mut claim = w.hub_claim.clone();
    let h1 = &mut claim.chain.headers[1];
    let mut nonce = u32::from_le_bytes(h1.0[76..80].try_into().unwrap());
    loop {
        nonce = nonce.wrapping_add(1);
        h1.0[76..80].copy_from_slice(&nonce.to_le_bytes());
        if !h1.meets_target() {
            break;
        }
    }
    let hub = claim.build();
    let (step, name) = first_failing_step(&hub.0, &hub.1).expect("invalid");
    assert_eq!((step, name.as_str()), (7, "target"));
    let mut h = w.harness("p3-badpow", hub, w.real_chain.build());
    h.step_until(400, |h| disproof(h).is_some()).unwrap();
    h.steps(2).unwrap();
    let d = disproof(&h).unwrap();
    assert!(d.starts_with("simple_target"), "{d}");
    assert_eq!(h.balance(Role::User), sat(50_000 - K) + output_of(&h, |r| r == d));
    println!("{}", h.narrative());
    println!("SIZES {}", sizes(&h));
}

/// A wrong Merkle sibling: the path no longer reaches the header's root.
#[test]
fn wrong_merkle_sibling_is_disproved() {
    let w = World::new(3, false);
    let mut claim = w.hub_claim.clone();
    claim.merkle.siblings[0][3] ^= 0x40;
    let hub = claim.build();
    let (_, name) = first_failing_step(&hub.0, &hub.1).expect("invalid");
    assert_eq!(name, "merkle_root");
    let mut h = w.harness("p3-badmerkle", hub, w.real_chain.build());
    h.step_until(400, |h| disproof(h).is_some()).unwrap();
    h.steps(2).unwrap();
    let d = disproof(&h).unwrap();
    assert!(d.starts_with("simple_merkle_root"), "{d}");
    assert_eq!(h.balance(Role::User), sat(50_000 - K) + output_of(&h, |r| r == d));
    println!("{}", h.narrative());
}

/// A wrong ledger sibling: the entry's path no longer reaches the anchored root.
#[test]
fn wrong_ledger_sibling_is_disproved() {
    let w = World::new(3, false);
    let mut claim = w.hub_claim.clone();
    claim.ledger.siblings[5][0] ^= 1;
    let hub = claim.build();
    let (_, name) = first_failing_step(&hub.0, &hub.1).expect("invalid");
    assert_eq!(name, "ledger_root");
    let mut h = w.harness("p3-badledger", hub, w.real_chain.build());
    h.step_until(400, |h| disproof(h).is_some()).unwrap();
    h.steps(2).unwrap();
    let d = disproof(&h).unwrap();
    assert!(d.starts_with("simple_ledger_root"), "{d}");
    println!("{}", h.narrative());
}

/// The hub anchored in a private fork; the user refutes with the real,
/// longer chain (depth 2). The hub disputes the refutation anyway, finds
/// nothing to disprove, and is timed out: the user wins.
#[test]
fn heavier_chain_refutes_the_fork() {
    let w = World::new(3, true);
    let hub = w.hub_claim.build();
    assert_eq!(first_failing_step(&hub.0, &hub.1), None, "the fork is internally valid");
    let user = w.real_chain.build();
    assert_eq!(first_failing_step(&user.0, &user.1), None);
    let mut h = w.harness("p3-fork", hub, user);
    h.user.queue_moves(1, vec![vec![true]]);
    h.hub.faults.dispute_anyway = true;
    h.step_until(400, |h| roles(h).iter().any(|r| r == "dispute_timeout")).unwrap();
    h.steps(2).unwrap();
    let r = roles(&h);
    assert!(r.contains(&"move_2".to_string()) && r.contains(&"d2/dispute".to_string()), "{r:?}");
    assert!(h.hub.narrative().iter().any(|l| l.contains("nothing to disprove")));
    let kept = h.balance(Role::User) - output_of(&h, |r| r == "dispute_timeout");
    assert!(kept >= sat(50_000 - 3 * K) && kept <= sat(50_000 - K), "the user's own fees only: {kept}");
    println!("{}", h.narrative());
    println!("SIZES {}", sizes(&h));
}

/// A false refutation: the user's chain has a header that does not link;
/// the hub disputes and disproves it.
#[test]
fn false_refutation_is_disproved() {
    let w = World::new(3, true);
    let hub = w.hub_claim.build();
    let mut chain = w.real_chain.clone();
    chain.headers[2].0[10] ^= 0x80;
    let user = chain.build();
    assert_eq!(first_failing_step(&user.0, &user.1).map(|f| f.1), Some("hdr_c1".into()));
    let mut h = w.harness("p3-falseref", hub, user);
    h.user.queue_moves(1, vec![vec![true]]);
    h.step_until(400, |h| disproof(h).is_some()).unwrap();
    h.steps(2).unwrap();
    let d = disproof(&h).unwrap();
    assert!(d.starts_with("cpred_hdr_c1"), "{d}");
    assert!(h.hub.narrative().iter().any(|l| l.contains("disputing the claim")));
    assert_eq!(h.balance(Role::Hub), sat(50_000 - K - K) + output_of(&h, |r| r == d));
    println!("{}", h.narrative());
}
