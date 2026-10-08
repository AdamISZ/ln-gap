//! A venue of members with seal chains (V25_POC_PLAN.md, Phase 3): members
//! receive signed choices, put their leaves in the current period's tree,
//! close each period with the tree's root, and hand out paths; faults can
//! be injected per member. Chain-agnostic: the caller funds the chains,
//! runs the ceremonies and mines the closings the venue hands back.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use anyhow::{ensure, Result};
use bitcoin::Transaction;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};

use crate::dating::{Path, PeriodTree, SignedChoice};
use crate::{Member, PresignedChain};

/// Faults a member can be told to commit.
#[derive(Clone, Debug, Default)]
pub struct Faults {
    /// Periods whose closing the member does not broadcast (its bond is
    /// then burnable, and its chain ends there).
    pub skip: BTreeSet<u32>,
    /// Hand out no paths.
    pub withhold: bool,
    /// Refuse moves of these contracts.
    pub censor: BTreeSet<u32>,
    /// Periods for which the member also signs a second, different root
    /// (and hands it out with its own paths).
    pub equivocate: BTreeSet<u32>,
}

/// One member of the venue.
pub struct VenueMember {
    pub index: usize,
    pub member: Member,
    pub chain: PresignedChain,
    pub faults: Faults,
    /// Leaves received, per period.
    inbox: BTreeMap<u32, Vec<[u8; 20]>>,
    /// The trees of closed periods (their roots are on chain).
    pub sealed: BTreeMap<u32, PeriodTree>,
    /// The second trees of equivocated periods.
    pub equivocal: BTreeMap<u32, PeriodTree>,
    /// Set once a skipped closing breaks the chain.
    pub dead: bool,
}

impl VenueMember {
    pub fn new(index: usize, member: Member, chain: PresignedChain) -> VenueMember {
        VenueMember {
            index,
            member,
            chain,
            faults: Faults::default(),
            inbox: BTreeMap::new(),
            sealed: BTreeMap::new(),
            equivocal: BTreeMap::new(),
            dead: false,
        }
    }

    /// The period a move received with the chain at `tip` goes into: the
    /// next closing to be mined, i.e. the first `k` with `H_k > tip`.
    pub fn period_for(&self, tip: u32) -> Option<u32> {
        let s = &self.chain.spec;
        (1..=s.periods).find(|&k| s.height(k) > tip)
    }

    /// The closing height of period k.
    pub fn closing_height(&self, k: u32) -> u32 {
        self.chain.spec.height(k)
    }

    fn receive(&mut self, tip: u32, sc: &SignedChoice) -> Option<u32> {
        if self.dead || self.faults.censor.contains(&sc.choice.contract) {
            return None;
        }
        let k = self.period_for(tip)?;
        self.inbox.entry(k).or_default().push(sc.choice.leaf());
        Some(k)
    }

    /// The closing to broadcast with the chain at `tip` (to be mined in
    /// block `tip + 1`), if one is due.
    fn closing_due(&mut self, tip: u32) -> Result<Option<Transaction>> {
        if self.dead {
            return Ok(None);
        }
        let Some(k) = (1..=self.chain.spec.periods).find(|&k| self.closing_height(k) == tip + 1) else {
            return Ok(None);
        };
        if self.faults.skip.contains(&k) {
            self.dead = true;
            return Ok(None);
        }
        let leaves = self.inbox.remove(&k).unwrap_or_default();
        let tx = if leaves.is_empty() {
            self.chain.close_empty(&self.member, k)?
        } else {
            let tree = PeriodTree::new(leaves);
            let tx = self.chain.close(&self.member, k, &tree.root())?;
            if self.faults.equivocate.contains(&k) {
                // a second root: the same leaves, one extra leaf appended
                let mut other = tree.leaves().to_vec();
                other.push([0xEE; 20]);
                self.equivocal.insert(k, PeriodTree::new(other));
            }
            self.sealed.insert(k, tree);
            tx
        };
        Ok(Some(tx))
    }

    /// The path of `leaf` in the member's sealed tree for period k, with
    /// the root it leads to (`None` if withheld or absent).
    pub fn path(&self, k: u32, leaf: [u8; 20]) -> Option<(Path, [u8; 20])> {
        if self.faults.withhold {
            return None;
        }
        let tree = self.sealed.get(&k)?;
        Some((tree.path_of(leaf)?, tree.root()))
    }

    /// For an equivocated period: the second root's signature (the
    /// slashable pair's other half).
    pub fn second_root(&self, k: u32) -> Result<Option<([u8; 20], WotsSig)>> {
        let Some(t) = self.equivocal.get(&k) else { return Ok(None) };
        let root = t.root();
        Ok(Some((root, self.member.sign_root(k, &root)?)))
    }
}

/// The venue: its members and the contracts' registered choice keys.
pub struct Venue {
    pub members: Vec<VenueMember>,
    keys: HashMap<(u32, u16), WotsPublic>,
}

impl Venue {
    pub fn new(members: Vec<VenueMember>) -> Venue {
        Venue { members, keys: HashMap::new() }
    }

    /// Register a contract depth's choice key (members check authorship).
    pub fn register(&mut self, contract: u32, depth: u16, key: WotsPublic) {
        self.keys.insert((contract, depth), key);
    }

    /// The mover sends its signed choice to every member, with the chain
    /// at `tip`. Returns, per member, the period it went into (`None`:
    /// refused).
    pub fn submit(&mut self, tip: u32, sc: &SignedChoice) -> Result<Vec<Option<u32>>> {
        let key = self.keys.get(&(sc.choice.contract, sc.choice.depth));
        ensure!(key.is_some(), "contract {} depth {} is not registered", sc.choice.contract, sc.choice.depth);
        sc.verify(key.unwrap())?;
        Ok(self.members.iter_mut().map(|m| m.receive(tip, sc)).collect())
    }

    /// Every closing due with the chain at `tip`, to be mined together in
    /// block `tip + 1`.
    pub fn closings_due(&mut self, tip: u32) -> Result<Vec<(usize, Transaction)>> {
        let mut out = Vec::new();
        for m in &mut self.members {
            if let Some(tx) = m.closing_due(tip)? {
                out.push((m.index, tx));
            }
        }
        Ok(out)
    }

    /// The members (and their periods) whose closings fall in a move's
    /// window: after the move was sent at `sent_tip`, up to the deadline
    /// height `deadline`.
    pub fn window(&self, sent_tip: u32, deadline: u32) -> Vec<(usize, u32)> {
        let mut out = Vec::new();
        for m in &self.members {
            for k in 1..=m.chain.spec.periods {
                let h = m.closing_height(k);
                if h > sent_tip && h <= deadline {
                    out.push((m.index, k));
                }
            }
        }
        out.sort_by_key(|(i, k)| (self.members[*i].closing_height(*k), *i));
        out
    }
}

/// The root a closing carries in its witness (`None` for an empty
/// closing): the Winternitz signature's 40 message digits, read back.
pub fn root_of_closing(tx: &Transaction) -> Option<[u8; 20]> {
    let w = &tx.input[0].witness;
    let total = crate::root_params().total_digits() as usize;
    // wire: (hash, digit) per digit, then the member's and the ceremony's
    // signatures, then the leaf script and the control block
    if w.len() != 2 * total + 4 {
        return None;
    }
    let digit = |i: usize| -> u8 { w.nth(2 * i + 1).and_then(|d| d.first().copied()).unwrap_or(0) };
    let mut root = [0u8; 20];
    for (j, b) in root.iter_mut().enumerate() {
        *b = (digit(2 * j) << 4) | digit(2 * j + 1);
    }
    Some(root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dating::{Choice, ChoiceKey};
    use crate::{ceremony, SealSpec};
    use bitcoin::{Amount, OutPoint};

    fn member(i: usize, start: u32) -> VenueMember {
        let spec = SealSpec {
            value: Amount::from_sat(300_000),
            start,
            period: 3,
            periods: 4,
            grace: 2,
            release_delay: 5,
            fanout_depth: 2,
            leaf_value: Amount::from_sat(330),
            split_fee: Amount::from_sat(400),
            anchor_value: Amount::from_sat(240),
            closing_fee: Amount::from_sat(3_000),
        };
        let m = Member::new([i as u8 + 1; 32], &spec);
        let funding = OutPoint { txid: bitcoin::Txid::from_byte_array([i as u8; 32]), vout: 0 };
        let chain = ceremony(&spec, &m.public(), funding, &[0xCE; 32]).unwrap();
        VenueMember::new(i, m, chain)
    }

    use bitcoin::hashes::Hash;

    #[test]
    fn roots_are_read_back_from_closings_and_paths_verify() {
        let mut v = Venue::new((0..3).map(|i| member(i, 100 + i as u32)).collect());
        let key = ChoiceKey::new([9; 32], 1);
        v.register(1, 1, key.public());
        let sc = SignedChoice { choice: Choice { contract: 1, depth: 1, value: vec![4] }, sig: key.sign(&[4]).unwrap() };
        let periods = v.submit(98, &sc).unwrap();
        assert_eq!(periods, vec![Some(1), Some(1), Some(1)]);
        for tip in 98..104 {
            for (i, tx) in v.closings_due(tip).unwrap() {
                let m = &v.members[i];
                let k = (1..=4).find(|&k| m.closing_height(k) == tip + 1).unwrap();
                match root_of_closing(&tx) {
                    Some(root) => {
                        let (path, r) = m.path(k, sc.choice.leaf()).expect("the move is in this period");
                        assert_eq!((r, path.root_from(sc.choice.leaf())), (root, root));
                    }
                    None => assert!(k > 1, "period 1 had the move"),
                }
            }
        }
        // closings at 100, 103, ... (member 0), 101, 104, ... (1), 102, 105, ... (2)
        assert_eq!(v.window(98, 102), vec![(0, 1), (1, 1), (2, 1)]);
        assert_eq!(v.window(100, 103), vec![(1, 1), (2, 1), (0, 2)]);
    }
}
