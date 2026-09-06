//! Taproot output = NUMS internal key + a set of named leaves.

use anyhow::{anyhow, ensure, Result};
use bitcoin::key::{TweakedPublicKey, XOnlyPublicKey};
use bitcoin::secp256k1::SECP256K1;
use bitcoin::taproot::{ControlBlock, LeafVersion, TapLeafHash, TaprootBuilder, TaprootSpendInfo};
use bitcoin::{Address, Network, ScriptBuf};

use crate::keys::nums_point;
use crate::tx::Timelock;

/// A named tapscript leaf together with the timelock it imposes on spenders.
#[derive(Clone, Debug)]
pub struct Leaf {
    pub name: String,
    pub script: ScriptBuf,
    pub timelock: Timelock,
}

impl Leaf {
    pub fn new(name: impl Into<String>, script: ScriptBuf, timelock: Timelock) -> Leaf {
        Leaf { name: name.into(), script, timelock }
    }
    pub fn leaf_hash(&self) -> TapLeafHash {
        TapLeafHash::from_script(&self.script, LeafVersion::TapScript)
    }
}

/// A finalized taproot tree: leaves plus everything needed to spend them.
#[derive(Clone, Debug)]
pub struct TapTree {
    leaves: Vec<Leaf>,
    internal_key: XOnlyPublicKey,
    info: TaprootSpendInfo,
}

impl TapTree {
    /// Tree with an unspendable (NUMS) key path; all spends are script paths.
    pub fn new(leaves: Vec<Leaf>) -> Result<TapTree> {
        TapTree::with_internal_key(nums_point(), leaves)
    }

    pub fn with_internal_key(internal_key: XOnlyPublicKey, leaves: Vec<Leaf>) -> Result<TapTree> {
        ensure!(!leaves.is_empty(), "taptree needs at least one leaf");
        for (i, a) in leaves.iter().enumerate() {
            for b in &leaves[i + 1..] {
                ensure!(a.name != b.name, "duplicate leaf name {}", a.name);
                ensure!(a.script != b.script, "leaves {} and {} have identical scripts", a.name, b.name);
            }
        }
        let builder = TaprootBuilder::with_huffman_tree(leaves.iter().map(|l| (1u32, l.script.clone())))
            .map_err(|e| anyhow!("taproot builder: {e}"))?;
        let info = builder
            .finalize(SECP256K1, internal_key)
            .map_err(|_| anyhow!("taproot tree not finalizable"))?;
        Ok(TapTree { leaves, internal_key, info })
    }

    pub fn leaves(&self) -> &[Leaf] {
        &self.leaves
    }
    pub fn internal_key(&self) -> XOnlyPublicKey {
        self.internal_key
    }
    pub fn output_key(&self) -> TweakedPublicKey {
        self.info.output_key()
    }
    pub fn script_pubkey(&self) -> ScriptBuf {
        ScriptBuf::new_p2tr_tweaked(self.output_key())
    }
    pub fn address(&self, network: Network) -> Address {
        Address::p2tr_tweaked(self.output_key(), network)
    }
    pub fn leaf(&self, name: &str) -> Result<&Leaf> {
        self.leaves.iter().find(|l| l.name == name).ok_or_else(|| anyhow!("no leaf named {name}"))
    }
    pub fn control_block(&self, name: &str) -> Result<ControlBlock> {
        let leaf = self.leaf(name)?;
        self.info
            .control_block(&(leaf.script.clone(), LeafVersion::TapScript))
            .ok_or_else(|| anyhow!("no control block for leaf {name}"))
    }
    /// Sizes for SCRIPTS.md: (script bytes, control block bytes) per leaf.
    pub fn sizes(&self) -> Vec<(String, usize, usize)> {
        self.leaves
            .iter()
            .map(|l| {
                let cb = self.control_block(&l.name).expect("leaf exists").serialize().len();
                (l.name.clone(), l.script.len(), cb)
            })
            .collect()
    }
}
