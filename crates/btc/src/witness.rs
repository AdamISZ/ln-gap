//! Witness assembly for script-path spends: `[args..., leaf script, control block]`.
//!
//! Stack convention used throughout LN-GAP: the *last* element of `args` ends
//! up on top of the stack and is the first thing the leaf consumes.

use bitcoin::taproot::ControlBlock;
use bitcoin::{Script, Witness};

pub fn tapscript_witness(args: &[Vec<u8>], leaf: &Script, control: &ControlBlock) -> Witness {
    let mut items: Vec<Vec<u8>> = args.to_vec();
    items.push(leaf.to_bytes());
    items.push(control.serialize());
    Witness::from_slice(&items)
}

/// Incremental builder that mirrors leaf consumption order: call `push` in the
/// order the *script consumes* elements, and `build` reverses so the first
/// pushed is on top.
#[derive(Default, Clone, Debug)]
pub struct WitnessStack {
    consumed_in_order: Vec<Vec<u8>>,
}

impl WitnessStack {
    pub fn new() -> Self {
        Self::default()
    }
    /// Next element the script will consume.
    pub fn push(&mut self, item: impl Into<Vec<u8>>) -> &mut Self {
        self.consumed_in_order.push(item.into());
        self
    }
    pub fn extend<I: IntoIterator<Item = Vec<u8>>>(&mut self, items: I) -> &mut Self {
        self.consumed_in_order.extend(items);
        self
    }
    /// Witness args in wire order (bottom of stack first).
    pub fn args(&self) -> Vec<Vec<u8>> {
        self.consumed_in_order.iter().rev().cloned().collect()
    }
    pub fn build(&self, leaf: &Script, control: &ControlBlock) -> Witness {
        tapscript_witness(&self.args(), leaf, control)
    }
    /// Total byte size of the args (for size reporting).
    pub fn arg_bytes(&self) -> usize {
        self.consumed_in_order.iter().map(|v| v.len()).sum()
    }
}

/// Extract the raw witness args (everything before leaf script and control
/// block) of a script-path input, in *consumption order* (top of stack first).
/// Used by disprovers to copy a prover's revealed preimages from a confirmed tx.
pub fn witness_args_consumption_order(w: &Witness) -> Vec<Vec<u8>> {
    let n = w.len();
    if n < 2 {
        return vec![];
    }
    // last two are script and control block; args are the first n-2, reversed.
    (0..n - 2).rev().map(|i| w.nth(i).expect("index").to_vec()).collect()
}
