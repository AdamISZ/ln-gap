//! Transaction building and timelock hygiene.

use anyhow::{bail, ensure, Result};
use bitcoin::{absolute, transaction::Version, Amount, OutPoint, Sequence, Transaction, TxIn, TxOut};

/// The fixed fee every pre-signed transaction in the PoC pays.
pub const FIXED_FEE: Amount = Amount::from_sat(1_000);

/// Absolute locks from here on are unix times, below it heights.
pub const LOCK_TIME_THRESHOLD: u32 = 500_000_000;

/// Timelock requirements a leaf imposes on the transaction that spends through it.
/// Deadlines are absolute (`cltv`), challenge windows are relative (`csv`).
/// An absolute lock below [`LOCK_TIME_THRESHOLD`] is a height, from it a
/// unix time read against median-time-past, as consensus reads nLockTime.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Timelock {
    pub cltv: Option<u32>,
    pub csv: Option<u16>,
}

impl Timelock {
    pub const NONE: Timelock = Timelock { cltv: None, csv: None };
    pub fn cltv(h: u32) -> Timelock {
        Timelock { cltv: Some(h), csv: None }
    }
    pub fn csv(n: u16) -> Timelock {
        Timelock { cltv: None, csv: Some(n) }
    }
    pub fn both(h: u32, n: u16) -> Timelock {
        Timelock { cltv: Some(h), csv: Some(n) }
    }
    /// The `nSequence` an input spending this leaf must carry.
    pub fn sequence(&self) -> Sequence {
        match self.csv {
            Some(n) => Sequence::from_height(n),
            // CLTV requires nSequence != 0xffffffff; ENABLE_RBF_NO_LOCKTIME (0xfffffffd) satisfies
            // that and does not enable relative locktime.
            None => Sequence::ENABLE_RBF_NO_LOCKTIME,
        }
    }
    /// The `nLockTime` a transaction spending this leaf must carry.
    pub fn locktime(&self) -> absolute::LockTime {
        match self.cltv {
            Some(v) => absolute::LockTime::from_consensus(v),
            None => absolute::LockTime::ZERO,
        }
    }
}

/// Build a version-2 transaction with explicit sequences and locktime.
pub fn build_tx(
    inputs: &[(OutPoint, Sequence)],
    outputs: Vec<TxOut>,
    lock_time: absolute::LockTime,
) -> Transaction {
    Transaction {
        version: Version::TWO,
        lock_time,
        input: inputs
            .iter()
            .map(|(op, seq)| TxIn {
                previous_output: *op,
                script_sig: Default::default(),
                sequence: *seq,
                witness: Default::default(),
            })
            .collect(),
        output: outputs,
    }
}

/// Build a one-input transaction whose fields satisfy `leaf_timelock`.
pub fn build_spend(prev: OutPoint, leaf_timelock: &Timelock, outputs: Vec<TxOut>) -> Transaction {
    build_tx(&[(prev, leaf_timelock.sequence())], outputs, leaf_timelock.locktime())
}

/// Assert that a transaction's fields satisfy what a leaf will check. This is
/// the "common source of silent failures" guard from the plan: a CLTV leaf
/// whose spending tx forgot nLockTime fails only at broadcast time otherwise.
pub fn check_timelock(tx: &Transaction, input: usize, req: &Timelock) -> Result<()> {
    let txin = tx.input.get(input).ok_or_else(|| anyhow::anyhow!("no input {input}"))?;
    if let Some(h) = req.cltv {
        let have = tx.lock_time.to_consensus_u32();
        match (tx.lock_time, h >= LOCK_TIME_THRESHOLD) {
            (absolute::LockTime::Blocks(_), false) | (absolute::LockTime::Seconds(_), true) => {
                ensure!(have >= h, "nLockTime {have} < leaf CLTV {h}")
            }
            (absolute::LockTime::Blocks(_), true) => bail!("leaf CLTV is time-based; tx uses a height"),
            (absolute::LockTime::Seconds(_), false) => bail!("leaf CLTV is height-based; tx uses time"),
        }
        ensure!(txin.sequence != Sequence::MAX, "CLTV needs nSequence != 0xffffffff");
    }
    match req.csv {
        Some(n) => {
            ensure!(
                txin.sequence.is_height_locked(),
                "leaf CSV {n} but nSequence {:?} is not a height lock",
                txin.sequence
            );
            let have = txin.sequence.to_relative_lock_time().expect("checked").to_consensus_u32();
            ensure!(have >= u32::from(n), "nSequence height {have} < leaf CSV {n}");
        }
        None => ensure!(
            !txin.sequence.is_relative_lock_time(),
            "tx sets a relative locktime but the leaf has no CSV; probably a wrong leaf"
        ),
    }
    Ok(())
}

/// Sum of input values minus sum of output values.
pub fn fee(tx: &Transaction, prevouts: &[TxOut]) -> Amount {
    let in_sum: u64 = prevouts.iter().map(|o| o.value.to_sat()).sum();
    let out_sum: u64 = tx.output.iter().map(|o| o.value.to_sat()).sum();
    Amount::from_sat(in_sum - out_sum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::ScriptBuf;

    fn out() -> Vec<TxOut> {
        vec![TxOut { value: Amount::from_sat(1), script_pubkey: ScriptBuf::new() }]
    }

    #[test]
    fn spend_matches_leaf_requirements() {
        for tl in [Timelock::NONE, Timelock::cltv(300), Timelock::csv(6), Timelock::both(300, 6)] {
            let tx = build_spend(OutPoint::null(), &tl, out());
            check_timelock(&tx, 0, &tl).unwrap();
        }
        let tx = build_spend(OutPoint::null(), &Timelock::NONE, out());
        assert!(check_timelock(&tx, 0, &Timelock::cltv(300)).is_err());
        assert!(check_timelock(&tx, 0, &Timelock::csv(6)).is_err());
        let tx = build_spend(OutPoint::null(), &Timelock::csv(6), out());
        assert!(check_timelock(&tx, 0, &Timelock::NONE).is_err());
        assert!(check_timelock(&tx, 0, &Timelock::csv(7)).is_err());
    }

    /// A time lock (>= 500,000,000) is carried as a time nLockTime; heights
    /// and times never satisfy each other.
    #[test]
    fn time_locks() {
        let t = 1_800_000_000;
        for tl in [Timelock::cltv(t), Timelock::both(t, 6)] {
            let tx = build_spend(OutPoint::null(), &tl, out());
            assert!(matches!(tx.lock_time, absolute::LockTime::Seconds(_)));
            check_timelock(&tx, 0, &tl).unwrap();
        }
        let early = build_spend(OutPoint::null(), &Timelock::cltv(t - 1), out());
        assert!(check_timelock(&early, 0, &Timelock::cltv(t)).is_err());
        let height = build_spend(OutPoint::null(), &Timelock::cltv(300), out());
        assert!(check_timelock(&height, 0, &Timelock::cltv(t)).unwrap_err().to_string().contains("time-based"));
        let time = build_spend(OutPoint::null(), &Timelock::cltv(t), out());
        assert!(check_timelock(&time, 0, &Timelock::cltv(300)).unwrap_err().to_string().contains("height-based"));
    }
}
