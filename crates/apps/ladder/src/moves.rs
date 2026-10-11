//! The moves' messages, built from BitVMX's search and read back.

use anyhow::{anyhow, ensure, Result};
use lngap_zk::dispute::Searched;
use lngap_zk::game::{blocks, Record};
use lngap_zk::FinalStep;

use crate::{Kind, Schedule, CLAIM_BYTES, C_LAST_HASH, C_LAST_STEP, F_NEXT_HASH, F_STEP_HASH, RECORD_BYTES};

fn h20(s: &str) -> Result<[u8; 20]> {
    hex::decode(s)?.try_into().map_err(|_| anyhow!("a step hash is 20 bytes: {s}"))
}

/// Move 1: the claim (last step, its hash) and round 1's hashes.
pub fn claim_message(last_step: u64, last_hash: &[u8; 20], round1: &[[u8; 20]]) -> Vec<u8> {
    let mut m = last_step.to_be_bytes().to_vec();
    m.extend_from_slice(last_hash);
    for h in round1 {
        m.extend_from_slice(h);
    }
    m
}

/// A round's hashes.
pub fn hashes_message(hashes: &[[u8; 20]]) -> Vec<u8> {
    hashes.iter().flatten().copied().collect()
}

/// The disputed step: the record, the hash after the agreed step, the
/// hash after the next; under a jump list, also the long jump's hash the
/// disputed step commits to (`jump`) and its number.
pub fn final_message(f: &FinalStep, jump: Option<&[u8; 20]>) -> Vec<u8> {
    let (_, _, record) = blocks(f);
    let mut m = record.to_bytes().to_vec();
    m.extend_from_slice(&f.prev_hash);
    m.extend_from_slice(&f.hash);
    if let Some(j) = jump {
        m.extend_from_slice(j);
        m.extend_from_slice(&(f.agreed_step + 1).to_be_bytes());
    }
    m
}

/// Every move's message, depth 1 first, from a search BitVMX ran; under a
/// jump list, `jump` is the prover's hash at the disputed step's long jump.
pub fn from_search(s: &Schedule, searched: &Searched, jump: Option<&[u8; 20]>) -> Result<Vec<Vec<u8>>> {
    ensure!(s.jump.is_some() == jump.is_some(), "a jump list's final move carries the long jump's hash");
    let r = s.rounds() as usize;
    ensure!(searched.rounds.len() == r, "the search ran {} rounds, the schedule has {r}", searched.rounds.len());
    let hashes = |q: usize| -> Result<Vec<[u8; 20]>> {
        let v: Vec<[u8; 20]> = searched.rounds[q].0.iter().map(|x| h20(x)).collect::<Result<_>>()?;
        ensure!(v.len() == s.hashes(q as u32 + 1), "round {} posted {} hashes", q + 1, v.len());
        Ok(v)
    };
    let (_, last_step, last_hash) = &searched.claim;
    let mut out = vec![claim_message(*last_step, &h20(last_hash)?, &hashes(0)?)];
    for q in 0..r {
        let c = searched.rounds[q].1;
        ensure!(c < s.segments(q as u32 + 1), "round {}: choice {c}", q + 1);
        out.push(vec![c as u8]);
        if q + 1 < r {
            out.push(hashes_message(&hashes(q + 1)?));
        }
    }
    out.push(final_message(&searched.final_step, jump));
    for (i, m) in out.iter().enumerate() {
        ensure!(m.len() == s.bytes(i as u32 + 1), "move {} is {} bytes, not {}", i + 1, m.len(), s.bytes(i as u32 + 1));
    }
    Ok(out)
}

/// Move `depth`'s fields, each to be signed under its own key.
pub fn fields<'m>(s: &Schedule, depth: u32, msg: &'m [u8]) -> Vec<&'m [u8]> {
    s.fields(depth).into_iter().map(|(o, l)| &msg[o..o + l]).collect()
}

/// The moves read back, for the mirrors and the parties' play.
pub struct View<'a> {
    pub s: &'a Schedule,
    pub msgs: &'a [Vec<u8>],
}

impl View<'_> {
    pub fn claim(&self) -> (u64, [u8; 20]) {
        let m = &self.msgs[0];
        (u64::from_be_bytes(m[C_LAST_STEP..C_LAST_STEP + 8].try_into().unwrap()), m[C_LAST_HASH..C_LAST_HASH + 20].try_into().unwrap())
    }
    /// Round `r`'s hash `i`.
    pub fn hash(&self, r: u32, i: usize) -> [u8; 20] {
        let (d, off) = self.s.hash_at(r, i);
        self.msgs[(d - 1) as usize][off..off + 20].try_into().unwrap()
    }
    /// The hub's choices so far.
    pub fn choices(&self) -> Vec<u32> {
        (1..=self.s.rounds()).take_while(|q| self.msgs.len() >= 2 * *q as usize).map(|q| u32::from(self.msgs[2 * q as usize - 1][0])).collect()
    }
    pub fn record(&self) -> Record {
        let m = &self.msgs[self.s.depths() as usize - 1];
        Record::from_bytes(m[..RECORD_BYTES].try_into().unwrap())
    }
    pub fn step_hash(&self) -> [u8; 20] {
        let m = &self.msgs[self.s.depths() as usize - 1];
        m[F_STEP_HASH..F_STEP_HASH + 20].try_into().unwrap()
    }
    pub fn next_hash(&self) -> [u8; 20] {
        let m = &self.msgs[self.s.depths() as usize - 1];
        m[F_NEXT_HASH..F_NEXT_HASH + 20].try_into().unwrap()
    }
    pub fn kind(&self, depth: u32) -> Kind {
        self.s.kind(depth)
    }
    /// Under a jump list: the long jump's hash the final move commits to.
    pub fn jump_hash(&self) -> [u8; 20] {
        let m = &self.msgs[self.s.depths() as usize - 1];
        m[crate::F_JUMP_HASH..crate::F_JUMP_HASH + 20].try_into().unwrap()
    }
    /// Under a jump list: the disputed step's number, as signed.
    pub fn succ(&self) -> u32 {
        let m = &self.msgs[self.s.depths() as usize - 1];
        u32::from_be_bytes(m[crate::F_SUCC..crate::F_SUCC + 4].try_into().unwrap())
    }
}

#[allow(dead_code)]
const _: usize = CLAIM_BYTES;
