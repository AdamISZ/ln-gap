//! Reading a counterparty's on-chain Move: which leaf, what it revealed.

use anyhow::{ensure, Result};
use bitcoin::Witness;
use lngap_btc::witness::witness_args_consumption_order;
use lngap_lamport::{bits_to_uint, Reveal};

use crate::instance::DepthKeys;
use crate::leaves::Claim;
use crate::{Program, CODE_BITS};

/// The reveals carried by a Move witness (after the two signatures).
#[derive(Clone, Debug)]
pub struct MoveReveals {
    pub mv: Reveal,
    pub state: Reveal,
    pub code: Reveal,
    /// Extras, in the order the contract's `move_extras` lists them.
    pub extras: Vec<Reveal>,
    /// The claim's end-state signature, if the program has a claim.
    pub claim_end: Option<lngap_lamport::winternitz::WotsSig>,
}

pub fn parse_move_witness(w: &Witness, n_move: usize, n_state: usize, extra_bits: &[usize], claim_end: Option<lngap_lamport::winternitz::WotsParams>) -> Result<MoveReveals> {
    let args = witness_args_consumption_order(w);
    let n_extra: usize = extra_bits.iter().sum();
    let n_end = claim_end.map(|p| 2 * p.total_digits() as usize).unwrap_or(0);
    let expected = 2 + n_move + n_state + CODE_BITS + n_extra + n_end;
    ensure!(args.len() == expected, "move witness has {} args, expected {expected}", args.len());
    let mut at = 2;
    let mut take = |n: usize| -> Result<Reveal> {
        let r = Reveal::from_consumption_order(&args[at..at + n]);
        at += n;
        r
    };
    let mv = take(n_move)?;
    let state = take(n_state)?;
    let code = take(CODE_BITS)?;
    let mut extras = Vec::new();
    for &n in extra_bits {
        extras.push(take(n)?);
    }
    let claim_end = match claim_end {
        Some(p) => Some(lngap_lamport::winternitz::WotsSig::from_consumption_order(p, &args[at..])?),
        None => None,
    };
    Ok(MoveReveals { mv, state, code, extras, claim_end })
}

/// Decode reveals against the prover's keys into a [`Claim`].
pub fn decode_claim(program: &dyn Program, keys: &DepthKeys, prior: Vec<bool>, r: &MoveReveals) -> Result<Claim> {
    let _ = program;
    let mv = keys.mv.decode_bits(&r.mv)?;
    let new = keys.state.decode_bits(&r.state)?;
    let code = bits_to_uint(&keys.code.decode_bits(&r.code)?) as u8;
    Ok(Claim { prior, mv, new, code, mover: keys.prover })
}

/// Native verdict on a claim: `Ok(())` if consistent with the program, else
/// which check fails.
pub fn check_claim(program: &dyn Program, c: &Claim) -> Result<(), String> {
    let expected = program.transition_bits(&c.prior, &c.mv, c.mover).map_err(|e| format!("invalid move: {e}"))?;
    if expected != c.new {
        return Err("claimed state does not match the transition".into());
    }
    let r = program.resolution_bits(&c.new).map_err(|e| e.to_string())?;
    if r.code != c.code {
        return Err(format!("claimed outcome code {} but R(s') = {} ({})", c.code, r.code, r.name));
    }
    Ok(())
}
