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
}

pub fn parse_move_witness(w: &Witness, n_move: usize, n_state: usize) -> Result<MoveReveals> {
    let args = witness_args_consumption_order(w);
    ensure!(args.len() == 2 + n_move + n_state + CODE_BITS, "move witness has {} args, expected {}", args.len(), 2 + n_move + n_state + CODE_BITS);
    let mv = Reveal::from_consumption_order(&args[2..2 + n_move])?;
    let state = Reveal::from_consumption_order(&args[2 + n_move..2 + n_move + n_state])?;
    let code = Reveal::from_consumption_order(&args[2 + n_move + n_state..])?;
    Ok(MoveReveals { mv, state, code })
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
