//! Chess played on the fact chain, settled in a channel with the stall
//! graph (docs/DECISIONS.md D28; docs/planning/CHESS_ON_FACTCHAIN.md).
//!
//! Every move is a fact-chain entry in its own slot: the 8-byte content
//! (game, depth, mover, move), the 40-byte state after the move
//! ([`ChessState::to_e`]: the position's 36 bytes, then the move's from,
//! to and promotion, then the depth), and the mover's 336 Lamport
//! preimages over the state and move bits. The header's head carries the
//! content and the state, so the stall claim ([`lngap_factchain::stall`],
//! chess [`Layout`]) binds a whole position per slot.
//!
//! On Bitcoin the Move leaf reveals only the outcome code and the claim's
//! WOTS end state (`MoveExtras::wots_only`); the two positions live in the
//! end state's `E` and `E2` registers, and the disprove leaves are
//! [`lngap_chess::leaf`]'s challenge kinds reading them from there, the
//! challenger supplying the exhibit (a square, a ray index, an attacker).
//! There are twelve: every kind but the move number, which the venue
//! state does not carry.
//!
//! Not here: the stalemate claim (a stalemated party has no move and, for
//! the PoC, loses by stall), and the 50-move rule and repetition
//! (cooperative).

use anyhow::{anyhow, ensure, Result};
use bitcoin::script::Builder;
use lngap_chess::certificate::find_kind;
use lngap_chess::leaf::{exhibit_values, leaf_over_registers, Kind, Registers};
use lngap_chess::{apply, terminal, Colour, Move, PieceType, Position, Square, Terminal};
use lngap_contract::claim::{words_bytes, words_from_bytes, ClaimData, ClaimSpec};
use lngap_contract::instance::DepthKeys;
use lngap_contract::leaves::Field;
use lngap_contract::prelude::*;
use lngap_contract::{Program, ProgramRegistry};
use lngap_factchain::slot::SlotEntry;
use lngap_factchain::sig::{levels_for, Place, SigExhibit};
use lngap_factchain::stall::{Layout, StallClaim};
use lngap_lamport::winternitz::WotsExt;
use lngap_n4bit::{hash_claim, Digest};
use lngap_names::ServedData;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// Bytes of a state as the venue carries it.
pub const STATE_BYTES: usize = 40;
pub const STATE_BITS: usize = 8 * STATE_BYTES;
pub const MOVE_BITS: usize = 16;
/// Bits the mover signs: the state, then the move.
pub const SIGNED_BITS: usize = STATE_BITS + MOVE_BITS;
/// Bytes of an entry: the content, the state, one preimage per signed bit.
pub const ENTRY_BYTES: usize = 8 + STATE_BYTES + SIGNED_BITS * 20;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChessFcParams {
    pub game_id: u16,
    pub checkpoint: [u8; 20],
    /// Header slots a claim covers: the game must end before slot `w_max`.
    pub w_max: usize,
}

/// A state on the venue: the position after a move, the move, and the
/// depth (the slot the move sits in). The initial state has depth 0 and a
/// null move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChessState {
    pub pos: Position,
    pub mv: Move,
    pub depth: u8,
}

impl ChessState {
    pub fn initial() -> ChessState {
        let mut pos = Position::start();
        pos.fullmove = 0;
        ChessState { pos, mv: Move::new(Square::new(0).unwrap(), Square::new(0).unwrap()), depth: 0 }
    }
    /// The 40 bytes: the position (its move number zero, its last four
    /// bytes replaced), then from, to, promotion code << 4, depth.
    pub fn to_e(&self) -> [u8; STATE_BYTES] {
        let mut b = self.pos.to_bytes();
        b[36] = self.mv.from.u8();
        b[37] = self.mv.to.u8();
        b[38] = self.mv.promotion.map_or(0, |p| p.code()) << 4;
        b[39] = self.depth;
        b
    }
    pub fn from_e(e: &[u8; STATE_BYTES]) -> Result<ChessState> {
        let mut b = *e;
        let (from, to, promo, depth) = (b[36], b[37], b[38] >> 4, b[39]);
        ensure!(b[38] & 15 == 0, "state byte 38 low nibble");
        b[36..40].copy_from_slice(&[0; 4]);
        let pos = Position::from_bytes(&b).map_err(|e| anyhow!("{e}"))?;
        let from = Square::new(from).ok_or_else(|| anyhow!("from square {from}"))?;
        let to = Square::new(to).ok_or_else(|| anyhow!("to square {to}"))?;
        let promotion = match promo {
            0 => None,
            c => Some(PieceType::from_code(c).filter(|p| p.is_promotion_piece()).ok_or_else(|| anyhow!("promotion code {c}"))?),
        };
        Ok(ChessState { pos, mv: Move { from, to, promotion }, depth })
    }
    pub fn to_bits(&self) -> Vec<bool> {
        bytes_to_bits(&self.to_e())
    }
    pub fn from_bits(bits: &[bool]) -> Result<ChessState> {
        ensure!(bits.len() == STATE_BITS, "a chess state is {STATE_BITS} bits");
        let bytes = bits_to_bytes(bits);
        Self::from_e(bytes.as_slice().try_into().unwrap())
    }
}

/// Bit `i` of byte `k` is bit `8k + i` (least significant first).
pub fn bytes_to_bits(b: &[u8]) -> Vec<bool> {
    b.iter().flat_map(|&x| (0..8).map(move |i| (x >> i) & 1 == 1)).collect()
}
pub fn bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    bits.chunks(8).map(|c| c.iter().enumerate().fold(0u8, |acc, (i, &b)| acc | (u8::from(b) << i))).collect()
}

/// A published move: the content, the state, the mover's preimages for
/// the state and move bits (`sigs[i]` opens bit `i` of [`ChessEntry::signed_bits`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChessEntry {
    pub game_id: u16,
    pub depth: u8,
    pub mover: u8,
    pub state: ChessState,
    pub sigs: Vec<[u8; 20]>,
}

impl ChessEntry {
    pub fn word1(mv: Move) -> u32 {
        u32::from(mv.to_u16()) << 16
    }
    pub fn signed_bits(state: &ChessState) -> Vec<bool> {
        let mut v = state.to_bits();
        v.extend(uint_to_bits(u32::from(state.mv.to_u16()), MOVE_BITS));
        v
    }
    pub fn encode(&self) -> Vec<u8> {
        // the sig count is the signing scheme's (per-bit Lamport for the
        // PoW graphs; D43's Winternitz reveals for the PoS graph) — the
        // wire is just the content then the 20-byte elements
        let mut v = Vec::with_capacity(48 + self.sigs.len() * 20);
        v.extend_from_slice(&SlotEntry::word0(self.game_id, self.depth, self.mover).to_be_bytes());
        v.extend_from_slice(&Self::word1(self.state.mv).to_be_bytes());
        v.extend_from_slice(&self.state.to_e());
        for s in &self.sigs {
            v.extend_from_slice(s);
        }
        v
    }
    pub fn decode(b: &[u8]) -> Result<ChessEntry> {
        ensure!(b.len() >= 48 && (b.len() - 48).is_multiple_of(20), "a chess entry is 48 content bytes plus 20-byte sig elements, got {}", b.len());
        let w0 = u32::from_be_bytes(b[0..4].try_into().unwrap());
        let w1 = u32::from_be_bytes(b[4..8].try_into().unwrap());
        let state = ChessState::from_e(b[8..48].try_into().unwrap())?;
        ensure!(u32::from(state.mv.to_u16()) << 16 == w1, "content move disagrees with the state's");
        ensure!(state.depth == ((w0 >> 8) & 0xff) as u8, "content depth disagrees with the state's");
        let sigs = b[48..].chunks(20).map(|c| c.try_into().unwrap()).collect();
        Ok(ChessEntry { game_id: (w0 >> 16) as u16, depth: ((w0 >> 8) & 0xff) as u8, mover: (w0 & 0xff) as u8, state, sigs })
    }
    /// Do the preimages open the signed bits under these commitments?
    pub fn check_sigs(&self, commits: &[[Digest; 2]]) -> bool {
        let bits = Self::signed_bits(&self.state);
        commits.len() == SIGNED_BITS && self.sigs.len() == SIGNED_BITS && bits.iter().enumerate().all(|(i, &b)| hash_claim(&self.sigs[i]) == commits[i][usize::from(b)])
    }
}

#[derive(Debug)]
pub struct ChessFc {
    pub params: ChessFcParams,
    name: String,
    store: ServedData,
}

/// The register layout of the stall claim as [`lngap_chess::leaf`] reads it.
pub const REGISTERS: Registers = Registers { n_nibbles: 240, e_off: 80, e2_off: 160 };

impl ChessFc {
    pub const PREFIX: &'static str = "chess-fc";
    pub fn new(params: ChessFcParams, store: ServedData) -> ChessFc {
        let name = format!("{}:{}", Self::PREFIX, serde_json::to_string(&params).expect("serializable"));
        ChessFc { params, name, store }
    }
    pub fn from_str(params: &str, store: ServedData) -> Result<ChessFc> {
        Ok(ChessFc::new(serde_json::from_str(params)?, store))
    }
    pub fn stall_key(game_id: u16, role: Role) -> String {
        format!("chess{game_id}/stall/{}", role.name())
    }
    pub fn lie_key(game_id: u16, role: Role) -> String {
        format!("chess{game_id}/lie/{}", role.name())
    }
    pub fn sig_key(game_id: u16, role: Role) -> String {
        format!("chess{game_id}/sig/{}", role.name())
    }
    /// The store key of `role`'s per-depth venue commitment tree roots.
    pub fn roots_key(game_id: u16, role: Role) -> String {
        format!("chess{game_id}/roots/{}", role.name())
    }
    /// Serve `role`'s commitment tree roots (index `d`; `None` where `role`
    /// does not move), which the counterparty's signature exhibit pins.
    pub fn put_roots(store: &ServedData, game_id: u16, role: Role, roots: &[Option<[u8; 20]>]) {
        store.put(&Self::roots_key(game_id, role), roots.iter().map(|r| words_from_bytes(&r.unwrap_or([0u8; 20]))).collect());
    }
    fn roots_of(&self, role: Role) -> Option<Vec<Option<[u8; 20]>>> {
        let data = self.store.get(&Self::roots_key(self.params.game_id, role))?;
        Some(data.iter().map(|w| { let b = words_bytes(w); (b.iter().any(|x| *x != 0)).then(|| b.as_slice().try_into().unwrap()) }).collect())
    }
    /// Where signed bit `i` sits in the entry's head: the state's bytes
    /// 8..48 (bit `i % 8` of byte `8 + i / 8`), then the move's two bytes
    /// (4 and 5, low byte first).
    pub fn places() -> Vec<Place> {
        (0..STATE_BITS).map(|i| Place { byte: 8 + i / 8, bit: (i % 8) as u8 }).chain((0..MOVE_BITS).map(|t| Place { byte: 5 - t / 8, bit: (t % 8) as u8 })).collect()
    }
    /// Chunk slots of an entry's stream: the two state chunks, then one
    /// per signed bit.
    pub const N_CHUNKS: usize = 2 + SIGNED_BITS;
    pub const CHUNK_OFFSET: usize = 2;
    /// `role`'s signature exhibit against the counterparty's entries, once
    /// the counterparty's commitment roots are served.
    pub fn sig_claim_for(&self, role: Role) -> Option<SigExhibit> {
        let roots = self.roots_of(role.other())?;
        Some(SigExhibit {
            checkpoint: self.params.checkpoint,
            target: lngap_factchain::pow_target(),
            game_id: self.params.game_id,
            me: role.idx() as u8,
            w_max: self.params.w_max,
            k: 2,
            n_chunks: Self::N_CHUNKS,
            chunk_offset: Self::CHUNK_OFFSET,
            places: Self::places(),
            roots,
            levels: levels_for(2 * SIGNED_BITS),
        })
    }
    /// White is the user and moves at odd depths.
    pub fn mover_at(depth: u32) -> Role {
        if depth % 2 == 1 { Role::User } else { Role::Hub }
    }
    pub fn role_of(c: Colour) -> Role {
        match c {
            Colour::White => Role::User,
            Colour::Black => Role::Hub,
        }
    }
    pub fn stall_claim_for(&self, role: Role) -> StallClaim {
        StallClaim {
            layout: Layout::chess(),
            checkpoint: self.params.checkpoint,
            target: lngap_factchain::pow_target(),
            game_id: self.params.game_id,
            me: role.idx() as u8,
            w_max: self.params.w_max,
            initial_e2: ChessState::initial().to_e().to_vec(),
            k: 2,
            check_next: true,
        }
    }
    pub fn lie_claim_for(&self, role: Role) -> StallClaim {
        StallClaim { check_next: false, ..self.stall_claim_for(role) }
    }
    /// The venue entry for `state` (after move `state.depth`) by its mover,
    /// signed with the mover's reveal of the signed bits.
    pub fn entry(&self, state: &ChessState, sigs: Vec<[u8; 20]>) -> ChessEntry {
        ChessEntry { game_id: self.params.game_id, depth: state.depth, mover: Self::mover_at(u32::from(state.depth)).idx() as u8, state: state.clone(), sigs }
    }
    /// The challenge kinds the disprove leaves cover.
    pub fn kinds() -> Vec<Kind> {
        Kind::ALL.into_iter().filter(|k| *k != Kind::MoveNumber).collect()
    }
    pub fn leaf_name(kind: Kind) -> String {
        format!("chess_{}", format!("{kind:?}").to_lowercase())
    }
    fn decode_claim(claim: &Claim) -> Result<(ChessState, Move, ChessState)> {
        let prior = ChessState::from_bits(&claim.prior)?;
        let after = ChessState::from_bits(&claim.new)?;
        let mv = Move::from_u16(bits_to_uint(&claim.mv) as u16).map_err(|e| anyhow!("{e}"))?;
        Ok((prior, mv, after))
    }
    /// The exhibit for `kind` against a claim, if the kind applies.
    pub fn exhibit(claim: &Claim, kind: Kind) -> Option<Vec<i64>> {
        let (prior, mv, after) = Self::decode_claim(claim).ok()?;
        find_kind(&prior.pos, mv, &after.pos, kind).map(exhibit_values)
    }
}

impl Contract for ChessFc {
    type State = ChessState;
    type Move = Move;

    fn name(&self) -> &str {
        &self.name
    }
    fn outcomes(&self) -> Vec<Outcome> {
        vec![Outcome::new(0, "UserWins", Payout::UserAll), Outcome::new(1, "HubWins", Payout::HubAll), Outcome::new(2, "Draw", Payout::Even)]
    }
    fn initial(&self) -> ChessState {
        ChessState::initial()
    }
    fn turn(&self, s: &ChessState) -> Option<Role> {
        match terminal(&s.pos) {
            Some(Terminal::Stalemate) => None,
            _ => Some(Self::role_of(s.pos.side)),
        }
    }
    fn transition(&self, s: &ChessState, m: &Move, mover: Role) -> std::result::Result<ChessState, Invalid> {
        if Self::role_of(s.pos.side) != mover {
            return Err(Invalid(format!("{mover} is not on turn")));
        }
        let mut pos = apply(&s.pos, *m).map_err(|v| Invalid(format!("{v}")))?;
        pos.fullmove = 0;
        Ok(ChessState { pos, mv: *m, depth: s.depth + 1 })
    }
    /// A stalemate is a draw; otherwise the side to move forfeits (a
    /// checkmated side included: it cannot move).
    fn resolution(&self, s: &ChessState) -> Outcome {
        let code = match terminal(&s.pos) {
            Some(Terminal::Stalemate) => 2,
            _ => match s.pos.side {
                Colour::White => 1,
                Colour::Black => 0,
            },
        };
        Contract::outcomes(self).into_iter().find(|o| o.code == code).unwrap()
    }
    fn max_depth_from(&self, s: &ChessState) -> u32 {
        (self.params.w_max as u32).saturating_sub(1 + u32::from(s.depth))
    }
    fn n_state_bits(&self) -> usize {
        STATE_BITS
    }
    fn n_move_bits(&self) -> usize {
        MOVE_BITS
    }
    fn state_bits(&self, s: &ChessState) -> Vec<bool> {
        s.to_bits()
    }
    fn state_from_bits(&self, b: &[bool]) -> Result<ChessState> {
        ChessState::from_bits(b)
    }
    fn move_bits(&self, m: &Move) -> Vec<bool> {
        uint_to_bits(u32::from(m.to_u16()), MOVE_BITS)
    }
    fn move_from_bits(&self, b: &[bool]) -> Result<Move> {
        ensure!(b.len() == MOVE_BITS);
        Move::from_u16(bits_to_uint(b) as u16).map_err(|e| anyhow!("{e}"))
    }
    fn describe_state(&self, s: &ChessState) -> String {
        format!("depth {} after {}: {}", s.depth, s.mv, s.pos.to_fen())
    }
    fn describe_move(&self, m: &Move) -> String {
        m.to_string()
    }
    /// One leaf per challenge kind, reading both positions from the claim's
    /// end state; the challenger supplies the exhibit.
    fn disprove_leaves(&self, ctx: &LeafCtx) -> Vec<DisproveSpec> {
        let Some(end) = ctx.end.clone() else { return vec![] };
        Self::kinds()
            .into_iter()
            .map(|kind| {
                let body = leaf_over_registers(Builder::new().wots_verify(&end), kind, REGISTERS);
                DisproveSpec {
                    name: Self::leaf_name(kind),
                    consumes: vec![Field::End, Field::Exhibit],
                    body,
                    detects: Arc::new(move |c: &Claim| Self::exhibit(c, kind).is_some()),
                    needs: vec![],
                    exhibit: Some(Arc::new(move |c: &Claim| Self::exhibit(c, kind))),
                }
            })
            .collect()
    }
    fn graph_shape(&self) -> GraphShape {
        GraphShape::Stall
    }
    fn move_extras(&self, _depth: u32, _prover: Role) -> MoveExtras {
        MoveExtras { cltv: None, expects: vec![], bind_end: None, bind_prior: None, bind_depth: None, wots_only: true }
    }
    fn claim(&self, _from: &[bool], _depth: u32) -> Option<ClaimSpec> {
        None
    }
    fn claim_bound(&self, _from: &[bool], _depth: u32, _keys: &[DepthKeys]) -> Option<ClaimSpec> {
        None
    }
    fn claim_data(&self, _from: &[bool], _depth: u32) -> ClaimData {
        vec![]
    }
    fn stall_claim(&self, role: Role) -> Option<ClaimSpec> {
        Some(self.stall_claim_for(role).spec())
    }
    fn stall_claim_data(&self, role: Role) -> ClaimData {
        self.store.get(&Self::stall_key(self.params.game_id, role)).unwrap_or_default()
    }
    fn lie_claim(&self, role: Role) -> Option<ClaimSpec> {
        Some(self.lie_claim_for(role).spec())
    }
    fn lie_claim_data(&self, role: Role) -> ClaimData {
        self.store.get(&Self::lie_key(self.params.game_id, role)).unwrap_or_default()
    }
    fn sig_claim(&self, role: Role) -> Option<ClaimSpec> {
        Some(self.sig_claim_for(role)?.spec())
    }
    fn sig_claim_data(&self, role: Role) -> ClaimData {
        self.store.get(&Self::sig_key(self.params.game_id, role)).unwrap_or_default()
    }
    /// `E` (words 10..20) is the state after the move, `E2` (20..30) the
    /// state before it; the move is in `E`'s bytes 36..38.
    fn state_from_end(&self, end: &[u32]) -> Option<(Vec<bool>, Vec<bool>, Vec<bool>)> {
        if end.len() != 30 {
            return None;
        }
        let e = words_bytes(&end[10..20]);
        let e2 = words_bytes(&end[20..30]);
        let after = ChessState::from_e(e.as_slice().try_into().ok()?).ok()?;
        Some((bytes_to_bits(&e2), uint_to_bits(u32::from(after.mv.to_u16()), MOVE_BITS), bytes_to_bits(&e)))
    }
}

/// A registry knowing `chess-fc:{params}`.
pub fn registry(store: ServedData) -> ProgramRegistry {
    let mut r = ProgramRegistry::new();
    r.register_factory(ChessFc::PREFIX, move |p| Ok(Arc::new(ChessFc::from_str(p, store.clone())?) as Arc<dyn Program>));
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program() -> ChessFc {
        ChessFc::new(ChessFcParams { game_id: 1, checkpoint: [0; 20], w_max: 20 }, ServedData::default())
    }

    #[test]
    fn state_round_trips_and_transitions() {
        let p = program();
        let s0 = p.initial();
        assert_eq!(ChessState::from_bits(&s0.to_bits()).unwrap(), s0);
        let s1 = p.transition(&s0, &Move::parse("e2e4").unwrap(), Role::User).unwrap();
        assert_eq!(s1.depth, 1);
        assert_eq!(ChessState::from_e(&s1.to_e()).unwrap(), s1);
        assert!(p.transition(&s0, &Move::parse("e2e4").unwrap(), Role::Hub).is_err());
        assert!(p.transition(&s1, &Move::parse("e2e4").unwrap(), Role::Hub).is_err());
        assert_eq!(p.turn(&s1), Some(Role::Hub));
        assert_eq!(p.resolution(&s1).name, "UserWins", "the hub on turn forfeits");
        let e = p.entry(&s1, vec![[0u8; 20]; SIGNED_BITS]);
        let bytes = e.encode();
        assert_eq!(bytes.len(), ENTRY_BYTES);
        assert_eq!(ChessEntry::decode(&bytes).unwrap(), e);
        // the claim's end state decodes back to (prior, move, state)
        let mut end = vec![0u32; 30];
        end[10..20].copy_from_slice(&lngap_contract::claim::words_from_bytes(&s1.to_e()));
        end[20..30].copy_from_slice(&lngap_contract::claim::words_from_bytes(&s0.to_e()));
        let (prior, mv, new) = Contract::state_from_end(&p, &end).unwrap();
        assert_eq!(prior, s0.to_bits());
        assert_eq!(new, s1.to_bits());
        assert_eq!(Contract::move_from_bits(&p, &mv).unwrap(), Move::parse("e2e4").unwrap());
    }

    /// Each leaf body over a signed end state, through the interpreter:
    /// accepted with the exhibit exactly when the exhibit search finds one.
    #[test]
    fn register_leaves_match_the_exhibit_search() {
        use lngap_btc::keys::Seed;
        use lngap_lamport::keystore::KeyStore;
        let p = program();
        let mut ks = KeyStore::new(Seed::from_label("end"));
        let end_pk = ks.generate_wots("end", 120).unwrap();
        let ctx = LeafCtx { depth: 1, prover: Role::User, prior: lngap_contract::PriorState::Constant(vec![]), mv: ks.generate("m", 16).unwrap(), new: ks.generate("s", 320).unwrap(), code: ks.generate("c", 2).unwrap(), outcomes: Contract::outcomes(&p), end: Some(end_pk.clone()) };
        let specs = Contract::disprove_leaves(&p, &ctx);
        assert_eq!(specs.len(), 12);
        let s0 = p.initial();
        let mut cases: Vec<(ChessState, Move, ChessState)> = Vec::new();
        for uci in ["e2e4", "g1f3", "c1e3", "e2e5", "e1e2", "a2a4"] {
            let mv = Move::parse(uci).unwrap();
            let after = match p.transition(&s0, &mv, Role::User) {
                Ok(s) => s,
                Err(_) => ChessState { pos: lngap_chess::certificate::mechanical_successor(&s0.pos, mv), mv, depth: 1 },
            };
            cases.push((s0.clone(), mv, after));
        }
        // a legal move with a corrupted successor square
        let mv = Move::parse("e2e4").unwrap();
        let mut bad = p.transition(&s0, &mv, Role::User).unwrap();
        bad.pos.set(Square::parse("h8").unwrap(), None);
        cases.push((s0.clone(), mv, bad));
        let mut checked = 0;
        for (prior, mv, after) in &cases {
            let claim = Claim { prior: prior.to_bits(), mv: p.move_bits(mv), new: after.to_bits(), code: 0, mover: Role::User };
            let mut end = vec![0u32; 30];
            end[10..20].copy_from_slice(&lngap_contract::claim::words_from_bytes(&after.to_e()));
            end[20..30].copy_from_slice(&lngap_contract::claim::words_from_bytes(&prior.to_e()));
            let mut signer = KeyStore::new(Seed::from_label("end"));
            signer.generate_wots("end", 120).unwrap();
            let sig = signer.sign_wots("end", &words_bytes(&end)).unwrap();
            for spec in &specs {
                let kind = ChessFc::kinds().into_iter().find(|k| ChessFc::leaf_name(*k) == spec.name).unwrap();
                let want = ChessFc::exhibit(&claim, kind);
                let exhibit = want.clone().unwrap_or_else(|| vec![0; lngap_chess::leaf::Kind::exhibit_len(kind)]);
                let args = spec.witness_args_with(None, &lngap_lamport::Reveal { preimages: vec![] }, &lngap_lamport::Reveal { preimages: vec![] }, &lngap_lamport::Reveal { preimages: vec![] }, &[], Some(&sig), &exhibit);
                let stack: Vec<Vec<u8>> = args.iter().rev().cloned().collect();
                let out = lngap_script32::sim::run(&spec.body, stack).unwrap_or_else(|e| panic!("{} on {mv}: {e}", spec.name));
                let accepted = out.len() == 1 && !out[0].is_empty();
                assert_eq!(accepted, want.is_some(), "{} on {mv} from {}", spec.name, prior.pos.to_fen());
                checked += 1;
            }
        }
        assert_eq!(checked, cases.len() * 12);
    }

    #[test]
    fn exhibits_name_the_leaf() {
        let p = program();
        let s0 = p.initial();
        let s1 = p.transition(&s0, &Move::parse("e2e4").unwrap(), Role::User).unwrap();
        let honest = Claim { prior: s0.to_bits(), mv: p.move_bits(&Move::parse("e2e4").unwrap()), new: s1.to_bits(), code: 0, mover: Role::User };
        for k in ChessFc::kinds() {
            assert!(ChessFc::exhibit(&honest, k).is_none(), "{k:?}");
        }
        // a bishop jumping a pawn: the ray leaf, exhibit j = 1
        let mut bad = s0.clone();
        bad.pos = lngap_chess::certificate::mechanical_successor(&s0.pos, Move::parse("c1e3").unwrap());
        bad.mv = Move::parse("c1e3").unwrap();
        bad.depth = 1;
        let lie = Claim { prior: s0.to_bits(), mv: p.move_bits(&bad.mv), new: bad.to_bits(), code: 0, mover: Role::User };
        assert_eq!(ChessFc::exhibit(&lie, Kind::Ray), Some(vec![1]));
        assert!(ChessFc::exhibit(&lie, Kind::Mover).is_none());
    }
}

#[cfg(test)]
mod claim_tests {
    use super::*;
    use lngap_factchain::sig::CommitTree;
    use lngap_factchain::{genesis, ChainClient, Miner};

    /// The signature exhibit's size for chess: its stream is the whole
    /// 6,768-byte entry, its tree three levels.
    #[test]
    fn measure_the_signature_exhibit() {
        let store = ServedData::default();
        let commits: Vec<[[u8; 20]; 2]> = (0..SIGNED_BITS).map(|i| [[i as u8; 20], [i as u8 ^ 0x80; 20]]).collect();
        let levels = levels_for(2 * SIGNED_BITS);
        for w_max in [20usize, 200] {
            let roots: Vec<Option<[u8; 20]>> = (0..w_max).map(|d| (d >= 1 && ChessFc::mover_at(d as u32) == Role::Hub).then(|| CommitTree::new(&commits, levels).root())).collect();
            ChessFc::put_roots(&store, 3, Role::Hub, &roots);
            let p = ChessFc::new(ChessFcParams { game_id: 3, checkpoint: [1u8; 20], w_max }, store.clone());
            let x = p.sig_claim_for(Role::User).unwrap();
            let spec = x.spec();
            println!("MEASURE sig exhibit chess W_max={w_max} k=2: {} steps -> {} padded, {} rounds, {} words, {} levels", x.n_steps(), spec.steps.len(), spec.rounds(), spec.n_words, levels);
            assert!(!spec.valid(&x.data(2, 0, false, &[[0u8; 96]; 2], &vec![0u8; ENTRY_BYTES], &commits)));
        }
    }

    /// The honest stall claim's data, laid out by `Layout::chess`, passes
    /// every step of its own spec: the depth register is read where
    /// `ChessState::to_e` puts it, and the head predicates find the
    /// mined entry's head where the layout says it is.
    #[test]
    fn honest_stall_claim_is_valid_on_a_mined_chain() {
        let g = genesis();
        let store = ServedData::default();
        let p = ChessFc::new(ChessFcParams { game_id: 2, checkpoint: g.header.digest(), w_max: 20 }, store);
        let s0 = ChessState::initial();
        let s1 = p.transition(&s0, &Move::parse("e2e4").unwrap(), Role::User).unwrap();
        let entry = p.entry(&s1, vec![[7u8; 20]; SIGNED_BITS]).encode();
        let mut miner = Miner::new(g.header.digest(), 0);
        let mut client = ChainClient::from_checkpoint(0, g.header.digest());
        for e in [entry, vec![]] {
            miner.submit(e);
            client.verify_and_append(&miner.mine_next().unwrap()).unwrap();
        }
        let headers: Vec<[u8; lngap_factchain::HEADER_BYTES]> = client.chain_headers().iter().map(|h| h.0).collect();
        let c = p.stall_claim_for(Role::User);
        let spec = c.spec();
        let data = c.data(1, &headers, &words_from_bytes(&s1.to_e()), &words_from_bytes(&s0.to_e()));
        let mut st = spec.start.clone();
        for (i, step) in spec.steps.iter().enumerate() {
            let (next, ok) = spec.apply(i, step, &st, spec.data_for(&data, i));
            assert!(ok, "step {i} ({}) fails on honest data", step.name());
            st = next;
        }
    }
}
