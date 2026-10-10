//! LN-GAP v3's dispute ladder in BitVMX's own shape (JUMPLIST_PLAN.md,
//! phase J2).
//!
//! A dispute is BitVMX's n-ary search over the statement program, played
//! on chain one move per link. Each move is its mover's one-time
//! signatures on the values it posts, and nothing else, one key per field
//! (so that a rule re-reveals only the fields it reads, within Script's
//! 1,000-item stack):
//!
//! - depth 1, Alice: the claim (the last step and its hash) and round 1's
//!   hashes;
//! - depth `2r`, the hub: its choice of segment in round `r`;
//! - depth `2r + 1`, Alice: round `r + 1`'s hashes (`r < R`);
//! - depth `2R + 1`, Alice: the disputed step: its record (the reads, the
//!   write, the last-write steps, the agreed step `t`), the hash after
//!   step `t` and the hash after step `t + 1`.
//!
//! The search's state (the interval) is never signed: a rule re-reveals
//! the signatures it reads (public once posted) and derives what it needs,
//! as BitVMX's own scripts do. The agreed step is the hub's choices
//! concatenated (BitVMX's `step_from_decision_bits`); the final move's
//! hashes must be those Alice posted for steps `t` and `t + 1` in the
//! search (BitVMX's equivocation challenges); its record is checked by
//! BitVMX's final-step challenges and proved by its per-instruction
//! scripts.

pub mod jhash;
pub mod jscript;
pub mod jump;
pub mod ladder;
pub mod moves;
pub mod rules;
pub mod script;
pub mod tail;

use emulator::decision::nary_search::NArySearchDefinition;

/// A move's message layout, by depth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Depth 1: the claim, then round 1's hashes.
    Claim,
    /// Depth `2r`: the hub's choice in round `r` (one byte).
    Choice(u32),
    /// Depth `2r + 1`, `r >= 1`: round `r + 1`'s hashes.
    Hashes(u32),
    /// Depth `2R + 1`: the disputed step.
    Final,
}

/// The claim's bytes in move 1: the last step (8, big-endian), its hash.
pub const CLAIM_BYTES: usize = 28;
pub const C_LAST_STEP: usize = 0;
pub const C_LAST_HASH: usize = 8;

/// The final move: the record (64 bytes, lngap-zk's D60 layout: its
/// `step` is the agreed step `t`), then the hash after `t`, then the hash
/// after `t + 1`; each a field.
pub const RECORD_BYTES: usize = 64;
pub const F_STEP_HASH: usize = RECORD_BYTES;
pub const F_NEXT_HASH: usize = RECORD_BYTES + 20;
pub const FINAL_BYTES: usize = RECORD_BYTES + 40;
/// The final move's fields.
pub const FIELD_RECORD: usize = 0;
pub const FIELD_STEP_HASH: usize = 1;
pub const FIELD_NEXT_HASH: usize = 2;
/// Under a jump list, two more: the long jump's hash the disputed step
/// commits to, and the disputed step's number `t + 1` (4 bytes).
pub const F_JUMP_HASH: usize = FINAL_BYTES;
pub const F_SUCC: usize = FINAL_BYTES + 20;
pub const FIELD_JUMP_HASH: usize = 3;
pub const FIELD_SUCC: usize = 4;
/// Move 1's fields: the claim, then round 1's hashes, one each.
pub const FIELD_CLAIM: usize = 0;

/// The search's shape: BitVMX's n-ary search definition, and the trace's
/// hash: a linear chain, or a jump list.
#[derive(Clone, Debug)]
pub struct Schedule {
    pub def: NArySearchDefinition,
    pub jump: Option<jump::JumpList>,
}

impl Schedule {
    pub fn new(def: NArySearchDefinition) -> Schedule {
        Schedule { def, jump: None }
    }
    /// From a BitVMX program definition file (`jump_list: true` for a
    /// jump list).
    pub fn load(pdf: &str) -> anyhow::Result<Schedule> {
        let p = emulator::loader::program_definition::ProgramDefinition::from_config(pdf).map_err(|e| anyhow::anyhow!("{pdf}: {e:?}"))?;
        let def = p.nary_def();
        let jump = p.jump_list.then(|| jump::JumpList::for_max_steps(def.max_steps));
        Ok(Schedule { def, jump })
    }
    /// R, the rounds.
    pub fn rounds(&self) -> u32 {
        u32::from(self.def.total_rounds())
    }
    /// The moves: `2R + 1`.
    pub fn depths(&self) -> u32 {
        2 * self.rounds() + 1
    }
    /// The hashes Alice posts in round `r` (1-based).
    pub fn hashes(&self, r: u32) -> usize {
        usize::from(self.def.hashes_for_round(r as u8))
    }
    /// The segments the hub chooses among in round `r`: its choice is
    /// below this.
    pub fn segments(&self, r: u32) -> u32 {
        self.hashes(r) as u32 + 1
    }
    /// The bits round `r`'s choice contributes to the agreed step.
    pub fn bits(&self, r: u32) -> u32 {
        u32::from(self.def.bits_for_round(r as u8))
    }
    pub fn kind(&self, depth: u32) -> Kind {
        let m = self.depths();
        assert!((1..=m).contains(&depth), "depth {depth} outside 1..={m}");
        if depth == 1 {
            Kind::Claim
        } else if depth == m {
            Kind::Final
        } else if depth % 2 == 0 {
            Kind::Choice(depth / 2)
        } else {
            Kind::Hashes(depth / 2)
        }
    }
    /// The bytes move `depth` signs.
    pub fn bytes(&self, depth: u32) -> usize {
        self.fields(depth).iter().map(|(_, l)| l).sum()
    }
    /// Where round `r`'s hash `i` (0-based) sits: (the depth whose move
    /// carries it, its byte offset there).
    pub fn hash_at(&self, r: u32, i: usize) -> (u32, usize) {
        assert!(i < self.hashes(r), "round {r} has {} hashes", self.hashes(r));
        if r == 1 {
            (1, CLAIM_BYTES + 20 * i)
        } else {
            (2 * r - 1, 20 * i)
        }
    }
    /// Round `r`'s hash `i` as a field: (depth, field index).
    pub fn hash_field(&self, r: u32, i: usize) -> (u32, usize) {
        let (d, _) = self.hash_at(r, i);
        (d, if r == 1 { 1 + i } else { i })
    }
    /// Move `depth`'s fields: (offset, length) in its message, each signed
    /// under its own key.
    pub fn fields(&self, depth: u32) -> Vec<(usize, usize)> {
        match self.kind(depth) {
            Kind::Claim => std::iter::once((0, CLAIM_BYTES)).chain((0..self.hashes(1)).map(|i| (CLAIM_BYTES + 20 * i, 20))).collect(),
            Kind::Choice(_) => vec![(0, 1)],
            Kind::Hashes(r) => (0..self.hashes(r + 1)).map(|i| (20 * i, 20)).collect(),
            Kind::Final if self.jump.is_some() => vec![(0, RECORD_BYTES), (F_STEP_HASH, 20), (F_NEXT_HASH, 20), (F_JUMP_HASH, 20), (F_SUCC, 4)],
            Kind::Final => vec![(0, RECORD_BYTES), (F_STEP_HASH, 20), (F_NEXT_HASH, 20)],
        }
    }
    /// The agreed step from the hub's choices (BitVMX's
    /// `step_from_decision_bits`).
    pub fn agreed_step(&self, choices: &[u32]) -> u64 {
        self.def.step_from_decision_bits(choices)
    }
}

/// Alice moves at odd depths (the prover), the hub at even ones.
pub fn mover_at(depth: u32) -> lngap_channel::Role {
    if depth % 2 == 1 {
        lngap_channel::Role::User
    } else {
        lngap_channel::Role::Hub
    }
}

/// The digit indices of message bytes `off .. off + len` (two per byte,
/// the high nibble first).
pub fn digits(off: usize, len: usize) -> std::ops::Range<usize> {
    2 * off..2 * (off + len)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_groth16_verifiers_schedules() {
        // binary: 29 rounds of one hash
        let s = Schedule::new(NArySearchDefinition::new(536_870_912, 2));
        assert_eq!((s.rounds(), s.depths(), s.hashes(1), s.hashes(29)), (29, 59, 1, 1));
        // 8-ary: 9 full rounds of 7 hashes and a last of 3 (2 bits)
        let s = Schedule::new(NArySearchDefinition::new(536_870_912, 8));
        assert_eq!((s.rounds(), s.depths()), (10, 21));
        assert_eq!((s.hashes(1), s.hashes(9), s.hashes(10)), (7, 7, 3));
        assert_eq!((s.bits(1), s.bits(10)), (3, 2));
        assert_eq!(s.bytes(1), CLAIM_BYTES + 140);
        assert_eq!(s.kind(20), Kind::Choice(10));
        assert_eq!(s.hash_at(10, 2), (19, 40));
        assert_eq!(s.hash_field(10, 2), (19, 2));
        assert_eq!(s.hash_field(1, 0), (1, 1));
        assert_eq!(s.fields(1).len(), 8);
        assert_eq!(s.fields(21), vec![(0, 64), (64, 20), (84, 20)]);
        // the agreed step is the choices' bits, concatenated
        assert_eq!(s.agreed_step(&[1, 0, 0, 0, 0, 0, 0, 0, 0, 3]), (1 << 26) + 3);
    }
}
