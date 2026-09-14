//! Leaf construction: Move, Settle, Split, and the declarative disprove leaves.

use std::ops::Range;
use std::sync::Arc;

use bitcoin::opcodes::all::*;
use bitcoin::opcodes::Opcode;
use bitcoin::script::{Builder, ScriptBuf};
use lngap_btc::script::BuilderExt;
use lngap_btc::taptree::Leaf;
use lngap_btc::tx::Timelock;
use lngap_channel::{CommitCtx, Role};
use lngap_lamport::gadgets::LamportExt;
use lngap_lamport::{PublicKey, Reveal};

use crate::{Extra, MoveExtras, Outcome, CODE_BITS};

/// Where a disprove leaf gets the state before the disputed move.
#[derive(Clone, Debug)]
pub enum PriorState {
    /// Depth 1: the doubly-signed state, baked into the leaf as constants.
    Constant(Vec<bool>),
    /// Depth ≥ 2: the previous prover's on-chain commitment.
    Committed(PublicKey),
}

/// Everything a contract needs to write the disprove leaves for one depth.
#[derive(Clone, Debug)]
pub struct LeafCtx {
    pub depth: u32,
    pub prover: Role,
    pub prior: PriorState,
    pub mv: PublicKey,
    pub new: PublicKey,
    pub code: PublicKey,
    pub outcomes: Vec<Outcome>,
}

impl LeafCtx {
    pub fn challenger(&self) -> Role {
        self.prover.other()
    }
}

/// A slice of the prover's (or previous prover's) reveals a leaf consumes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Field {
    Prior(Range<usize>),
    Move(Range<usize>),
    New(Range<usize>),
    Code,
    /// The challenger's own reveal of `needs[i]` (not part of the claim).
    Need(usize),
}

/// What a Move claimed, decoded, for native re-checking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub prior: Vec<bool>,
    pub mv: Vec<bool>,
    pub new: Vec<bool>,
    pub code: u8,
    pub mover: Role,
}

/// A disprove leaf: `<challenger> OP_CHECKSIGVERIFY <body>`. `detects` is the
/// native version of the check: true iff the leaf accepts (the claim is
/// inconsistent in this particular way).
#[derive(Clone)]
pub struct DisproveSpec {
    pub name: String,
    pub consumes: Vec<Field>,
    pub body: ScriptBuf,
    pub detects: Arc<dyn Fn(&Claim) -> bool + Send + Sync>,
    /// Statements the challenger must be able to reveal to use this leaf.
    pub needs: Vec<Extra>,
}

impl std::fmt::Debug for DisproveSpec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DisproveSpec({}, consumes {:?}, {} B)", self.name, self.consumes, self.body.len())
    }
}

impl DisproveSpec {
    pub fn leaf(&self, challenger_key: &bitcoin::key::XOnlyPublicKey) -> Leaf {
        let mut b = Builder::new().checksigverify(challenger_key);
        for ins in self.body.instructions() {
            b = match ins.expect("valid script") {
                bitcoin::script::Instruction::Op(op) => b.push_opcode(op),
                bitcoin::script::Instruction::PushBytes(pb) => b.push_slice(pb),
            };
        }
        Leaf::new(format!("disprove_{}", self.name), b.into_script(), Timelock::NONE)
    }

    /// Witness elements after the challenger's signature, in consumption order.
    /// `prior` is `None` when the prior state is a constant; `needs` are the
    /// challenger's reveals for `self.needs`, by index.
    pub fn witness_args(&self, prior: Option<&Reveal>, mv: &Reveal, new: &Reveal, code: &Reveal, needs: &[Reveal]) -> Vec<Vec<u8>> {
        let mut out = Vec::new();
        for f in &self.consumes {
            match f {
                Field::Prior(r) => {
                    if let Some(p) = prior {
                        out.extend(p.slice(r.clone()).consumption_order())
                    }
                }
                Field::Move(r) => out.extend(mv.slice(r.clone()).consumption_order()),
                Field::New(r) => out.extend(new.slice(r.clone()).consumption_order()),
                Field::Code => out.extend(code.consumption_order()),
                Field::Need(i) => out.extend(needs[*i].consumption_order()),
            }
        }
        out
    }
}

/// Builds a disprove leaf body while recording which reveals it consumes.
///
/// Two phases. First declare every input (`prior_uint`, `mv_uint`,
/// `new_uint`, `code_uint`): each is decoded from the witness and parked on
/// the altstack, so decoding never sees a script-computed value in the way.
/// The first computation call restores all inputs to the main stack **in
/// declaration order** (last declared on top) and closes the input phase.
/// Numbers decoded from reveals are script numbers (≤ 31 bits per decode).
pub struct LeafBuilder<'a> {
    ctx: &'a LeafCtx,
    b: Builder,
    consumes: Vec<Field>,
    n_inputs: usize,
    inputs_open: bool,
    needs: Vec<Extra>,
}

impl<'a> LeafBuilder<'a> {
    pub fn new(ctx: &'a LeafCtx) -> Self {
        LeafBuilder { ctx, b: Builder::new(), consumes: vec![], n_inputs: 0, inputs_open: true, needs: vec![] }
    }
    /// Input phase: require the challenger to reveal `extra` (an
    /// `expect_uint` check; leaves nothing on the stack).
    pub fn need(mut self, extra: Extra) -> Self {
        assert!(self.inputs_open, "declare needs before computing");
        self.b = self.b.expect_uint(&extra.pk, extra.value);
        self.consumes.push(Field::Need(self.needs.len()));
        self.needs.push(extra);
        self
    }
    fn park(mut self) -> Self {
        assert!(self.inputs_open, "declare all inputs before computing");
        self.b = self.b.push_opcode(OP_TOALTSTACK);
        self.n_inputs += 1;
        self
    }
    fn restore(mut self) -> Self {
        if self.inputs_open {
            self.inputs_open = false;
            for _ in 0..self.n_inputs {
                self.b = self.b.push_opcode(OP_FROMALTSTACK);
            }
            // altstack pops reverse the order; reverse back so the first
            // declared input is deepest: for i in 1..n { <i> OP_ROLL }
            for i in 1..self.n_inputs {
                self.b = self.b.push_int(i as i64).push_opcode(OP_ROLL);
            }
        }
        self
    }
    /// Input: the prior state's bits `r` as a number (constant at depth 1,
    /// decoded from the previous prover's reveal otherwise).
    pub fn prior_uint(mut self, r: Range<usize>) -> Self {
        match &self.ctx.prior {
            PriorState::Constant(bits) => {
                let v = lngap_lamport::bits_to_uint(&bits[r.clone()]);
                self.b = self.b.push_int(i64::from(v));
            }
            PriorState::Committed(pk) => {
                self.b = self.b.decode_uint(&pk.slice(r.clone()));
            }
        }
        self.consumes.push(Field::Prior(r));
        self.park()
    }
    /// Input: the move's bits `r` as a number.
    pub fn mv_uint(mut self, r: Range<usize>) -> Self {
        self.b = self.b.decode_uint(&self.ctx.mv.slice(r.clone()));
        self.consumes.push(Field::Move(r));
        self.park()
    }
    /// Input: the claimed new state's bits `r` as a number.
    pub fn new_uint(mut self, r: Range<usize>) -> Self {
        self.b = self.b.decode_uint(&self.ctx.new.slice(r.clone()));
        self.consumes.push(Field::New(r));
        self.park()
    }
    /// Input: the claimed outcome code.
    pub fn code_uint(mut self) -> Self {
        self.b = self.b.decode_uint(&self.ctx.code);
        self.consumes.push(Field::Code);
        self.park()
    }
    pub fn op(self, op: Opcode) -> Self {
        let mut s = self.restore();
        s.b = s.b.push_opcode(op);
        s
    }
    pub fn int(self, v: i64) -> Self {
        let mut s = self.restore();
        s.b = s.b.push_int(v);
        s
    }
    pub fn with(self, f: impl FnOnce(Builder) -> Builder) -> Self {
        let mut s = self.restore();
        s.b = f(s.b);
        s
    }
    /// Finish. A leaf with no computed inputs (only `need`s) must still leave
    /// a truthy element: pass `always` = true for "accepts whenever the
    /// challenger holds the needs".
    pub fn finish(self, name: &str, detects: impl Fn(&Claim) -> bool + Send + Sync + 'static) -> DisproveSpec {
        let s = self.restore();
        DisproveSpec { name: name.to_string(), consumes: s.consumes, body: s.b.into_script(), detects: Arc::new(detects), needs: s.needs }
    }
    /// A leaf satisfied by the challenger's needs alone.
    pub fn finish_needs_only(self, name: &str) -> DisproveSpec {
        assert!(self.n_inputs == 0, "needs-only leaf has no decoded inputs");
        let mut s = self.restore();
        s.b = s.b.push_opcode(OP_PUSHNUM_1);
        DisproveSpec { name: name.to_string(), consumes: s.consumes, body: s.b.into_script(), detects: Arc::new(|_| true), needs: s.needs }
    }
}

/// `bit_decode OP_DROP` per bit, msb first: forces a valid preimage per bit.
fn reveal_verify(mut b: Builder, pk: &PublicKey) -> Builder {
    for i in (0..pk.n_bits()).rev() {
        b = b.bit_decode(&pk.bits[i]).push_opcode(OP_DROP);
    }
    b
}

/// The Move leaf at depth `d` for prover `P`: both signatures, then (if
/// `prior` is given) the previous prover's reveal of the state the move
/// leaves from, then P's reveals of move, new state and outcome code, then
/// any extra statements the contract requires (`expect_uint`), then the
/// claim's end-state signature. With `extras.bind_end`, the move and state
/// reveals are decoded and compared against the bound end-state word.
/// Carries `CSV to_self_delay` when P is the commitment's broadcaster and
/// the leaf spends the commitment's output (`from_root`), and `CLTV` if the
/// contract says the move is only allowed from some height.
/// Witness: `sig_U, sig_H, [prior reveal], move reveal, new-state reveal,
/// code reveal, extras..., [end signature]`.
#[allow(clippy::too_many_arguments)]
pub fn move_leaf(ctx: &CommitCtx, depth: u32, prover: Role, prior: Option<&PublicKey>, mv: &PublicKey, new: &PublicKey, code: &PublicKey, extras: &MoveExtras, claim_end: Option<&lngap_lamport::winternitz::WotsPublic>, from_root: bool) -> Leaf {
    let delayed = from_root && prover == ctx.broadcaster;
    let mut b = Builder::new();
    let mut tl = Timelock::NONE;
    if let Some(h) = extras.cltv {
        b = b.cltv(h);
        tl.cltv = Some(h);
    }
    if delayed {
        b = b.csv(ctx.params.to_self_delay);
        tl.csv = Some(ctx.params.to_self_delay);
    }
    b = ctx.two_of_two_verify(b);
    let bind_prior = extras.bind_prior.as_ref().filter(|_| claim_end.is_some() && prior.is_some());
    if let Some(p) = prior {
        if bind_prior.is_some() {
            b = b.decode_uint(p).push_opcode(OP_TOALTSTACK);
        } else {
            b = reveal_verify(b, p);
        }
    }
    let bind = extras.bind_end.as_ref().filter(|_| claim_end.is_some());
    if bind.is_some() {
        // decoded numbers parked: move below, state on top of the altstack
        b = b.decode_uint(mv).push_opcode(OP_TOALTSTACK);
        b = b.decode_uint(new).push_opcode(OP_TOALTSTACK);
    } else {
        b = reveal_verify(b, mv);
        b = reveal_verify(b, new);
    }
    b = reveal_verify(b, code);
    for e in &extras.expects {
        b = b.expect_uint(&e.pk, e.value);
    }
    if let Some(end) = claim_end {
        use lngap_lamport::winternitz::WotsExt;
        b = b.wots_verify(end);
        if let Some(bind) = bind {
            b = bind_check(b, end.params.message_digits as usize, bind.word);
        }
        if let Some(bp) = bind_prior {
            b = fold_state(b, end.params.message_digits as usize, bp.word).push_opcode(OP_FROMALTSTACK).push_opcode(OP_NUMEQUALVERIFY);
        }
        for _ in 0..end.params.message_digits / 2 {
            b = b.push_opcode(OP_2DROP);
        }
    }
    Leaf::new(format!("move_{depth}"), b.push_opcode(OP_PUSHNUM_1).into_script(), tl)
}

/// With `n` message nibbles on the stack (nibble `n-1` on top) and the
/// decoded state (top) and move on the altstack: nibble `8 word` is zero,
/// nibble `8 word + 1` is the move, and nibbles `8 word + 2 ..= 8 word + 7`
/// read as a number are the state. Consumes the altstack values.
/// With `n` message nibbles on the stack (nibble `n-1` on top), push the
/// number formed by nibbles `8 word + 2 ..= 8 word + 7` (a word's low 24 bits).
fn fold_state(mut b: Builder, n: usize, word: usize) -> Builder {
    let d = |i: usize| (n - 1 - i) as i64;
    let base = 8 * word;
    b = b.push_int(d(base + 2)).push_opcode(OP_PICK);
    for k in 3..8 {
        for _ in 0..4 {
            b = b.push_opcode(OP_DUP).push_opcode(OP_ADD);
        }
        b = b.push_int(d(base + k) + 1).push_opcode(OP_PICK).push_opcode(OP_ADD);
    }
    b
}

fn bind_check(mut b: Builder, n: usize, word: usize) -> Builder {
    let d = |i: usize| (n - 1 - i) as i64;
    let base = 8 * word;
    b = fold_state(b, n, word);
    b = b.push_opcode(OP_FROMALTSTACK).push_opcode(OP_NUMEQUALVERIFY);
    b = b.push_int(d(base + 1)).push_opcode(OP_PICK).push_opcode(OP_FROMALTSTACK).push_opcode(OP_NUMEQUALVERIFY);
    b.push_int(d(base)).push_opcode(OP_PICK).push_int(0).push_opcode(OP_NUMEQUALVERIFY)
}

/// Move witness args after the two signatures.
pub fn move_witness_args(prior: Option<&Reveal>, mv: &Reveal, new: &Reveal, code: &Reveal, extras: &[Reveal], claim_end: Option<&lngap_lamport::winternitz::WotsSig>) -> Vec<Vec<u8>> {
    let mut v = prior.map(|p| p.consumption_order()).unwrap_or_default();
    v.extend(mv.consumption_order());
    v.extend(new.consumption_order());
    v.extend(code.consumption_order());
    for e in extras {
        v.extend(e.consumption_order());
    }
    if let Some(sig) = claim_end {
        v.extend(sig.consumption_order());
    }
    v
}

/// The Settle leaf on the commitment's contract output: after the absolute
/// deadline, both signatures. Delayed by `to_self_delay` in the broadcaster's
/// version (D1) so a revoked broadcast can be punished first.
pub fn settle_leaf(ctx: &CommitCtx, deadline: u32) -> Leaf {
    let mut b = Builder::new().cltv(deadline);
    let tl = if ctx.params.to_self_delay > 0 {
        b = b.csv(ctx.params.to_self_delay);
        Timelock::both(deadline, ctx.params.to_self_delay)
    } else {
        Timelock::cltv(deadline)
    };
    Leaf::new("settle", ctx.two_of_two(b).into_script(), tl)
}

/// The Split leaf for outcome `o` on `C'_d`: after `window` blocks, both
/// signatures, and the prover's code reveal must equal `o.code`.
/// Witness: `sig_U, sig_H, code reveal`.
pub fn split_leaf(ctx: &CommitCtx, o: &Outcome, window: u16, code: &PublicKey) -> Leaf {
    assert_eq!(code.n_bits(), CODE_BITS);
    let b = Builder::new().csv(window);
    let b = ctx.two_of_two_verify(b).expect_uint(code, u32::from(o.code)).push_opcode(OP_PUSHNUM_1);
    Leaf::new(format!("split_{}", o.name), b.into_script(), Timelock::csv(window))
}
