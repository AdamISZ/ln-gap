//! The Groth16 statement checked natively: what BitVMX's Groth16 verifier
//! program (FairgateLabs' bitvmx-zk-verifier, the ELF the disputes run)
//! decides on an input, in milliseconds instead of a 478M-step emulation.
//!
//! The program's input (`lngap-r0`'s `bitvmx::input`): the journal's
//! length in words (u32 LE), the image id, the proof's three points
//! compressed in Fairgate's convention (each x little-endian, the top bit
//! of its last byte set iff y is odd; B as x.c0 then x.c1, the flag from
//! y.c0), then the journal. The program accepts iff the points are a
//! Groth16 proof, under RISC Zero 3.1's verifying key, of the receipt
//! claim "the guest `image_id` halted with exit code 0 and wrote
//! `journal`", with RISC Zero 3.1's control root and BN254 control id.
//!
//! The ELF as BitVMX-CPU ships it carries RISC Zero 3.0's key and
//! constants; [`verifier_elf`] writes this module's into a copy of it, the
//! program the disputes run.
//!
//! The verifying key, the control root and id, and the claim's hashing are
//! RISC Zero's (risc0-groth16 3.0.6, risc0-circuit-recursion 4.1.0,
//! risc0-zkvm 3.1.0, risc0-binfmt 3.0.6; Apache-2.0), reproduced here so
//! the workspace needn't depend on RISC Zero; the pairing is arkworks'.
//!
//! The emulation stays the authority in a dispute (the trace is what the
//! search commits to); this answers the question that comes first: does
//! the program accept?

use anyhow::{ensure, Context, Result};
use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField};
use sha2::{Digest as _, Sha256};
use std::str::FromStr;

/// RISC Zero 3.1's recursion control root (`ALLOWED_CONTROL_ROOT`).
pub const CONTROL_ROOT: &str = "e6feef13db7aed4a731c7b0852de1f5c89b137726073f625d05333184d3a551d";
/// RISC Zero 3.1's BN254 identity control id (`BN254_IDENTITY_CONTROL_ID`).
pub const BN254_CONTROL_ID: &str = "de81d091ba14062acb5023b3b36deee95624e3fd47475cb7ff64aed5f9eac20a";

/// The verifying key of RISC Zero 3.1's Groth16 circuit (risc0-groth16
/// 3.0.6, from risc0-ethereum's Groth16Verifier.sol), as decimal
/// coordinates; G2 coordinates as `(c1, c0)`.
const ALPHA: [&str; 2] = ["16428432848801857252194528405604668803277877773566238944394625302971855135431", "16846502678714586896801519656441059708016666274385668027902869494772365009666"];
const BETA: [&str; 4] = [
    "3182164110458002340215786955198810119980427837186618912744689678939861918171",
    "16348171800823588416173124589066524623406261996681292662100840445103873053252",
    "4920802715848186258981584729175884379674325733638798907835771393452862684714",
    "19687132236965066906216944365591810874384658708175106803089633851114028275753",
];
const GAMMA: [&str; 4] = [
    "11559732032986387107991004021392285783925812861821192530917403151452391805634",
    "10857046999023057135944570762232829481370756359578518086990519993285655852781",
    "4082367875863433681332203403145435568316851327593401208105741076214120093531",
    "8495653923123431417604973247489272438418190587263600148770280649306958101930",
];
const DELTA: [&str; 4] = [
    "15616655295497688016920922285786248029410410634174255119755032442279507261612",
    "15776672394616990683767400715354533957990327248900631669473166016258279232588",
    "15603769682755083227316504195454390494226357053638046843688553601570183264395",
    "6666730711543397578682474175129345128534747409410156889826997147291122518312",
];
const IC: [[&str; 2]; 6] = [
    ["18663918579753010382002747204100316475180663666125247285366810668134508578264", "17189072794432247265173990289507014998311702955803346313941168113828133843434"],
    ["10995657406716404592042449088731908804822551193011116024160605390904112699922", "16840054500543522560166231854936072122401577171365452702445604851845250658027"],
    ["17223746139751910493708334502747005647365937123243899090309734281916083451762", "4092210736358501801028887881307062309243791997444282548134854129284894411044"],
    ["3765213192101990618643617040373059738050185238026301923348610794767426428033", "12210223264334159465299028585581460715942724522871187397965100355295734194591"],
    ["10211980968769599651826920300372241897389214017084266564307091587192484525770", "6627619408770540710319105693121261544533216204749218194792386277379533604252"],
    ["13454640350766589059799184485082639692652215534373479852236969801352010275184", "8731676129773990833613417922371950977268622282768299686490610454524284784606"],
];

fn sha256(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}

/// RISC Zero's tagged struct hash (`risc0_binfmt::tagged_struct`).
fn tagged(tag: &str, down: &[[u8; 32]], data: &[u32]) -> [u8; 32] {
    let mut all = sha256(tag.as_bytes()).to_vec();
    for d in down {
        all.extend_from_slice(d);
    }
    for w in data {
        all.extend_from_slice(&w.to_le_bytes());
    }
    all.extend_from_slice(&(down.len() as u16).to_le_bytes());
    sha256(&all)
}

/// The digest of RISC Zero's receipt claim for a guest that halted with
/// exit code 0 (`ReceiptClaim::ok(image_id, journal)`): its input none,
/// its pre-state pruned to the image id, its post-state at pc 0 with a
/// zero root, its output the journal with no assumptions.
pub fn claim_digest(image_id: &[u8; 32], journal: &[u8]) -> [u8; 32] {
    let zero = [0u8; 32];
    let post = tagged("risc0.SystemState", &[zero], &[0]);
    let output = tagged("risc0.Output", &[sha256(journal), zero], &[]);
    tagged("risc0.ReceiptClaim", &[zero, *image_id, post, output], &[0, 0])
}

/// The proof's public inputs: the control root's halves, the claim's
/// halves (each half a little-endian integer), the BN254 control id
/// (likewise).
pub fn public_inputs(claim: &[u8; 32]) -> [Fr; 5] {
    let root = hex::decode(CONTROL_ROOT).expect("hex");
    let id = hex::decode(BN254_CONTROL_ID).expect("hex");
    let le = Fr::from_le_bytes_mod_order;
    [le(&root[..16]), le(&root[16..]), le(&claim[..16]), le(&claim[16..]), le(&id)]
}

fn dec(s: &str) -> Fq {
    Fq::from_str(s).ok().expect("a field element")
}

fn g1_const(c: [&str; 2]) -> G1Affine {
    G1Affine::new(dec(c[0]), dec(c[1]))
}

fn g2_const(c: [&str; 4]) -> G2Affine {
    G2Affine::new(Fq2::new(dec(c[1]), dec(c[0])), Fq2::new(dec(c[3]), dec(c[2])))
}

/// RISC Zero 3.1's verifying key, as points: `ic` the public inputs'
/// bases, the constant's first.
pub struct Key {
    pub alpha: G1Affine,
    pub beta: G2Affine,
    pub gamma: G2Affine,
    pub delta: G2Affine,
    pub ic: [G1Affine; 6],
}

pub fn key() -> Key {
    Key { alpha: g1_const(ALPHA), beta: g2_const(BETA), gamma: g2_const(GAMMA), delta: g2_const(DELTA), ic: IC.map(g1_const) }
}

/// A Groth16 proof's points.
pub struct Proof {
    pub a: G1Affine,
    pub b: G2Affine,
    pub c: G1Affine,
}

/// A base field element from 32 little-endian bytes, below the modulus.
fn fq_le(b: &[u8]) -> Result<Fq> {
    let x = Fq::from_le_bytes_mod_order(b);
    ensure!(x.into_bigint().to_bytes_le() == b, "a coordinate beyond the field");
    Ok(x)
}

fn odd(y: Fq) -> bool {
    y.into_bigint().is_odd()
}

/// A G1 point from 32 bytes in Fairgate's convention.
fn g1(b: &[u8]) -> Result<G1Affine> {
    let mut x = b.to_vec();
    let flag = x[31] & 0x80 != 0;
    x[31] &= 0x7f;
    let x = fq_le(&x)?;
    let (y, minus) = G1Affine::get_ys_from_x_unchecked(x).context("a G1 x off the curve")?;
    let p = G1Affine::new_unchecked(x, if odd(y) == flag { y } else { minus });
    ensure!(p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve(), "not a G1 point");
    Ok(p)
}

/// A G2 point from 64 bytes in Fairgate's convention.
fn g2(b: &[u8]) -> Result<G2Affine> {
    let mut c1 = b[32..].to_vec();
    let flag = c1[31] & 0x80 != 0;
    c1[31] &= 0x7f;
    let x = Fq2::new(fq_le(&b[..32])?, fq_le(&c1)?);
    let (y, minus) = G2Affine::get_ys_from_x_unchecked(x).context("a G2 x off the curve")?;
    let p = G2Affine::new_unchecked(x, if odd(y.c0) == flag { y } else { minus });
    ensure!(p.is_on_curve() && p.is_in_correct_subgroup_assuming_on_curve(), "not a G2 point");
    Ok(p)
}

/// The points of a proof compressed (A, B, C: 128 bytes).
pub fn decode(points: &[u8]) -> Result<Proof> {
    ensure!(points.len() == 128, "the proof is 128 bytes, not {}", points.len());
    Ok(Proof { a: g1(&points[..32])?, b: g2(&points[32..96])?, c: g1(&points[96..])? })
}

/// Whether `points` (A, B, C compressed: 128 bytes) prove that the guest
/// `image_id` halted with exit code 0 and wrote `journal`.
pub fn verify(image_id: &[u8; 32], points: &[u8], journal: &[u8]) -> Result<()> {
    let Proof { a, b, c } = decode(points)?;
    let k = key();
    let inputs = public_inputs(&claim_digest(image_id, journal));
    let mut vk_x = G1Projective::from(k.ic[0]);
    for (x, ic) in inputs.iter().zip(&k.ic[1..]) {
        vk_x += *ic * x;
    }
    // e(A, B) = e(alpha, beta) e(vk_x, gamma) e(C, delta)
    let check = Bn254::multi_pairing([a, -k.alpha, -vk_x.into_affine(), -c], [b, k.beta, k.gamma, k.delta]);
    ensure!(check.0 == <Bn254 as Pairing>::TargetField::ONE, "the proof doesn't verify");
    Ok(())
}

/// The verifier program's input split: the image id, the proof's points
/// (compressed, 128 bytes), the journal.
pub fn split_input(input: &[u8]) -> Result<([u8; 32], &[u8], &[u8])> {
    ensure!(input.len() >= 164, "an input of {} bytes", input.len());
    let n = u32::from_le_bytes(input[..4].try_into().unwrap()) as usize;
    ensure!(input.len() == 164 + 4 * n, "a journal of {n} words in an input of {} bytes", input.len());
    Ok((input[4..36].try_into().unwrap(), &input[36..164], &input[164..]))
}

/// What the verifier program decides on `input`: `Ok` iff it accepts.
pub fn verify_input(input: &[u8]) -> Result<()> {
    let (image_id, points, journal) = split_input(input)?;
    verify(&image_id, points, journal)
}

/// SHA-256 of BitVMX's Groth16 verifier as BitVMX-CPU ships it
/// (`docker-riscv32/verifier/build/zkverifier-new-mul.elf`, GPL-3.0, not
/// vendored), built with RISC Zero 3.0's key and constants.
pub const SHIPPED_ELF_SHA256: &str = "2b96e192300ab938b918a860b5bdf5f72a066e0e4688fdf7efc32228d6915598";
/// SHA-256 of [`verifier_elf`]'s result: the shipped ELF carrying this
/// module's key and constants.
pub const VERIFIER_ELF_SHA256: &str = "2dc582f3107ca69059342d07fcc18302f65b1f89431e837df2a12f8848741c42";

/// Where the shipped ELF keeps its constants (file offsets of its
/// symbols): the key in `.rodata` (`BYTES_ALPHA`, `BYTES_BETA`,
/// `BYTES_GAMMA`, `BYTES_DELTA`, `BYTES_GAMMA_ABC`: 416 bytes, each point
/// compressed as a proof's are), and in `.data` the public-input table
/// (`BYTES_PUBLIC_INPUTS`: five 32-byte inputs, the control root's halves
/// first and second, the BN254 control id fifth).
const ELF_KEY_AT: usize = 0xb0000;
const ELF_INPUTS_AT: usize = 0xaf004;

/// A G1 point as 32 bytes in Fairgate's convention (`g1`'s inverse).
fn g1_bytes(p: &G1Affine) -> [u8; 32] {
    let mut b: [u8; 32] = p.x.into_bigint().to_bytes_le().try_into().expect("32 bytes");
    b[31] |= if odd(p.y) { 0x80 } else { 0 };
    b
}

/// A G2 point as 64 bytes in Fairgate's convention (`g2`'s inverse).
fn g2_bytes(p: &G2Affine) -> [u8; 64] {
    let mut b = [0u8; 64];
    b[..32].copy_from_slice(&p.x.c0.into_bigint().to_bytes_le());
    b[32..].copy_from_slice(&p.x.c1.into_bigint().to_bytes_le());
    b[63] |= if odd(p.y.c0) { 0x80 } else { 0 };
    b
}

/// The key as the verifier program stores it.
fn key_bytes() -> Vec<u8> {
    let k = key();
    let mut b = g1_bytes(&k.alpha).to_vec();
    for p in [k.beta, k.gamma, k.delta] {
        b.extend(g2_bytes(&p));
    }
    for p in k.ic {
        b.extend(g1_bytes(&p));
    }
    b
}

/// Writes this module's key and constants where the verifier program
/// keeps its own.
fn write_constants(elf: &mut [u8]) {
    let key = key_bytes();
    elf[ELF_KEY_AT..ELF_KEY_AT + key.len()].copy_from_slice(&key);
    let root = hex::decode(CONTROL_ROOT).expect("hex");
    let id = hex::decode(BN254_CONTROL_ID).expect("hex");
    let at = ELF_INPUTS_AT;
    elf[at..at + 16].copy_from_slice(&root[..16]);
    elf[at + 32..at + 48].copy_from_slice(&root[16..]);
    elf[at + 128..at + 160].copy_from_slice(&id);
}

/// The verifier ELF as BitVMX-CPU ships it, from Cargo's checkout of
/// BitVMX-CPU (a git dependency of this crate): the first copy under
/// `$CARGO_HOME/git/checkouts` whose hash is [`SHIPPED_ELF_SHA256`].
pub fn shipped_verifier_elf() -> Result<Vec<u8>> {
    let home = match std::env::var_os("CARGO_HOME") {
        Some(h) => std::path::PathBuf::from(h),
        None => std::path::PathBuf::from(std::env::var_os("HOME").context("neither CARGO_HOME nor HOME is set")?).join(".cargo"),
    };
    let checkouts = home.join("git/checkouts");
    for repo in std::fs::read_dir(&checkouts).with_context(|| format!("reading {}", checkouts.display()))?.flatten() {
        if !repo.file_name().to_string_lossy().starts_with("bitvmx-cpu-") {
            continue;
        }
        for rev in std::fs::read_dir(repo.path())?.flatten() {
            let Ok(elf) = std::fs::read(rev.path().join("docker-riscv32/verifier/build/zkverifier-new-mul.elf")) else { continue };
            if hex::encode(sha256(&elf)) == SHIPPED_ELF_SHA256 {
                return Ok(elf);
            }
        }
    }
    anyhow::bail!("no BitVMX-CPU checkout under {} holds the verifier ELF", checkouts.display())
}

/// BitVMX's Groth16 verifier program deciding as [`verify_input`] does:
/// the ELF BitVMX-CPU ships (`shipped`, checked against
/// [`SHIPPED_ELF_SHA256`]) with this module's key and constants written
/// over 3.0's. Like the shipped ELF, the result is GPL-3.0: don't commit it.
pub fn verifier_elf(shipped: &[u8]) -> Result<Vec<u8>> {
    ensure!(hex::encode(sha256(shipped)) == SHIPPED_ELF_SHA256, "not the verifier ELF BitVMX-CPU ships");
    let mut elf = shipped.to_vec();
    write_constants(&mut elf);
    ensure!(hex::encode(sha256(&elf)) == VERIFIER_ELF_SHA256, "the patched verifier's hash is unexpected");
    Ok(elf)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ln-gap's withdrawal guest, the previous statement: a return of 9
    /// sats with memo 42.
    fn withdraw_9_42() -> Vec<u8> {
        hex::decode(include_str!("../../sessions/tests/data/withdraw-9-42.hex").trim()).unwrap()
    }

    /// The current statement, on the toy deployment's return of 9 with memo 42.
    fn withdraw_9_42_deployment() -> Vec<u8> {
        hex::decode(include_str!("../../sessions/tests/data/withdraw-9-42-deployment.hex").trim()).unwrap()
    }

    /// The placeholder guest's receipt on (9, 42) under RISC Zero 3.0, as
    /// FairgateLabs' `proof-as-input` encodes it (lngap-r0's bitvmx.rs):
    /// the shipped verifier ran it to Halt(0).
    const PLACEHOLDER_R0_3_0: &str = "02000000c2bf393e7d9cbb53a5b6f0c1bc9767d42c04f632a9824a572eb7a5d6d77cd25055980d21b8181f697bec1fd16580c85509250218b39ecac0d3f2b8f55f456a1cd0838280b11c1fb7575a9a808d95d08a3431af29793cd1d444f0a9c6c56e3f109fcca45f4f0a79fe1dbf43f70bcd73560644f679d3852ab8fea067548d7c189d523bd82d59a760a5b05757fca4743552bb0717eb0be71a060e2b37877d343410090000002a000000";

    #[test]
    fn verifies_what_the_program_accepts() {
        for (name, input) in [("withdraw-9-42", withdraw_9_42()), ("withdraw-9-42-deployment", withdraw_9_42_deployment())] {
            let t = std::time::Instant::now();
            verify_input(&input).unwrap_or_else(|e| panic!("{name}: {e:#}"));
            println!("GROTH16 {name}: verified natively in {:.1?}", t.elapsed());
        }
    }

    #[test]
    fn rejects_a_receipt_made_under_risc_zero_3_0() {
        assert!(verify_input(&hex::decode(PLACEHOLDER_R0_3_0).unwrap()).is_err(), "a 3.0 receipt verifies under 3.1's key");
    }

    /// The key and constants read back from where the program keeps them,
    /// through the decoders a proof's points go through.
    #[test]
    fn writes_the_constants_where_the_program_reads_them() {
        let mut elf = vec![0u8; ELF_KEY_AT + 416];
        write_constants(&mut elf);
        let (b, k) = (&elf[ELF_KEY_AT..], key());
        assert_eq!(g1(&b[..32]).unwrap(), k.alpha);
        assert_eq!(g2(&b[32..96]).unwrap(), k.beta);
        assert_eq!(g2(&b[96..160]).unwrap(), k.gamma);
        assert_eq!(g2(&b[160..224]).unwrap(), k.delta);
        for (i, ic) in k.ic.iter().enumerate() {
            assert_eq!(&g1(&b[224 + 32 * i..256 + 32 * i]).unwrap(), ic, "IC{i}");
        }
        let (t, root) = (&elf[ELF_INPUTS_AT..ELF_INPUTS_AT + 160], hex::decode(CONTROL_ROOT).unwrap());
        assert_eq!([&t[..16], &t[32..48]].concat(), root);
        assert_eq!(hex::encode(&t[128..]), BN254_CONTROL_ID);
        assert!(t[16..32].iter().chain(&t[48..128]).all(|&x| x == 0), "the other inputs stay as the program sets them");
    }

    /// The shipped ELF takes the key and constants and changes nowhere
    /// else.
    #[test]
    fn patches_the_shipped_verifier() {
        let shipped = shipped_verifier_elf().unwrap();
        let elf = verifier_elf(&shipped).unwrap();
        let patched = |i: usize| (ELF_KEY_AT..ELF_KEY_AT + 416).contains(&i) || (ELF_INPUTS_AT..ELF_INPUTS_AT + 160).contains(&i);
        assert_eq!(elf.len(), shipped.len());
        assert!(elf.iter().zip(&shipped).enumerate().all(|(i, (a, b))| a == b || patched(i)), "a byte changed outside the constants");
    }

    #[test]
    fn rejects_what_it_doesnt() {
        let good = withdraw_9_42();
        let edit = |at: usize, x: u8| {
            let mut v = good.clone();
            v[at] ^= x;
            v
        };
        // b (the journal's first word), the image id, each point's x and
        // flag, the journal's length
        for (what, input) in [("b", edit(164, 3)), ("the image id", edit(4, 1)), ("A", edit(36, 1)), ("A's flag", edit(67, 0x80)), ("B", edit(68, 1)), ("B's flag", edit(131, 0x80)), ("C", edit(132, 1)), ("the length", edit(0, 1))] {
            assert!(verify_input(&input).is_err(), "{what} changed, yet it verifies");
        }
    }
}
