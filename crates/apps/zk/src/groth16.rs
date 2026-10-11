//! The Groth16 statement checked natively: what BitVMX's Groth16 verifier
//! program (FairgateLabs' bitvmx-zk-verifier, the ELF the disputes run)
//! decides on an input, in milliseconds instead of a 478M-step emulation.
//!
//! The program's input (`lngap-r0`'s `bitvmx::input`): the journal's
//! length in words (u32 LE), the image id, the proof's three points
//! compressed in Fairgate's convention (each x little-endian, the top bit
//! of its last byte set iff y is odd; B as x.c0 then x.c1, the flag from
//! y.c0), then the journal. The program accepts iff the points are a
//! Groth16 proof, under RISC Zero 3.0's verifying key, of the receipt
//! claim "the guest `image_id` halted with exit code 0 and wrote
//! `journal`", with RISC Zero 3.0's control root and BN254 control id: the
//! constants the ELF carries (it verifies 3.0 receipts unpatched).
//!
//! The verifying key, the control root and id, and the claim's hashing are
//! RISC Zero's (risc0-groth16 3.0.5, risc0-zkvm 3.0.6, risc0-binfmt 3.0.5;
//! Apache-2.0), reproduced here so the workspace needn't depend on RISC
//! Zero; the pairing is arkworks'.
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

/// RISC Zero 3.0's recursion control root (`ALLOWED_CONTROL_ROOT`).
pub const CONTROL_ROOT: &str = "a54dc85ac99f851c92d7c96d7318af41dbe7c0194edfcc37eb4d422a998c1f56";
/// RISC Zero 3.0's BN254 identity control id (`BN254_IDENTITY_CONTROL_ID`).
pub const BN254_CONTROL_ID: &str = "c07a65145c3cb48b6101962ea607a4dd93c753bb26975cb47feb00d3666e4404";

/// The verifying key (risc0-groth16 3.0.5, from risc0-ethereum's
/// Groth16Verifier.sol), as decimal coordinates; G2 coordinates as
/// `(c1, c0)`.
const ALPHA: [&str; 2] = ["20491192805390485299153009773594534940189261866228447918068658471970481763042", "9383485363053290200918347156157836566562967994039712273449902621266178545958"];
const BETA: [&str; 4] = [
    "4252822878758300859123897981450591353533073413197771768651442665752259397132",
    "6375614351688725206403948262868962793625744043794305715222011528459656738731",
    "21847035105528745403288232691147584728191162732299865338377159692350059136679",
    "10505242626370262277552901082094356697409835680220590971873171140371331206856",
];
const GAMMA: [&str; 4] = [
    "11559732032986387107991004021392285783925812861821192530917403151452391805634",
    "10857046999023057135944570762232829481370756359578518086990519993285655852781",
    "4082367875863433681332203403145435568316851327593401208105741076214120093531",
    "8495653923123431417604973247489272438418190587263600148770280649306958101930",
];
const DELTA: [&str; 4] = [
    "1668323501672964604911431804142266013250380587483576094566949227275849579036",
    "12043754404802191763554326994664886008979042643626290185762540825416902247219",
    "7710631539206257456743780535472368339139328733484942210876916214502466455394",
    "13740680757317479711909903993315946540841369848973133181051452051592786724563",
];
const IC: [[&str; 2]; 6] = [
    ["8446592859352799428420270221449902464741693648963397251242447530457567083492", "1064796367193003797175961162477173481551615790032213185848276823815288302804"],
    ["3179835575189816632597428042194253779818690147323192973511715175294048485951", "20895841676865356752879376687052266198216014795822152491318012491767775979074"],
    ["5332723250224941161709478398807683311971555792614491788690328996478511465287", "21199491073419440416471372042641226693637837098357067793586556692319371762571"],
    ["12457994489566736295787256452575216703923664299075106359829199968023158780583", "19706766271952591897761291684837117091856807401404423804318744964752784280790"],
    ["19617808913178163826953378459323299110911217259216006187355745713323154132237", "21663537384585072695701846972542344484111393047775983928357046779215877070466"],
    ["6834578911681792552110317589222010969491336870276623105249474534788043166867", "15060583660288623605191393599883223885678013570733629274538391874953353488393"],
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
fn public_inputs(claim: &[u8; 32]) -> [Fr; 5] {
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

/// Whether `points` (A, B, C compressed: 128 bytes) prove that the guest
/// `image_id` halted with exit code 0 and wrote `journal`.
pub fn verify(image_id: &[u8; 32], points: &[u8], journal: &[u8]) -> Result<()> {
    ensure!(points.len() == 128, "the proof is 128 bytes, not {}", points.len());
    let (a, b, c) = (g1(&points[..32])?, g2(&points[32..96])?, g1(&points[96..])?);
    let inputs = public_inputs(&claim_digest(image_id, journal));
    let mut vk_x = G1Projective::from(g1_const(IC[0]));
    for (x, ic) in inputs.iter().zip(&IC[1..]) {
        vk_x += g1_const(*ic) * x;
    }
    // e(A, B) = e(alpha, beta) e(vk_x, gamma) e(C, delta)
    let check = Bn254::multi_pairing([a, -g1_const(ALPHA), -vk_x.into_affine(), -c], [b, g2_const(BETA), g2_const(GAMMA), g2_const(DELTA)]);
    ensure!(check.0 == <Bn254 as Pairing>::TargetField::ONE, "the proof doesn't verify");
    Ok(())
}

/// What the verifier program decides on `input`: `Ok` iff it accepts.
pub fn verify_input(input: &[u8]) -> Result<()> {
    ensure!(input.len() >= 164, "an input of {} bytes", input.len());
    let n = u32::from_le_bytes(input[..4].try_into().unwrap()) as usize;
    ensure!(input.len() == 164 + 4 * n, "a journal of {n} words in an input of {} bytes", input.len());
    let image_id: [u8; 32] = input[4..36].try_into().unwrap();
    verify(&image_id, &input[36..164], &input[164..])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ln-gap's withdrawal guest: a return of 9 sats with memo 42.
    fn withdraw_9_42() -> Vec<u8> {
        hex::decode(include_str!("../../sessions/tests/data/withdraw-9-42.hex").trim()).unwrap()
    }

    /// The placeholder guest's receipt on (9, 42), as FairgateLabs'
    /// `proof-as-input` encodes it (lngap-r0's bitvmx.rs): the unpatched
    /// verifier ran it to Halt(0).
    const PLACEHOLDER: &str = "02000000c2bf393e7d9cbb53a5b6f0c1bc9767d42c04f632a9824a572eb7a5d6d77cd25055980d21b8181f697bec1fd16580c85509250218b39ecac0d3f2b8f55f456a1cd0838280b11c1fb7575a9a808d95d08a3431af29793cd1d444f0a9c6c56e3f109fcca45f4f0a79fe1dbf43f70bcd73560644f679d3852ab8fea067548d7c189d523bd82d59a760a5b05757fca4743552bb0717eb0be71a060e2b37877d343410090000002a000000";

    #[test]
    fn verifies_what_the_program_accepts() {
        for (name, input) in [("withdraw-9-42", withdraw_9_42()), ("placeholder", hex::decode(PLACEHOLDER).unwrap())] {
            let t = std::time::Instant::now();
            verify_input(&input).unwrap_or_else(|e| panic!("{name}: {e:#}"));
            println!("GROTH16 {name}: verified natively in {:.1?}", t.elapsed());
        }
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
