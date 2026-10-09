//! The input of BitVMX's Groth16 verifier program (FairgateLabs'
//! bitvmx-zk-verifier) for a Groth16 receipt: the journal's length in
//! 4-byte words (u32 LE), the image id, the proof's three points
//! compressed (A and C 32 bytes, B 64: arkworks' compressed BN254
//! serialization), the journal. The encoding of FairgateLabs'
//! `proof-as-input`, checked byte for byte against it in the tests.

use anyhow::{ensure, Result};
use ark_bn254::{Fq, Fq2, G1Affine, G2Affine};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;

fn fq(be: &[u8]) -> Fq {
    Fq::from_be_bytes_mod_order(be)
}

/// The proof's points compressed, from RISC Zero's 256-byte seal (A, B,
/// C; coordinates big-endian; B's in Fq2 imaginary part first).
pub fn compress_seal(seal: &[u8]) -> Result<Vec<u8>> {
    ensure!(seal.len() == 256, "a Groth16 seal is 256 bytes, not {}", seal.len());
    let w = |i: usize| &seal[32 * i..32 * (i + 1)];
    let a = G1Affine::new(fq(w(0)), fq(w(1)));
    let b = G2Affine::new(Fq2::new(fq(w(3)), fq(w(2))), Fq2::new(fq(w(5)), fq(w(4))));
    let c = G1Affine::new(fq(w(6)), fq(w(7)));
    let mut out = vec![];
    a.serialize_compressed(&mut out)?;
    b.serialize_compressed(&mut out)?;
    c.serialize_compressed(&mut out)?;
    Ok(out)
}

/// The verifier program's input.
pub fn input(image_id: &[u8; 32], seal: &[u8], journal: &[u8]) -> Result<Vec<u8>> {
    ensure!(journal.len().is_multiple_of(4), "the journal must be whole words");
    let mut out = ((journal.len() / 4) as u32).to_le_bytes().to_vec();
    out.extend_from_slice(image_id);
    out.extend(compress_seal(seal)?);
    out.extend_from_slice(journal);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A receipt of the placeholder guest on (9, 42), encoded by
    /// FairgateLabs' `proof-as-input` (the input the unpatched verifier ran
    /// to Halt(0)).
    const SEAL: &str = "1c6a455ff5b8f2d3c0ca9eb31802250955c88065d11fec7b691f18b8210d9855128d7fd898e6113182af26563e6efd40445a16a4bd3cdaa51c24647c933edb4c1d187c8d5467a0feb82a85d379f644065673cd0bf743bf1dfe790a4f5fa4cc9f103f6ec5c6a9f044d4d13c7929af31348ad0958d809a5a57b71f1cb1808283d02a926437b087dedb1c0a27ceab343029468584c20edee5954ba81aa0846e2c5806044b9bfbbc563a93d941cf9b21a482d734cf625ea31aff8a6f92d13c8cecdb1034347d87372b0e061ae70beb1707bb523574a4fc5757b0a560a7592dd83b520e14d5bc1097c394158e0158ca467e750c46bb93b6c9f7e1aa4d6ed0025860d2";
    const INPUT: &str = "02000000c2bf393e7d9cbb53a5b6f0c1bc9767d42c04f632a9824a572eb7a5d6d77cd25055980d21b8181f697bec1fd16580c85509250218b39ecac0d3f2b8f55f456a1cd0838280b11c1fb7575a9a808d95d08a3431af29793cd1d444f0a9c6c56e3f109fcca45f4f0a79fe1dbf43f70bcd73560644f679d3852ab8fea067548d7c189d523bd82d59a760a5b05757fca4743552bb0717eb0be71a060e2b37877d343410090000002a000000";

    #[test]
    fn matches_fairgates_encoding() {
        let id: [u8; 32] = hex::decode("c2bf393e7d9cbb53a5b6f0c1bc9767d42c04f632a9824a572eb7a5d6d77cd250").unwrap().try_into().unwrap();
        let got = input(&id, &hex::decode(SEAL).unwrap(), &[9, 0, 0, 0, 42, 0, 0, 0]).unwrap();
        assert_eq!(hex::encode(got), INPUT);
    }
}
