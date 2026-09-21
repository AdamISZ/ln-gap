//! The off-chain half: the attester's key, the per-epoch point table, and
//! attestation (revealing per-chunk scalars). All EC arithmetic happens here;
//! Script only ever sees the resulting points.

use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::key::{Keypair, XOnlyPublicKey};
use bitcoin::secp256k1::{PublicKey, Scalar, SecretKey, SECP256K1};

fn tagged(tag: &str, parts: &[&[u8]]) -> [u8; 32] {
    let th = sha256::Hash::hash(tag.as_bytes());
    let mut eng = sha256::Hash::engine();
    eng.input(th.as_ref());
    eng.input(th.as_ref());
    for p in parts {
        eng.input(p);
    }
    sha256::Hash::from_engine(eng).to_byte_array()
}

/// A hash-to-scalar with (practically unreachable) retry on out-of-range.
fn scalar(tag: &str, parts: &[&[u8]]) -> Scalar {
    for tries in 0u8.. {
        let t = [tries];
        let mut ps = parts.to_vec();
        ps.push(&t);
        if let Ok(s) = Scalar::from_be_bytes(tagged(tag, &ps)) {
            return s;
        }
    }
    unreachable!()
}

/// The one-time attester. In deployment this is a FROST quorum's group key
/// plus the members' share of each nonce; here a single secret plays both.
///
/// `fixed_r` is the nonce discipline (D38): the default derives one nonce
/// per (epoch, chunk, value) — an equivocation then yields the
/// possession-pair slash evidence and WOTS-style grafting but no key
/// extraction. `new_fixed_r` derives one nonce per (epoch, CHUNK), shared
/// across the chunk's sixteen values: a second value attested at the same
/// chunk reuses the nonce, the classic Schnorr/DLC same-R failure, and the
/// group key itself leaks to anyone holding both attestations
/// ([`extract_group_key`]). (The granularity must be the chunk, not the
/// slot: one R shared across ALL chunks of a slot would leak the key from
/// a single honest attestation — s_j - s_k = (e_j - e_k) * x.)
pub struct Attester {
    secret: SecretKey,
    group: XOnlyPublicKey,
    fixed_r: bool,
}

/// The committed point table of one epoch: `points[j][v]` is the anticipation
/// point for "chunk j has value v". One message per epoch, exactly the WOTS
/// one-time discipline; a second attestation in the same epoch is an
/// equivocation (see `slash_leaf`).
pub struct EpochTable {
    pub index: u64,
    pub chunks: usize,
    pub points: Vec<[XOnlyPublicKey; 16]>,
}

/// An attestation: one revealed scalar per chunk.
pub struct Attestation {
    pub secrets: Vec<SecretKey>,
}

impl Attester {
    pub fn new(seed: [u8; 32]) -> Attester {
        Self::with_discipline(seed, false)
    }

    /// The fixed-R-per-chunk variant: one nonce per (epoch, chunk), so an
    /// equivocation reuses it and leaks the group key (see the struct
    /// docs). The bond's burn path (D38) keys off this discipline.
    pub fn new_fixed_r(seed: [u8; 32]) -> Attester {
        Self::with_discipline(seed, true)
    }

    fn with_discipline(seed: [u8; 32], fixed_r: bool) -> Attester {
        let secret = SecretKey::from_slice(&tagged("ecwots/group", &[&seed]))
            .expect("tagged hash is a valid key");
        let kp = Keypair::from_secret_key(SECP256K1, &secret);
        Attester {
            secret,
            group: kp.x_only_public_key().0,
            fixed_r,
        }
    }

    pub fn group_key(&self) -> XOnlyPublicKey {
        self.group
    }

    /// The bond's burn-path commitment (D38): the hash mirror of the group
    /// SECRET, committed at bond setup — a slasher who extracts the key
    /// from an equivocation opens the burn leaf by revealing it.
    pub fn burn_mirror(&self) -> bitcoin::hashes::hash160::Hash {
        bitcoin::hashes::Hash::hash(&self.secret.secret_bytes())
    }

    /// The secret nonce of (epoch, chunk, value). Deterministic so the
    /// registry of nonce points can be reproduced; never revealed as such.
    /// Under the fixed-R discipline the nonce does not depend on the value:
    /// the chunk's sixteen values share one R.
    fn nonce(&self, epoch: u64, j: usize, v: u8) -> SecretKey {
        for tries in 0u8.. {
            let secret_b = self.secret.secret_bytes();
            let epoch_b = epoch.to_be_bytes();
            let j_b = (j as u64).to_be_bytes();
            let vb = [v];
            let tries_b = [tries];
            let mut parts: Vec<&[u8]> = vec![&secret_b, &epoch_b, &j_b];
            if !self.fixed_r {
                parts.push(&vb);
            }
            parts.push(&tries_b);
            if let Ok(r) = SecretKey::from_slice(&tagged("ecwots/nonce", &parts)) {
                return r;
            }
        }
        unreachable!()
    }

    /// The nonce POINT R of (epoch, chunk, value) — public registry data.
    /// The point table alone does not carry R; watchers need it for the
    /// fixed-R extraction (recomputing the challenges). Under fixed-R the
    /// point is the same for all sixteen values of the chunk.
    pub fn nonce_point(&self, epoch: u64, j: usize, v: u8) -> XOnlyPublicKey {
        Keypair::from_secret_key(SECP256K1, &self.nonce(epoch, j, v))
            .x_only_public_key()
            .0
    }

    /// e = H(R, P, stmt) for the chunk statement, in the anticipation-point
    /// identity S = R + e*P.
    fn challenge(&self, r_x: &XOnlyPublicKey, epoch: u64, j: usize, v: u8) -> Scalar {
        statement_challenge(&self.group, r_x, epoch, j, v)
    }

    /// The chunk's anticipation point S = R + H(R,P,stmt)*P (public data,
    /// committed per epoch by the registry / the leaf).
    pub fn chunk_point(&self, epoch: u64, j: usize, v: u8) -> XOnlyPublicKey {
        let r = self.nonce(epoch, j, v);
        let r_pt = PublicKey::from_secret_key(SECP256K1, &r);
        let (r_x, _) = r_pt.x_only_public_key();
        let e = self.challenge(&r_x, epoch, j, v);
        let p_full = PublicKey::from_secret_key(SECP256K1, &self.secret);
        let ep = p_full.mul_tweak(&SECP256K1, &e).expect("nonzero tweak");
        let s_pt = r_pt.combine(&ep).expect("nonzero sum");
        s_pt.x_only_public_key().0
    }

    /// The chunk secret s = r + e*x. Revealing it is the attestation to
    /// "chunk j has value v in this epoch".
    pub fn chunk_secret(&self, epoch: u64, j: usize, v: u8) -> SecretKey {
        let r = self.nonce(epoch, j, v);
        let (r_x, _) = Keypair::from_secret_key(SECP256K1, &r).x_only_public_key();
        let e = self.challenge(&r_x, epoch, j, v);
        let ex = self.secret.mul_tweak(&e).expect("nonzero product");
        r.add_tweak(&Scalar::from_be_bytes(ex.secret_bytes()).expect("in range"))
            .expect("nonzero sum")
    }

    /// The full point table of an epoch: `chunks` positions x 16 values.
    pub fn epoch_table(&self, index: u64, chunks: usize) -> EpochTable {
        EpochTable {
            index,
            chunks,
            points: (0..chunks)
                .map(|j| core::array::from_fn(|v| self.chunk_point(index, j, v as u8)))
                .collect(),
        }
    }

    /// Attest to `msg` (one chunk per nibble) under `table`'s epoch.
    pub fn attest(&self, table: &EpochTable, msg: &[u8]) -> Attestation {
        assert_eq!(msg.len() * 2, table.chunks, "one chunk per nibble");
        Attestation {
            secrets: (0..table.chunks)
                .map(|j| self.chunk_secret(table.index, j, crate::chunk_value(msg, j)))
                .collect(),
        }
    }
}

impl Attestation {
    /// Off-chain verification: each revealed secret opens its chunk point.
    /// (s*G == S, full-point equality, so x-only parity never enters.)
    pub fn verify(&self, table: &EpochTable, msg: &[u8]) -> bool {
        self.secrets.len() == table.chunks
            && (0..table.chunks).all(|j| {
                let kp = Keypair::from_secret_key(SECP256K1, &self.secrets[j]);
                kp.x_only_public_key().0 == table.points[j][crate::chunk_value(msg, j) as usize]
            })
    }
}

/// The chunk statement's challenge e = H(R, P, stmt), recomputed from
/// public data (the nonce point from the registry, the group key) — the
/// watcher's half of the fixed-R extraction.
pub fn statement_challenge(group: &XOnlyPublicKey, r_x: &XOnlyPublicKey, epoch: u64, j: usize, v: u8) -> Scalar {
    let stmt = format!("ecwots/{epoch}/{j}/{v}");
    scalar(
        "ecwots/challenge",
        &[&r_x.serialize(), &group.serialize(), stmt.as_bytes()],
    )
}

/// The secp256k1 group order minus two (the Fermat inversion exponent;
/// the group order is prime).
const N_MINUS_2: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48,
    0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x3F,
];

/// a^{-1} mod the group order, by Fermat: a^(n-2). Built only from
/// libsecp256k1's own modular multiply (`mul_tweak`) via square-and-
/// multiply — PoC-grade speed (~385 modmuls), no hand-rolled field math.
/// Tested against the mul_tweak roundtrip (table.rs tests).
fn scalar_inverse(a: &SecretKey) -> Result<SecretKey, secp256k1::Error> {
    let one = {
        let mut o = [0u8; 32];
        o[31] = 1;
        SecretKey::from_slice(&o).expect("1 is a valid key")
    };
    let mut result = one;
    for i in (0..256).rev() {
        let bit = (N_MINUS_2[31 - i / 8] >> (i % 8)) & 1;
        let r = Scalar::from_be_bytes(result.secret_bytes()).expect("a secret is in range");
        result = result.mul_tweak(&r)?; // square
        if bit == 1 {
            let a_s = Scalar::from_be_bytes(a.secret_bytes()).expect("a secret is in range");
            result = result.mul_tweak(&a_s)?; // multiply by a
        }
    }
    Ok(result)
}

/// The group key extracted from an equivocation under the fixed-R
/// discipline (D38): two secrets `s`, `s2` revealed at one chunk position
/// of one epoch for DIFFERENT values `v`, `v2` — the nonce was reused, so
/// s - s2 = (e - e2) * x. `r_x` is the chunk's nonce point (registry
/// data) and `group` the attester's group key — both public. Meaningful
/// only under `new_fixed_r`; under the default per-value nonces the two
/// equations have independent nonces and no such x exists.
pub fn extract_group_key(
    group: &XOnlyPublicKey,
    epoch: u64,
    j: usize,
    v: u8,
    v2: u8,
    r_x: &XOnlyPublicKey,
    s: &SecretKey,
    s2: &SecretKey,
) -> Result<SecretKey, secp256k1::Error> {
    assert_ne!(v, v2, "no equivocation at this chunk");
    let e = statement_challenge(group, r_x, epoch, j, v);
    let e2 = statement_challenge(group, r_x, epoch, j, v2);
    // ds = s - s2, de = e - e2 (the only arithmetic available on keys is
    // tweak ops: negate, add, multiply).
    let s2_neg = Scalar::from_be_bytes(s2.negate().secret_bytes()).expect("a secret is in range");
    let ds = s.add_tweak(&s2_neg)?;
    let e2_neg = Scalar::from_be_bytes(
        SecretKey::from_slice(&e2.to_be_bytes())
            .expect("a scalar is a valid key")
            .negate()
            .secret_bytes(),
    )
    .expect("a secret is in range");
    let de = SecretKey::from_slice(&e.to_be_bytes())
        .expect("a scalar is a valid key")
        .add_tweak(&e2_neg)?;
    let de_inv = scalar_inverse(&de)?;
    ds.mul_tweak(&Scalar::from_be_bytes(de_inv.secret_bytes()).expect("a secret is in range"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::hashes::Hash;

    #[test]
    fn scalar_inverse_roundtrips() {
        for seed in 1..=8u8 {
            let a = SecretKey::from_slice(&[seed.wrapping_mul(17).wrapping_add(3); 32]).unwrap();
            let inv = scalar_inverse(&a).unwrap();
            let prod = inv
                .mul_tweak(&Scalar::from_be_bytes(a.secret_bytes()).unwrap())
                .unwrap();
            let mut one = [0u8; 32];
            one[31] = 1;
            assert_eq!(prod.secret_bytes(), one, "inv(a) * a must be 1");
        }
        // edge: 1 inverts to itself
        let mut one = [0u8; 32];
        one[31] = 1;
        let one_sk = SecretKey::from_slice(&one).unwrap();
        assert_eq!(scalar_inverse(&one_sk).unwrap().secret_bytes(), one);
    }

    #[test]
    fn fixed_r_equivocation_leaks_the_group_key() {
        let att = Attester::new_fixed_r([0x42; 32]);
        let table = att.epoch_table(7, 8);
        // two 4-byte messages at epoch 7, differing at chunk 0
        let m1 = [0x10, 0, 0, 0];
        let m2 = [0x20, 0, 0, 0];
        let a1 = att.attest(&table, &m1);
        let a2 = att.attest(&table, &m2);
        assert!(a1.verify(&table, &m1) && a2.verify(&table, &m2));
        let j = 0;
        let (v1, v2) = (crate::chunk_value(&m1, j), crate::chunk_value(&m2, j));
        assert_ne!(v1, v2);
        // the fixed-R premise: the nonce point is shared across the chunk's values
        let r_x = att.nonce_point(7, j, v1);
        assert_eq!(r_x, att.nonce_point(7, j, v2), "fixed-R: one nonce per (epoch, chunk)");
        let x = extract_group_key(&att.group_key(), 7, j, v1, v2, &r_x, &a1.secrets[j], &a2.secrets[j]).unwrap();
        // the exact check: the extracted key opens the bond's burn mirror
        let mirror: bitcoin::hashes::hash160::Hash = bitcoin::hashes::Hash::hash(&x.secret_bytes());
        assert_eq!(mirror, att.burn_mirror(), "the extraction must recover the group key itself");
    }

    #[test]
    fn default_discipline_has_no_shared_nonce_to_extract_from() {
        let att = Attester::new([0x42; 32]);
        assert_ne!(
            att.nonce_point(7, 0, 1),
            att.nonce_point(7, 0, 2),
            "per-value nonces: no reuse, no extraction"
        );
        // and an honest single attestation under fixed-R reveals one secret
        // per chunk under DISTINCT chunk nonces: nothing to combine
        let att = Attester::new_fixed_r([0x42; 32]);
        assert_ne!(att.nonce_point(7, 0, 0), att.nonce_point(7, 1, 0));
    }
}
