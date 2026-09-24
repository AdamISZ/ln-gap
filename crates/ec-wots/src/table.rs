//! The off-chain half: the attester's key, the per-epoch point table, and
//! attestation (revealing per-chunk scalars). All EC arithmetic happens here;
//! Script only ever sees the resulting points.

use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::key::{Keypair, Parity, XOnlyPublicKey};
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
/// Nonce discipline (D47): one nonce per (epoch, chunk, VALUE). An honest
/// attestation opens one value per chunk under that value's nonce; an
/// equivocation opens two values at some chunk under two DIFFERENT nonces,
/// so the pair is evidence (two possession secrets at one position — what
/// `slash_leaf_any` checks) but nothing leaks, neither the group key nor a
/// share. The former "fixed-R" variant (D38: one nonce per (epoch, chunk)
/// shared by the sixteen values, so that an equivocation leaked the group
/// key for a hash-mirror burn leaf) was dropped by D47: a public group key
/// lets every in-flight contract's staller forge an attestation of its own
/// never-published move, and the evidence pair needs no leak.
pub struct Attester {
    secret: SecretKey,
    group: XOnlyPublicKey,
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
        let secret = SecretKey::from_slice(&tagged("ecwots/group", &[&seed]))
            .expect("tagged hash is a valid key");
        let kp = Keypair::from_secret_key(SECP256K1, &secret);
        Attester {
            secret,
            group: kp.x_only_public_key().0,
        }
    }

    pub fn group_key(&self) -> XOnlyPublicKey {
        self.group
    }

    /// The secret nonce of (epoch, chunk, value). Deterministic so the
    /// registry of points can be reproduced; never revealed as such.
    fn nonce(&self, epoch: u64, j: usize, v: u8) -> SecretKey {
        for tries in 0u8.. {
            let secret_b = self.secret.secret_bytes();
            let epoch_b = epoch.to_be_bytes();
            let j_b = (j as u64).to_be_bytes();
            let vb = [v];
            let tries_b = [tries];
            let parts: Vec<&[u8]> = vec![&secret_b, &epoch_b, &j_b, &vb, &tries_b];
            if let Ok(r) = SecretKey::from_slice(&tagged("ecwots/nonce", &parts)) {
                return r;
            }
        }
        unreachable!()
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
    /// "chunk j has value v in this epoch". Normalised so that s*G has EVEN
    /// y (s is negated otherwise): the table stores x-only points, and with
    /// this normalisation the point of a revealed secret is exactly the
    /// table point lifted to even y — which is what makes sums of secrets
    /// correspond to sums of table points ([`EpochTable::point_sum`],
    /// [`Attestation::scalar_sum`], the fee lock of ATTESTATION_FEES.md).
    /// BIP340 signatures under the x-only point are unaffected.
    pub fn chunk_secret(&self, epoch: u64, j: usize, v: u8) -> SecretKey {
        let r = self.nonce(epoch, j, v);
        let (r_x, _) = Keypair::from_secret_key(SECP256K1, &r).x_only_public_key();
        let e = self.challenge(&r_x, epoch, j, v);
        let ex = self.secret.mul_tweak(&e).expect("nonzero product");
        let s = r
            .add_tweak(&Scalar::from_be_bytes(ex.secret_bytes()).expect("in range"))
            .expect("nonzero sum");
        match PublicKey::from_secret_key(SECP256K1, &s).x_only_public_key().1 {
            Parity::Even => s,
            Parity::Odd => s.negate(),
        }
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

impl EpochTable {
    /// The sum of the anticipation points selected by `msg` over the chunk
    /// positions `chunks` (each x-only point lifted to even y — the
    /// normalisation of [`Attester::chunk_secret`]). Its discrete log is
    /// the sum of the secrets an attestation of exactly `msg` reveals at
    /// those positions, and nothing else: the fee lock's adaptor point
    /// ("pay iff you attest exactly this head", ATTESTATION_FEES.md). `msg`
    /// is indexed from `chunks.start` (nibble `k` of `msg` is chunk
    /// `chunks.start + k`).
    pub fn point_sum(&self, msg: &[u8], chunks: std::ops::Range<usize>) -> PublicKey {
        assert_eq!(msg.len() * 2, chunks.len(), "one chunk per nibble of msg");
        let mut acc: Option<PublicKey> = None;
        for (k, j) in chunks.enumerate() {
            let v = crate::chunk_value(msg, k) as usize;
            let pt = PublicKey::from_x_only_public_key(self.points[j][v], Parity::Even);
            acc = Some(match acc {
                None => pt,
                Some(a) => a.combine(&pt).expect("a sum of distinct anticipation points is not the identity"),
            });
        }
        acc.expect("at least one chunk")
    }
}

impl Attestation {
    /// Off-chain verification: each revealed secret opens its chunk point.
    /// (x-only equality; the secrets are even-y normalised, see
    /// [`Attester::chunk_secret`].)
    pub fn verify(&self, table: &EpochTable, msg: &[u8]) -> bool {
        self.secrets.len() == table.chunks
            && (0..table.chunks).all(|j| {
                let kp = Keypair::from_secret_key(SECP256K1, &self.secrets[j]);
                kp.x_only_public_key().0 == table.points[j][crate::chunk_value(msg, j) as usize]
            })
    }

    /// The sum of the revealed secrets over the chunk positions `chunks`:
    /// the discrete log of [`EpochTable::point_sum`] for the attested
    /// message — the adaptor secret that completes a fee lock.
    pub fn scalar_sum(&self, chunks: std::ops::Range<usize>) -> SecretKey {
        let mut acc: Option<SecretKey> = None;
        for j in chunks {
            let s = self.secrets[j];
            acc = Some(match acc {
                None => s,
                Some(a) => a
                    .add_tweak(&Scalar::from_be_bytes(s.secret_bytes()).expect("a secret is in range"))
                    .expect("a sum of distinct secrets is not zero"),
            });
        }
        acc.expect("at least one chunk")
    }
}

/// The chunk statement's challenge e = H(R, P, stmt) in the anticipation
/// point identity S = R + e*P, from public data (the nonce point, the
/// group key).
pub fn statement_challenge(group: &XOnlyPublicKey, r_x: &XOnlyPublicKey, epoch: u64, j: usize, v: u8) -> Scalar {
    let stmt = format!("ecwots/{epoch}/{j}/{v}");
    scalar(
        "ecwots/challenge",
        &[&r_x.serialize(), &group.serialize(), stmt.as_bytes()],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn per_value_nonces_and_even_y_secrets() {
        let att = Attester::new([0x42; 32]);
        let table = att.epoch_table(7, 8);
        // two 4-byte messages at epoch 7, differing at chunk 0
        let m1 = [0x10, 0, 0, 0];
        let m2 = [0x20, 0, 0, 0];
        let a1 = att.attest(&table, &m1);
        let a2 = att.attest(&table, &m2);
        assert!(a1.verify(&table, &m1) && a2.verify(&table, &m2));
        // per-value nonces: the two values' points at chunk 0 are unrelated
        assert_ne!(table.points[0][1], table.points[0][2]);
        // every revealed secret's point has even y (the normalisation)
        for s in a1.secrets.iter().chain(a2.secrets.iter()) {
            assert_eq!(PublicKey::from_secret_key(SECP256K1, s).x_only_public_key().1, Parity::Even);
        }
    }

    /// The fee lock's algebra: the sum of the secrets an attestation of
    /// exactly `msg` reveals is the log of the sum of `msg`'s table points,
    /// and a different message's secrets are not.
    #[test]
    fn scalar_sum_opens_point_sum() {
        let att = Attester::new([0x43; 32]);
        let table = att.epoch_table(3, 16);
        let m = [0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x23, 0x45, 0x67];
        let m2 = [0xDE, 0xAD, 0xBE, 0xEF, 0x01, 0x23, 0x45, 0x68];
        let t_pt = table.point_sum(&m, 0..16);
        let t = att.attest(&table, &m).scalar_sum(0..16);
        assert_eq!(PublicKey::from_secret_key(SECP256K1, &t), t_pt);
        let t2 = att.attest(&table, &m2).scalar_sum(0..16);
        assert_ne!(PublicKey::from_secret_key(SECP256K1, &t2), t_pt, "a different head's secrets do not open the lock");
        // a sub-range (the head region of a header) sums the same way
        let t_pt = table.point_sum(&m[2..6], 4..12);
        let t = att.attest(&table, &m).scalar_sum(4..12);
        assert_eq!(PublicKey::from_secret_key(SECP256K1, &t), t_pt);
    }
}
