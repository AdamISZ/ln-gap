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
    /// registry of nonce points can be reproduced; never revealed as such.
    fn nonce(&self, epoch: u64, j: usize, v: u8) -> SecretKey {
        for tries in 0u8.. {
            let b = tagged(
                "ecwots/nonce",
                &[
                    &self.secret.secret_bytes(),
                    &epoch.to_be_bytes(),
                    &(j as u64).to_be_bytes(),
                    &[v],
                    &[tries],
                ],
            );
            if let Ok(r) = SecretKey::from_slice(&b) {
                return r;
            }
        }
        unreachable!()
    }

    /// e = H(R, P, stmt) for the chunk statement, in the anticipation-point
    /// identity S = R + e*P.
    fn challenge(&self, r_x: &XOnlyPublicKey, epoch: u64, j: usize, v: u8) -> Scalar {
        let stmt = format!("ecwots/{epoch}/{j}/{v}");
        scalar(
            "ecwots/challenge",
            &[&r_x.serialize(), &self.group.serialize(), stmt.as_bytes()],
        )
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
