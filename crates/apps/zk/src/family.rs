//! `Game::Zk` in the PoS graph (Z3 step 6): the search game's leaves
//! (D60, D61) behind `lngap_pos::ext::Family`.
//!
//! - depth 1: `zk_claim`; verifier depths: `zk_choice`; prover depths
//!   below the last: `zk_copied`;
//! - the last depth (2R + 1): the claimant's final disproves (S1/S2,
//!   `zk_record_step`, the halt pair, `zk_input_<j>`), and the prover's
//!   `zk_prove_<class>` for each instruction class the program's code has
//!   (a step of any other class fails the opcode disprove);
//! - the venue's check: the head's state-key signature (head bytes 4..48,
//!   as blackjack's), the body opening the head's digests (D60), and at
//!   depth 1 the input words each signed (D61);
//! - the read challenge (D62): the verifier's opening at 2R + 2
//!   (`zk_open`), R more rounds, the prover's terminal move at 4R + 3 with
//!   BitVMX's `zk_read_value_<r>` and `zk_correct_hash`; the instance runs
//!   to 4R + 3, the proof still due at 2R + 1;
//! - the input keys' equivocation leaves; `settle` pays the prover.
//!
//! An entry is the head, the state key's signature elements (20 bytes
//! each), then the body: the state block, then the claim block (depth 1)
//! or the record (the last depth), then at depth 1 each input word (4
//! bytes, big-endian) and its signature elements.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};

use bitcoin::ScriptBuf;
use bitcoin_script_riscv::riscv::instruction_mapping::{generate_verification_script, requires_witness};
use lngap_channel::Role;
use lngap_lamport::winternitz::{WotsPublic, WotsSig};
use lngap_pos::instance::mover_at;
use lngap_pos::ttt::{Layout, PosLeaf};

use crate::challenges::ProgramInfo;
use crate::final_d60::{final_leaves, input_key_params, input_leaves, input_message, input_signed};
use crate::game::{prove_script_d60, Search, BLOCK};
use crate::{guard, BASE_REGISTER_ADDRESS, HEAD_BYTES};

/// The search game's family for one contract.
pub struct ZkFamily {
    pub search: Search,
    pub info: ProgramInfo,
    /// The prover's input keys, one per input word (D61).
    pub input_keys: Vec<WotsPublic>,
    /// One (opcode, micro-step) sample per instruction class in the code.
    pub classes: BTreeMap<String, (u32, u8)>,
    /// Built leaf scripts, per (depth, rebuttal key): they depend on nothing
    /// else, while a graph is rebuilt per commitment version and per side
    /// (and builds most depths' rebuttal trees twice, under the claim and
    /// the counter). The context-dependent prefixes are added around them
    /// by the graph, outside the cache.
    cache: Mutex<Cache>,
}

#[derive(Default)]
struct Cache {
    disproves: HashMap<(u32, [u8; 32]), Arc<Vec<(String, ScriptBuf)>>>,
    proofs: HashMap<(u32, [u8; 32]), Arc<Vec<(String, ScriptBuf)>>>,
}

/// A key's fingerprint for the cache.
fn fingerprint(k: &WotsPublic) -> [u8; 32] {
    let mut h = ::blake3::Hasher::new();
    h.update(&k.params.message_digits.to_be_bytes());
    for d in &k.digits {
        h.update(d.as_ref());
    }
    *h.finalize().as_bytes()
}

impl std::fmt::Debug for ZkFamily {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ZkFamily({} rounds, {} classes, {} input words)", self.search.rounds, self.classes.len(), self.input_keys.len())
    }
}

/// The instruction classes of a program's code, with a sample of each.
pub fn code_classes(info: &ProgramInfo) -> BTreeMap<String, (u32, u8)> {
    let mut m = BTreeMap::new();
    for op in info.code_chunks.iter().flat_map(|c| c.data.iter().copied()) {
        for micro in 0..8u8 {
            if let Some(k) = guard::key_of(op, micro) {
                m.entry(k).or_insert((op, micro));
            }
        }
    }
    m
}

impl ZkFamily {
    pub fn new(search: Search, info: ProgramInfo, input_keys: Vec<WotsPublic>) -> Arc<ZkFamily> {
        let classes = code_classes(&info);
        Arc::new(ZkFamily { search, info, input_keys, classes, cache: Mutex::new(Cache::default()) })
    }
}

fn pos_leaf(name: String, script: ScriptBuf) -> PosLeaf {
    // the leaves read the entry bodies (witness blocks), which the heads
    // alone don't give: no head-only mirror
    PosLeaf { name, script, fires: Arc::new(|_, _| false) }
}

/// An entry: the head, the state key's signature, the body.
pub fn encode_entry(head: &[u8; HEAD_BYTES], sig: &WotsSig, body: &[u8]) -> Vec<u8> {
    let mut e = head.to_vec();
    for h in &sig.hashes {
        e.extend_from_slice(h);
    }
    e.extend_from_slice(body);
    e
}

/// Depth 1's input section of the body: each word, then its signature's
/// elements.
pub fn encode_inputs(words: &[u32], sigs: &[WotsSig]) -> Vec<u8> {
    let mut b = vec![];
    for (w, s) in words.iter().zip(sigs) {
        b.extend_from_slice(&w.to_be_bytes());
        for h in &s.hashes {
            b.extend_from_slice(h);
        }
    }
    b
}

impl ZkFamily {
    fn build_disproves(&self, l: &Layout, rebut: &WotsPublic) -> Vec<PosLeaf> {
        let d = l.depth;
        let s = &self.search;
        if d == 1 {
            vec![pos_leaf("zk_claim".into(), s.claim_leaf(rebut))]
        } else if d == s.depths() {
            // phase 1's record (D59/D60/D61)
            let mut v: Vec<PosLeaf> = final_leaves(l, rebut, &self.info).into_iter().map(|f| pos_leaf(f.name, f.script)).collect();
            v.extend(input_leaves(l, rebut, &self.input_keys, &self.info).into_iter().map(|f| pos_leaf(f.name, f.script)));
            v
        } else if d == s.open_depth() {
            // the read challenge's opening (D62)
            vec![pos_leaf("zk_open".into(), s.open_leaf(rebut))]
        } else if d == s.total() {
            // the read challenge's terminal move: the copy, and BitVMX's
            // read-value and correct-hash challenges (D62)
            vec![
                pos_leaf("zk_copied".into(), s.copied_leaf(rebut, d)),
                pos_leaf("zk_read_value_1".into(), s.read_value_leaf(rebut, 1)),
                pos_leaf("zk_read_value_2".into(), s.read_value_leaf(rebut, 2)),
                pos_leaf("zk_correct_hash".into(), s.correct_hash_leaf(rebut)),
            ]
        } else if d % 2 == 0 {
            vec![pos_leaf("zk_choice".into(), s.choice_leaf(rebut, d))]
        } else {
            vec![pos_leaf("zk_copied".into(), s.copied_leaf(rebut, d))]
        }
    }

    fn build_proofs(&self, l: &Layout, rebut: &WotsPublic) -> Vec<(String, ScriptBuf)> {
        self.classes
            .iter()
            .map(|(key, &(op, micro))| {
                let ins = riscv_decode::decode(op).expect("a class sample decodes");
                let exec = generate_verification_script(&ins, micro, BASE_REGISTER_ADDRESS, requires_witness(&ins));
                (format!("zk_prove_{key}"), prove_script_d60(l, rebut, key, &ScriptBuf::from_bytes(exec.into_bytes()), requires_witness(&ins)))
            })
            .collect()
    }
}

impl lngap_pos::ext::Family for ZkFamily {
    fn disprove_leaves(&self, l: &Layout, rebut: &WotsPublic) -> Vec<PosLeaf> {
        let key = (l.depth, fingerprint(rebut));
        let hit = self.cache.lock().unwrap().disproves.get(&key).cloned();
        let leaves = match hit {
            Some(v) => v,
            None => {
                let v: Arc<Vec<(String, ScriptBuf)>> = Arc::new(self.build_disproves(l, rebut).into_iter().map(|p| (p.name, p.script)).collect());
                self.cache.lock().unwrap().disproves.insert(key, v.clone());
                v
            }
        };
        leaves.iter().map(|(n, s)| pos_leaf(n.clone(), s.clone())).collect()
    }

    fn final_depth(&self) -> Option<u32> {
        Some(self.search.depths())
    }

    fn prove_leaves(&self, l: &Layout, rebut: &WotsPublic) -> Vec<(String, ScriptBuf)> {
        let key = (l.depth, fingerprint(rebut));
        let hit = self.cache.lock().unwrap().proofs.get(&key).cloned();
        match hit {
            Some(v) => v.as_ref().clone(),
            None => {
                let v = self.build_proofs(l, rebut);
                self.cache.lock().unwrap().proofs.insert(key, Arc::new(v.clone()));
                v
            }
        }
    }

    fn entry_ok(&self, d: u32, state_key: &WotsPublic, entry: &[u8]) -> bool {
        let n_sig = state_key.params.total_digits() as usize * 20;
        if entry.len() < HEAD_BYTES + n_sig {
            return false;
        }
        let head: [u8; HEAD_BYTES] = entry[..HEAD_BYTES].try_into().expect("48 bytes");
        let sigs: Vec<[u8; 20]> = entry[HEAD_BYTES..HEAD_BYTES + n_sig].chunks(20).map(|x| x.try_into().expect("20")).collect();
        if !lngap_pos::rebut::check_entry_sig(state_key, &head[lngap_blackjack::SIGNED_FROM..], &sigs) {
            return false;
        }
        let body = &entry[HEAD_BYTES + n_sig..];
        let blocks = BLOCK * (1 + usize::from(d == 1) + usize::from(d == self.search.depths()));
        if body.len() < blocks || !self.search.body_opens(d, &head, &body[..blocks]) {
            return false;
        }
        let rest = &body[blocks..];
        if d != 1 {
            return rest.is_empty();
        }
        // D61: every input word signed under its key
        let per = 4 + input_key_params().total_digits() as usize * 20;
        if rest.len() != per * self.input_keys.len() {
            return false;
        }
        let mut words = vec![];
        let mut wsigs = vec![];
        for c in rest.chunks(per) {
            let w = u32::from_be_bytes(c[..4].try_into().unwrap());
            let hs: Vec<[u8; 20]> = c[4..].chunks(20).map(|x| x.try_into().unwrap()).collect();
            match WotsSig::from_hashes(input_key_params(), &input_message(w), hs) {
                Ok(s) => {
                    words.push(w);
                    wsigs.push(s);
                }
                Err(_) => return false,
            }
        }
        input_signed(&self.input_keys, &words, &wsigs)
    }

    fn equiv_keys(&self) -> Vec<(String, WotsPublic, Role)> {
        self.input_keys.iter().enumerate().map(|(j, k)| (format!("equiv_input_{j}"), k.clone(), mover_at(1))).collect()
    }

    fn settle_code(&self) -> u8 {
        // the prover moves at odd depths; silence until the deadline is
        // acceptance (D60)
        if mover_at(1) == Role::User {
            0
        } else {
            1
        }
    }
}
