//! Prints the scripts that the explainer documents in `docs/` walk
//! through, from the same builders the dispute graph uses:
//!
//!     cargo run -p lngap-pos --example doc_scripts
//!
//! Each disprove leaf starts with the Winternitz verification of the
//! parked pair (`docs/winternitz.md`); that prefix is identical in every
//! leaf, so it is cut off here and only the predicate that follows it is
//! printed. Long pushes (keys, points, hashes) are abbreviated.

use bitcoin::key::Keypair;
use bitcoin::script::{Builder, Instruction};
use bitcoin::secp256k1::{SecretKey, SECP256K1};
use bitcoin::Script;
use lngap_channel::Role;
use lngap_ec_wots::{readout_tied_fragment, Attester};
use lngap_lamport::winternitz::{WotsExt, WotsParams, WotsPublic, WotsSecret};
use lngap_pos::refute::pair_key;
use lngap_pos::ttt::Layout;
use lngap_pos::{blackjack, chess, graph, ttt, HEADER_CHUNKS};

/// One instruction per line; pushes longer than 4 bytes abbreviated.
fn asm(script: &Script) -> String {
    let mut out = Vec::new();
    for ins in script.instructions() {
        out.push(match ins.expect("a valid script") {
            Instruction::Op(op) => format!("{op:?}").replace("OP_PUSHNUM_", "").replace("OP_PUSHBYTES_0", "0"),
            Instruction::PushBytes(pb) => {
                let b = pb.as_bytes();
                match b.len() {
                    0 => "0".into(),
                    1..=4 => {
                        // a script number, little-endian with a sign bit
                        let mut v: i64 = 0;
                        for (i, x) in b.iter().enumerate() {
                            v |= i64::from(*x) << (8 * i);
                        }
                        format!("{v}")
                    }
                    n => format!("<{n} bytes: {}…>", hex::encode(&b[..4])),
                }
            }
        });
    }
    // runs of one opcode as `OP_X ×n`
    let mut lines: Vec<(String, usize)> = Vec::new();
    for o in out {
        match lines.last_mut() {
            Some((last, n)) if *last == o && o.starts_with("OP_") => *n += 1,
            _ => lines.push((o, 1)),
        }
    }
    lines.into_iter().map(|(o, n)| if n > 1 { format!("{o} ×{n}") } else { o }).collect::<Vec<_>>().join("\n")
}

/// The leaf's script after its Winternitz prefix.
fn tail<'a>(leaf: &'a Script, key: &WotsPublic) -> &'a Script {
    let prefix = Builder::new().wots_verify(key).into_script();
    assert!(leaf.as_bytes().starts_with(prefix.as_bytes()), "every disprove leaf opens with the pair's verification");
    Script::from_bytes(&leaf.as_bytes()[prefix.len()..])
}

fn section(title: &str, body: &str) {
    println!("==== {title}\n{body}\n");
}

fn main() {
    let key = pair_key([9u8; 32]).public();

    // tic-tac-toe: cell_occupied_4 at depth 2 (the hub, O, moves)
    let l = Layout::at(2, 1, Role::Hub);
    let leaf = ttt::disprove_leaves(&l, &key).into_iter().find(|p| p.name == "cell_occupied_4").expect("the leaf");
    section(
        &format!("tic-tac-toe cell_occupied_4, depth 2 ({} bytes in all, {} after the WOTS prefix)", leaf.script.len(), tail(&leaf.script, &key).len()),
        &asm(tail(&leaf.script, &key)),
    );

    // chess: the sizes of the family at depth 2
    let l = Layout::at(2, 1, Role::Hub);
    let mut sizes: Vec<String> = chess::disprove_leaves(&l, &key).iter().map(|p| format!("{:<28} {:>6} B", p.name, p.script.len())).collect();
    sizes.sort();
    section("chess disprove leaves, depth 2 (whole leaf, WOTS prefix included)", &sizes.join("\n"));

    // blackjack: bj_card_2 at depth 2 (the house reveals the first three cards)
    let c = lngap_blackjack::Commitments { player: [[0xaa; 32]; lngap_blackjack::K], house: [[0xbb; 32]; lngap_blackjack::K] };
    let l = Layout::at(2, 1, Role::Hub);
    let leaf = blackjack::disprove_leaves(&l, &key, &c).into_iter().find(|p| p.name == "bj_card_2").expect("the leaf");
    section(
        &format!("blackjack bj_card_2, depth 2 ({} bytes in all, {} after the WOTS prefix)", leaf.script.len(), tail(&leaf.script, &key).len()),
        &asm(tail(&leaf.script, &key)),
    );

    // Winternitz: the verification of a one-byte message (2 digits, 2 checksum digits)
    let small = WotsSecret::from_entropy(WotsParams::for_bytes(1), [3u8; 32]).public();
    let s = Builder::new().wots_verify(&small).into_script();
    section(&format!("WOTS verify, a 1-byte message: {} message + {} checksum digits ({} bytes)", small.params.message_digits, small.params.checksum_digits, s.len()), &asm(&s));

    // EC-OTS: one chunk of the readout
    let table = Attester::new([7u8; 32]).epoch_table(1, HEADER_CHUNKS);
    let s = readout_tied_fragment(Builder::new(), &table.points[80]).into_script();
    section(&format!("EC-OTS readout, one head chunk ({} bytes)", s.len()), &asm(&s));

    // the refutation's gate: the 2-of-2, then the proposer fragment over five members
    let pk = |i: u8| Keypair::from_secret_key(SECP256K1, &SecretKey::from_slice(&[i; 32]).unwrap()).x_only_public_key().0;
    let points: Vec<_> = (1..=5).map(pk).collect();
    let s = graph::proposer_fragment(Builder::new().two_of_two_verify_keys(&pk(10), &pk(11)), &points).into_script();
    section(&format!("refute: the 2-of-2 and the proposer fragment, five members ({} bytes)", s.len()), &asm(&s));
}

/// The channel's 2-of-2 over two explicit keys (the graph takes them from
/// the commitment's context).
trait TwoOfTwo {
    fn two_of_two_verify_keys(self, a: &bitcoin::XOnlyPublicKey, b: &bitcoin::XOnlyPublicKey) -> Self;
}

impl TwoOfTwo for Builder {
    fn two_of_two_verify_keys(self, a: &bitcoin::XOnlyPublicKey, b: &bitcoin::XOnlyPublicKey) -> Self {
        use lngap_btc::script::BuilderExt;
        self.two_of_two_verify(a, b)
    }
}
