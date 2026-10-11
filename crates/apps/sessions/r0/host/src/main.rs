//! `lngap-r0`: prove the withdrawal guest, wrap a proof in Groth16, read
//! a receipt back.
//!
//! ```text
//! lngap-r0 prove <b> <c> <out>   a succinct (STARK) receipt of the guest on the toy
//!                                L2's withdrawal of b, memo c
//! lngap-r0 wrap <in> <out>       the Groth16 receipt of a succinct receipt
//!                                (x86 Linux with Docker: RISC Zero's gnark step)
//! lngap-r0 verify <in>           verify a receipt against the guest's image id
//! lngap-r0 show <in>             the receipt's kind, image id, journal, seal
//! lngap-r0 selftest              prove (9, 42), wrap, verify: the whole pipeline
//! lngap-r0 withdraw-demo <b> <c> <out>
//!                                the toy L2 (toy.rs) with Alice's return of b,
//!                                memo c; check it natively; prove the guest
//! lngap-r0 bitvmx-input <in> <out.hex>
//!                                a Groth16 receipt as the BitVMX verifier's input
//! ```
//!
//! Receipts are written with bincode. The guest proved is the COMMITTED
//! binary `guests/withdraw.bin`, built reproducibly by
//! `scripts/build-guest.sh`, so every machine proves the same program
//! (the same image id) without building it.

mod bitvmx;
mod toy;

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use risc0_zkvm::{compute_image_id, default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};

/// The guest, as committed.
const WITHDRAW_ELF: &[u8] = include_bytes!("../../guests/withdraw.bin");

fn image_id() -> Digest {
    compute_image_id(WITHDRAW_ELF).expect("the committed guest binary")
}

fn read(path: &str) -> Result<Receipt> {
    let bytes = std::fs::read(path).with_context(|| format!("reading {path}"))?;
    bincode::deserialize(&bytes).with_context(|| format!("decoding {path}"))
}

fn write(path: &str, r: &Receipt) -> Result<()> {
    if let Some(dir) = Path::new(path).parent() {
        std::fs::create_dir_all(dir)?;
    }
    std::fs::write(path, bincode::serialize(r)?).with_context(|| format!("writing {path}"))
}

fn kind(r: &Receipt) -> &'static str {
    match &r.inner {
        InnerReceipt::Composite(_) => "composite",
        InnerReceipt::Succinct(_) => "succinct",
        InnerReceipt::Groth16(_) => "groth16",
        InnerReceipt::Fake(_) => "fake (RISC0_DEV_MODE is set: not a proof)",
        _ => "other",
    }
}

/// Prove the guest on the toy L2's withdrawal of `b`, memo `c`.
fn prove(b: u32, c: u32) -> Result<Receipt> {
    let input = toy::withdraw_input(b, c);
    let env = ExecutorEnv::builder().write(&input)?.build()?;
    let t = Instant::now();
    let info = default_prover().prove_with_opts(env, WITHDRAW_ELF, &ProverOpts::succinct())?;
    eprintln!("proved in {:.1?} ({} user cycles)", t.elapsed(), info.stats.user_cycles);
    Ok(info.receipt)
}

/// Prove the guest on a given withdrawal input (JSON, as a wallet prints
/// it: `lichen withdraw-input <memo>`), checked natively first.
fn prove_input(path: &str) -> Result<Receipt> {
    let input: lngap_r0_core::WithdrawInput = serde_json::from_slice(&std::fs::read(path)?).with_context(|| format!("{path}: a withdrawal input"))?;
    let journal = lngap_r0_core::check(&input, &lngap_r0_core::SEQUENCER_KEY, &lngap_r0_core::HUB_KEY).map_err(|e| anyhow::anyhow!("the statement fails natively: {e:?}"))?;
    eprintln!("{path}: the return of {} with memo {} at index {}, root signed at height {}; journal {}", input.note.value, input.note.memo, input.index, input.height, hex::encode(journal));
    let env = ExecutorEnv::builder().write(&input)?.build()?;
    let t = Instant::now();
    let info = default_prover().prove_with_opts(env, WITHDRAW_ELF, &ProverOpts::succinct())?;
    eprintln!("proved in {:.1?} ({} user cycles, {} segments)", t.elapsed(), info.stats.user_cycles, info.stats.segments);
    info.receipt.verify(image_id())?;
    Ok(info.receipt)
}

/// The BitVMX verifier's input for a Groth16 receipt.
fn bitvmx_input(r: &Receipt) -> Result<Vec<u8>> {
    let InnerReceipt::Groth16(g) = &r.inner else { bail!("a {} receipt, not a Groth16 one", kind(r)) };
    let id: [u8; 32] = image_id().as_bytes().try_into()?;
    bitvmx::input(&id, &g.seal, &r.journal.bytes)
}

fn wrap(r: &Receipt) -> Result<Receipt> {
    let t = Instant::now();
    let g = default_prover().compress(&ProverOpts::groth16(), r)?;
    eprintln!("wrapped in Groth16 in {:.1?}", t.elapsed());
    Ok(g)
}

fn show(r: &Receipt) -> Result<()> {
    println!("kind      {}", kind(r));
    println!("image id  {}", hex::encode(image_id().as_bytes()));
    println!("journal   {}", hex::encode(&r.journal.bytes));
    if let InnerReceipt::Groth16(g) = &r.inner {
        println!("seal      {}", hex::encode(&g.seal));
        println!("verifier  {}", g.verifier_parameters);
    }
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    match a.as_slice() {
        ["prove", b, c, out] => {
            let r = prove(b.parse()?, c.parse()?)?;
            r.verify(image_id())?;
            write(out, &r)?;
            eprintln!("{out}: {} receipt, {} bytes", kind(&r), std::fs::metadata(out)?.len());
        }
        ["wrap", input, out] => {
            let r = read(input)?;
            let g = wrap(&r)?;
            g.verify(image_id())?;
            write(out, &g)?;
            eprintln!("{out}: {} receipt, verified", kind(&g));
            show(&g)?;
        }
        ["verify", input] => {
            let r = read(input)?;
            r.verify(image_id())?;
            println!("{input}: {} receipt verifies against the guest's image id", kind(&r));
        }
        ["show", input] => show(&read(input)?)?,
        ["selftest"] => {
            let r = prove(9, 42)?;
            r.verify(image_id())?;
            let g = wrap(&r)?;
            g.verify(image_id())?;
            if !matches!(g.inner, InnerReceipt::Groth16(_)) {
                bail!("the wrap did not produce a Groth16 receipt");
            }
            println!("selftest: OK (a Groth16 receipt of the guest on (9, 42), verified)");
            show(&g)?;
        }
        ["withdraw-demo", b, c, out] => {
            let input = toy::withdraw_input(b.parse()?, c.parse()?);
            let journal = lngap_r0_core::check(&input, &lngap_r0_core::SEQUENCER_KEY, &lngap_r0_core::HUB_KEY).map_err(|e| anyhow::anyhow!("the statement fails natively: {e:?}"))?;
            eprintln!("the toy L2: Alice's return of {b} with memo {c} at index {}, root signed at height {}; journal {}", input.index, input.height, hex::encode(journal));
            let env = ExecutorEnv::builder().write(&input)?.build()?;
            let t = Instant::now();
            let info = default_prover().prove_with_opts(env, WITHDRAW_ELF, &ProverOpts::succinct())?;
            eprintln!("proved in {:.1?} ({} user cycles, {} segments)", t.elapsed(), info.stats.user_cycles, info.stats.segments);
            info.receipt.verify(image_id())?;
            write(out, &info.receipt)?;
            show(&info.receipt)?;
        }
        ["prove-input", json, out] => {
            let r = prove_input(json)?;
            write(out, &r)?;
            show(&r)?;
        }
        ["claim", json, out] => {
            // a wallet's claim, whole: prove, wrap (x86 Linux), encode
            let g = wrap(&prove_input(json)?)?;
            g.verify(image_id())?;
            let bytes = bitvmx_input(&g)?;
            std::fs::write(out, hex::encode(&bytes))?;
            println!("{out}: the claim's input for the BitVMX verifier, {} bytes", bytes.len());
        }
        ["bitvmx-input", input, out] => {
            let r = read(input)?;
            r.verify(image_id())?;
            let bytes = bitvmx_input(&r)?;
            std::fs::write(out, hex::encode(&bytes))?;
            println!("{out}: {} bytes for the BitVMX verifier", bytes.len());
            println!("{}", hex::encode(&bytes));
        }
        _ => bail!("usage: lngap-r0 prove <b> <c> <out> | wrap <in> <out> | verify <in> | show <in> | selftest | withdraw-demo <b> <c> <out> | bitvmx-input <in> <out.hex> | prove-input <withdraw-input.json> <out> | claim <withdraw-input.json> <out.hex>"),
    }
    Ok(())
}
