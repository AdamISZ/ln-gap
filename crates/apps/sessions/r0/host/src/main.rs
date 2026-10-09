//! `lngap-r0`: prove the withdrawal guest, wrap a proof in Groth16, read
//! a receipt back.
//!
//! ```text
//! lngap-r0 prove <b> <c> <out>   a succinct (STARK) receipt of the guest on (b, c)
//! lngap-r0 wrap <in> <out>       the Groth16 receipt of a succinct receipt
//!                                (x86 Linux with Docker: RISC Zero's gnark step)
//! lngap-r0 verify <in>           verify a receipt against the guest's image id
//! lngap-r0 show <in>             the receipt's kind, image id, journal, seal
//! lngap-r0 selftest              prove (9, 42), wrap, verify: the whole pipeline
//! ```
//!
//! Receipts are written with bincode.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use lngap_r0_methods::{WITHDRAW_ELF, WITHDRAW_ID};
use risc0_zkvm::{default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt};

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

fn prove(b: u32, c: u32) -> Result<Receipt> {
    let env = ExecutorEnv::builder().write(&(b, c))?.build()?;
    let t = Instant::now();
    let info = default_prover().prove_with_opts(env, WITHDRAW_ELF, &ProverOpts::succinct())?;
    eprintln!("proved in {:.1?} ({} user cycles)", t.elapsed(), info.stats.user_cycles);
    Ok(info.receipt)
}

fn wrap(r: &Receipt) -> Result<Receipt> {
    let t = Instant::now();
    let g = default_prover().compress(&ProverOpts::groth16(), r)?;
    eprintln!("wrapped in Groth16 in {:.1?}", t.elapsed());
    Ok(g)
}

fn show(r: &Receipt) -> Result<()> {
    println!("kind      {}", kind(r));
    println!("image id  {}", hex::encode(Digest::from(WITHDRAW_ID).as_bytes()));
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
            r.verify(WITHDRAW_ID)?;
            write(out, &r)?;
            eprintln!("{out}: {} receipt, {} bytes", kind(&r), std::fs::metadata(out)?.len());
        }
        ["wrap", input, out] => {
            let r = read(input)?;
            let g = wrap(&r)?;
            g.verify(WITHDRAW_ID)?;
            write(out, &g)?;
            eprintln!("{out}: {} receipt, verified", kind(&g));
            show(&g)?;
        }
        ["verify", input] => {
            let r = read(input)?;
            r.verify(WITHDRAW_ID)?;
            println!("{input}: {} receipt verifies against the guest's image id", kind(&r));
        }
        ["show", input] => show(&read(input)?)?,
        ["selftest"] => {
            let r = prove(9, 42)?;
            r.verify(WITHDRAW_ID)?;
            let g = wrap(&r)?;
            g.verify(WITHDRAW_ID)?;
            if !matches!(g.inner, InnerReceipt::Groth16(_)) {
                bail!("the wrap did not produce a Groth16 receipt");
            }
            println!("selftest: OK (a Groth16 receipt of the guest on (9, 42), verified)");
            show(&g)?;
        }
        _ => bail!("usage: lngap-r0 prove <b> <c> <out> | wrap <in> <out> | verify <in> | show <in> | selftest"),
    }
    Ok(())
}
