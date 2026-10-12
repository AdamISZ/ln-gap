# The committed guest binary

`withdraw.bin` is the guest program the host tool proves (RISC Zero's
program-binary format: the guest ELF with RISC Zero's kernel). Its image
id is what a session contract pins.

The canonical binary is built reproducibly by `../scripts/build-guest.sh`
(x86 Docker, RISC Zero's pinned builder image), and the image id below is
that build's.

| guest | built by | image id |
|---|---|---|
| placeholder (commits b, c) | Mac, local build (development only) | `0a89c87936208a4e19b83b3161ea9c992282057e16e39ebc1279c1e85df83695` |
| withdraw (the statement), at 96e041b | Mac, local build (development only) | `843412961546156cf1276c6d22adb816d1eb1879a0f57d0abe799d1d779d7216` |
| withdraw (the statement), at 6ed5998 | x86 Linux, `build-guest.sh` (reproducible), 441,580 bytes, SHA-256 `1a64b317e6c0db816b25515be9dbd476ed259e8e5f00e0b1908613190223538f` | `4beda75466ff0db4aa6c6fe9512140368ad287c695f0ff162775db93039aa639` |
| withdraw, deployment keys in the input, journal `b ‖ c ‖ D`, accelerated crypto, at d9335ea | Mac, local build (development only), 373,072 bytes, SHA-256 `a4adfb2d14b22449689e6b7b4f0095c4d54eee98c4b4f530117aa4c4f226be56` | `1bb827a083155b984971443d0c11a0e161041ff77fb77360dcaa7b2013693cdf` |
| **withdraw, deployment keys in the input, journal `b ‖ c ‖ D`, accelerated crypto, at d9335ea: the current file** | **x86 Linux, `build-guest.sh` (reproducible), 412,444 bytes, SHA-256 `a29190991b073c93190333218bf87b3056e27a9f2da00b019103686511e17e56`** | **`e0cd81a7ada6a59415be2e4a4e0cea04b6a616cc0efeeb7443e49be38a90298e`** |

The current statement (2026-10-12): the sequencer's and the hub's keys
are part of the input, and the journal commits to them as the deployment
id `D`, so one guest serves every deployment; the guest uses RISC Zero's
accelerated `sha2`, `k256` and `crypto-bigint`. Checked on the Mac: the
host tool recomputes the same image id from the file. Its proof (toy
deployment, b = 9, c = 42; 446k cycles, one segment; 2 min 24 s and
4.8 GB peak on the 12-core laptop, 30 s on an M4 Pro), encoded as the
verifier's 204-byte input (`../tests/data/withdraw-9-42-deployment.hex`),
runs BitVMX's unpatched Groth16 verifier to Halt(0) in 477,943,091 steps;
with b tampered, Halt(1).

The previous statement, at 6ed5998: checked on the Mac: the host tool recomputes the same image id from the
file. Its proof (toy L2, b = 9, c = 42; 5.9M cycles, 27.7 min on a
12-core laptop, 9.6 GB peak; Groth16 wrap 109 s), encoded as the
verifier's 172-byte input, runs BitVMX's unpatched Groth16 verifier to
Halt(0) in 478,100,841 steps; with b tampered, Halt(1).
