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
| **withdraw (the statement), at 6ed5998: the current file** | **x86 Linux, `build-guest.sh` (reproducible), 441,580 bytes, SHA-256 `1a64b317e6c0db816b25515be9dbd476ed259e8e5f00e0b1908613190223538f`** | **`4beda75466ff0db4aa6c6fe9512140368ad287c695f0ff162775db93039aa639`** |

Checked on the Mac: the host tool recomputes the same image id from the
file. Its proof (toy L2, b = 9, c = 42; 5.9M cycles, 27.7 min on a
12-core laptop, 9.6 GB peak; Groth16 wrap 109 s), encoded as the
verifier's 172-byte input, runs BitVMX's unpatched Groth16 verifier to
Halt(0) in 478,100,841 steps; with b tampered, Halt(1).
