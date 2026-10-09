# The committed guest binary

`withdraw.bin` is the guest program the host tool proves (RISC Zero's
program-binary format: the guest ELF with RISC Zero's kernel). Its image
id is what a session contract pins.

The canonical binary is built reproducibly by `../scripts/build-guest.sh`
(x86 Docker, RISC Zero's pinned builder image), and the image id below is
that build's. Until the first such build is committed, the file here is a
development build from a Mac, whose image id is machine-specific.

| guest | built by | image id |
|---|---|---|
| placeholder (commits b, c) | Mac, local build (development only) | `0a89c87936208a4e19b83b3161ea9c992282057e16e39ebc1279c1e85df83695` |
| withdraw (the statement) | Mac, local build (development only; current file) | `843412961546156cf1276c6d22adb816d1eb1879a0f57d0abe799d1d779d7216` |
