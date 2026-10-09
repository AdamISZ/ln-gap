# Test data

`withdraw-9-42.hex`: the BitVMX Groth16 verifier's 172-byte input for a
proof of the withdrawal guest (image id `4beda754...a639`, the canonical
build in `../../r0/guests/`) on the toy L2's return of 9 to the hub with
memo 42: journal length (2 words), image id, the proof's points
(FairgateLabs' encoding), journal `b ‖ c`. Proved on x86 Linux with RISC
Zero 3.0.6; the unpatched verifier runs it to Halt(0) in 478,100,841
steps. Our proof, not GPL code.
