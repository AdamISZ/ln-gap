# Test data

`withdraw-9-42-deployment.hex` (to come from the canonical build:
`r0/scripts/linux-withdraw.sh` prints it): the verifier's 204-byte input
for the current statement on the toy deployment's return of 9 with memo
42: journal length (10 words), image id, the proof's points, journal
`b ‖ c ‖ D` (`D` the toy deployment's id). lichen's `groth16.rs` reads it.

`withdraw-9-42.hex`, the previous statement's (the ladder's tests use it:
any valid Groth16 input does): the BitVMX Groth16 verifier's 172-byte input for a
proof of the withdrawal guest (image id `4beda754...a639`, the canonical
build in `../../r0/guests/`) on the toy L2's return of 9 to the hub with
memo 42: journal length (2 words), image id, the proof's points
(FairgateLabs' encoding), journal `b ‖ c`. Proved on x86 Linux with RISC
Zero 3.0.6; the unpatched verifier runs it to Halt(0) in 478,100,841
steps. Our proof, not GPL code.
