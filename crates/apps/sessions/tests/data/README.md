# Test data

`withdraw-9-42-deployment.hex`: the verifier's 204-byte input for the
current statement (image id `69ca65ff...c72c`, the canonical build;
`r0/scripts/linux-withdraw.sh` prints it) on the toy deployment's return of 9 with memo
42: journal length (10 words), image id, the proof's points, journal
`b ‖ c ‖ D` (`D` the toy deployment's id). Proved on x86 Linux with RISC
Zero 3.1.0; the verifier with 3.1's key and constants
(`lngap_zk::groth16::verifier_elf`) runs it to Halt(0) in 477,836,363
steps, and with b tampered to Halt(1) (`tests/groth16_input.rs`).

`withdraw-9-42.hex`, the previous statement's (the ladder's tests use it:
any valid Groth16 input does): the BitVMX Groth16 verifier's 172-byte input for a
proof of the withdrawal guest (image id `c7971df3...b541`: the guest at
f7d6f42 with c042ce9's RISC Zero 3.1.0 pins, built canonically) on the toy L2's return of 9 to the hub with
memo 42: journal length (2 words), image id, the proof's points
(FairgateLabs' encoding), journal `b ‖ c`. Proved on x86 Linux with RISC
Zero 3.1.0; the verifier with 3.1's key and constants runs it to Halt(0)
in 478,284,186 steps, and with b tampered to Halt(1). Our proof, not GPL
code.
