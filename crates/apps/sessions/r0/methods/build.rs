//! Builds the guest. With `LNGAP_GUEST_DOCKER` set, it builds inside RISC
//! Zero's pinned builder image (x86 Docker), which fixes the toolchain and
//! the paths, so the binary and its image id are the same on every
//! machine: the canonical build (scripts/build-guest.sh). Without it,
//! a local build for development, whose image id is machine-specific.

use std::collections::HashMap;

use risc0_build::{DockerOptionsBuilder, GuestOptionsBuilder};

fn main() {
    println!("cargo:rerun-if-env-changed=LNGAP_GUEST_DOCKER");
    if std::env::var("LNGAP_GUEST_DOCKER").is_ok() {
        let docker = DockerOptionsBuilder::default()
            // the build context must hold the guest and the core crate it uses
            .root_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/.."))
            .build()
            .unwrap();
        let guest = GuestOptionsBuilder::default().use_docker(docker).build().unwrap();
        risc0_build::embed_methods_with_options(HashMap::from([("withdraw", guest)]));
    } else {
        risc0_build::embed_methods();
    }
}
