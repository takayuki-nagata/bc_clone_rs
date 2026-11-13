// SPDX-License-Identifier: MIT

//! `bc_inventory [--check]`: writes or checks `docs/VERIFICATION_INVENTORY.md` (see the crate
//! documentation).

fn main() {
    let args: Vec<String> = std::env::args_os()
        .skip(1)
        .map(|a| a.to_string_lossy().into_owned())
        .collect();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let status = bc_inventory::run(&args, &root, &mut std::io::stdout(), &mut std::io::stderr());
    std::process::exit(status);
}
