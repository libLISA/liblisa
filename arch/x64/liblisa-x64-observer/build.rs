// use std::{process::Command, fs, env};

// pub fn main() {
//     let target = env::current_dir()
//         .unwrap()
//         .join("image/bootdisk");
//     let mut cmd = Command::new("cargo");
//     cmd.args(["build-image-release", "--output", target.to_str().unwrap()])
//         .current_dir(fs::canonicalize("vmimage-x86-64").unwrap());

//     println!("cargo:rerun-if-changed=vmimage-x86-64/src");
//     println!("cargo:rerun-if-changed=vmimage-x86-64/link.x");
//     println!("cargo:rerun-if-changed=vmimage-x86-64/Cargo.toml");
//     println!("cargo:rerun-if-changed=vmimage-x86-64/Cargo.lock");

//     for (key, val) in std::env::vars() {
//         println!("{}={}", key, val);
//         if key.starts_with("CARGO_") && key != "CARGO_HOME" {
//             cmd.env_remove(&key);
//         }
//     }

//     let result = cmd.status().unwrap();
//     assert!(result.success(), "building the vmimage failed");
// }

use std::path::PathBuf;
use std::process::Command;

fn main() {
    // let cargo_binary = std::env::var("_").unwrap();
    let cargo_binary = "cargo";
    println!("Cargo binary: {cargo_binary}");
    let mut cmd = Command::new(cargo_binary);
    cmd.arg("build");
    let profile = std::env::var("PROFILE").unwrap();

    if profile != "debug" {
        cmd.arg("--release");
    }

    cmd.args(["--target", "x86_64-unknown-none"]);
    cmd.args(["--target-dir", "../image"]);
    cmd.args(["-Z", "build-std=core,alloc"]);

    let dir = PathBuf::from(&std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("vmimage-x86-64");

    println!("cargo:rerun-if-changed={}", dir.display());

    cmd.current_dir(&dir);
    let to_remove = std::env::vars()
        // .inspect(|x| println!("Current env: {x:?}"))
        .map(|(k, _)| k)
        .filter(|k| k.starts_with("CARGO") || k.starts_with("RUST"))
        .collect::<Vec<_>>();
    for x in to_remove {
        cmd.env_remove(x);
    }
    cmd.env(
        "RUSTFLAGS",
        "-Clink-arg=-Tlink.x -Ccode-model=large -Crelocation-model=static -Ctarget-feature=-mmx,-sse,+soft-float",
    );

    // for env in cmd.get_envs() {
    //     println!("ENV: {env:?}");
    // }

    let status = cmd.spawn().unwrap().wait().unwrap();

    assert!(status.success());

    // set by cargo, build scripts should use this directory for output files
    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    let kernel = dir
        .parent()
        .unwrap()
        .join("image")
        .join("x86_64-unknown-none")
        .join(profile)
        .join("vmimage-x86-64");

    // create a BIOS disk image
    let bios_path = out_dir.join("bootdisk.img");
    bootloader::BiosBoot::new(&kernel).create_disk_image(&bios_path).unwrap();

    // pass the disk image paths as env variables to the `main.rs`
    println!("cargo:rustc-env=BIOS_PATH={}", bios_path.display());
}
