use std::path::PathBuf;
use std::process::Command;

fn main() {
    let cargo_binary = "cargo";
    println!("Cargo binary: {cargo_binary}");
    let mut cmd = Command::new(cargo_binary);
    cmd.arg("build");

    // TODO: Generate a separate debug image
    cmd.arg("--release");

    cmd.args(["--target", "x86_64-unknown-none"]);
    cmd.args(["--target-dir", "../image"]);
    cmd.args(["-Z", "build-std=core,alloc"]);

    let dir = PathBuf::from(&std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("vmimage-x86-64");

    cmd.current_dir(&dir);
    let to_remove = std::env::vars()
        // .inspect(|x| println!("Current env: {x:?}"))
        .map(|(k, _)| k)
        .filter(|k| k.starts_with("CARGO") || k.starts_with("RUST"))
        .collect::<Vec<_>>();
    for x in to_remove {
        cmd.env_remove(x);
    }

    let root = std::env::current_dir().unwrap();
    let root = root.display();

    let home = std::env::var("HOME").unwrap();
    let rustflags = format!("-Clink-arg=-Tlink.x -Ccode-model=large -Crelocation-model=static -Ctarget-feature=-mmx,-sse,+soft-float --remap-path-prefix {root}=. --remap-path-prefix {home}=..");
    cmd.env("RUSTFLAGS", rustflags);
    
    let status = cmd.spawn().unwrap().wait().unwrap();

    assert!(status.success());

    // set by cargo, build scripts should use this directory for output files
    let out_dir = PathBuf::from("arch/x64/liblisa-x64-observer/image");

    // TODO: Use cargo artifacts once we're able to specify rustflags in the dependency.
    let kernel = dir
        .parent()
        .unwrap()
        .join("image")
        .join("x86_64-unknown-none")
        .join("release")
        .join("vmimage-x86-64");

    // create a BIOS disk image
    let bios_path = out_dir.join("bootdisk.img");
    bootloader::BiosBoot::new(&kernel).create_disk_image(&bios_path).unwrap();
}
