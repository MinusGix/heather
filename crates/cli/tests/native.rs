//! Exercise the actual exported bytes through the host assembler and linker.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn source_to_native_binary() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = root.join(format!("target/native-integration-{}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let assembly = output.join("mix.s");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["compile-x86", "examples/x86-native/mix.hthr", "mix", "-o"])
        .arg(&assembly).args(["--cache-dir", "target/native-test-images"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let binary = output.join("mix");
    let linked = Command::new("cc").current_dir(&root)
        .args(["-std=c11", "-Wall", "-Wextra", "-Werror", "examples/x86-native/main.c"])
        .arg(&assembly).arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let native = Command::new(&binary).output().unwrap();
    assert!(native.status.success(), "{}", String::from_utf8_lossy(&native.stdout));
    assert!(String::from_utf8_lossy(&native.stdout).contains("10005 native cases passed"));
    std::fs::remove_dir_all(output).unwrap();
}
