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

#[test]
fn source_to_standalone_elf_without_a_toolchain() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = root.join(format!("target/elf-integration-{}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let binary = output.join("mix");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        // No child compiler/assembler/linker can be found through PATH.
        .env("PATH", &output)
        .args(["build-x86", "examples/x86-native/mix.hthr", "mix", "--arg", "0x14", "--arg", "0b10110", "-o"])
        .arg(&binary).args(["--cache-dir", "target/native-test-images"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let bytes = std::fs::read(&binary).unwrap();
    assert_eq!(&bytes[..4], b"\x7fELF");
    assert_eq!(u64::from_le_bytes(bytes[24..32].try_into().unwrap()), 0x4000b0);
    assert_eq!(u32::from_le_bytes(bytes[68..72].try_into().unwrap()), 5); // RX
    assert_eq!(u32::from_le_bytes(bytes[124..128].try_into().unwrap()), 6); // RW stack
    assert_eq!(Command::new(&binary).status().unwrap().code(), Some(27));
    let certificate = std::fs::read_to_string(output.join("mix.certificate.hthr")).unwrap();
    for claim in ["_entry_graph", "_inline_trace", "_exit_request", "_elf_file_correct", "_elf_entry_code"] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    // The request carries the full result, while Linux reports its low byte.
    let wide_status = output.join("wide-status");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root).env("PATH", &output)
        .args(["build-x86", "examples/x86-native/mix.hthr", "mix", "--arg", "255", "--arg", "0", "-o"])
        .arg(&wide_status).args(["--cache-dir", "target/native-test-images"])
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    assert_eq!(Command::new(&wide_status).status().unwrap().code(), Some(249)); // 255 xor 262 = 505
    // An invalid argument must fail before publishing either output.
    let rejected = output.join("bad");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["build-x86", "examples/x86-native/mix.hthr", "mix", "--arg", "-1", "--arg", "0", "-o"])
        .arg(&rejected).output().unwrap();
    assert!(!result.status.success());
    assert!(!rejected.exists());
    assert!(!output.join("bad.certificate.hthr").exists());
    std::fs::remove_dir_all(output).unwrap();
}
