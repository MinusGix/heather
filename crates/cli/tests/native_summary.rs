//! One checked callee summary used with different inputs and placements.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn two_placed_calls_share_one_summary() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let directory = root.join(format!("target/native-summary-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let executable = directory.join("caller");
    let output = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .env("PATH", &directory)
        .args(["build-x86", "examples/x86-native/reused_callee.hthr", "caller", "--callee", "leaf", "--arg", "21", "--arg", "1", "-o"])
        .arg(&executable).args(["--cache-dir", "target/native-test-images"]).output().unwrap();
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    assert_eq!(Command::new(&executable).status().unwrap().code(), Some(3));
    let certificate = std::fs::read_to_string(directory.join("caller.certificate.hthr")).unwrap();
    assert_eq!(certificate.matches("fn caller_native_leaf_summary(").count(), 1);
    assert_eq!(certificate.matches("use_call_summary(").count(), 2);
    assert_eq!(certificate.matches("call_trace_append(").count(), 2);
    assert!(certificate.contains("caller_native_leaf_second_values"));
    assert!(certificate.contains("StoreStack64(Rdi)"));
    assert!(certificate.contains("_dead_frame_byte"));
    assert!(certificate.contains("_callee_preserved_rsi"));
    std::fs::remove_dir_all(directory).unwrap();
}
