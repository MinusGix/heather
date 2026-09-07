//! An actual nested CALL/RET executable, with no host linker or initial-stack dependency.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn nested_calls_return_the_source_result() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let directory = root.join(format!("target/native-calls-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let executable = directory.join("caller");
    let output = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .env("PATH", &directory)
        .args(["build-x86", "examples/x86-native/calls.hthr", "caller", "--callee", "leaf", "--arg", "20", "--arg", "22", "-o"])
        .arg(&executable).args(["--cache-dir", "target/native-test-images"]).output().unwrap();
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let file = std::fs::read(&executable).unwrap();
    assert_eq!(u16::from_le_bytes(file[56..58].try_into().unwrap()), 3);
    assert_eq!(u64::from_le_bytes(file[24..32].try_into().unwrap()), 0x4000e8);
    // The additional segment is RW, zero-filled, and disjoint from code.
    assert_eq!(u32::from_le_bytes(file[180..184].try_into().unwrap()), 6);
    assert_eq!(u64::from_le_bytes(file[192..200].try_into().unwrap()), 0x401000);
    assert_eq!(u64::from_le_bytes(file[208..216].try_into().unwrap()), 0);
    assert_eq!(u64::from_le_bytes(file[216..224].try_into().unwrap()), 4096);
    assert_eq!(Command::new(&executable).status().unwrap().code(), Some(197));
    let certificate = std::fs::read_to_string(directory.join("caller.certificate.hthr")).unwrap();
    for claim in ["_source_call", "_file_correct", "_loaded_execution", "_callee_contract", "_exit_request", "_syscall_fetched", "_stack_restored", "_aligned_call"] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    std::fs::remove_dir_all(directory).unwrap();
}
