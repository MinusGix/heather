//! A live caller slot survives a callee that clobbers its scratch register.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn caller_reloads_its_live_stack_local() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let directory = root.join(format!("target/native-stack-local-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let executable = directory.join("caller");
    let output = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .env("PATH", &directory)
        .args(["build-x86", "examples/x86-native/stack_local.hthr", "caller", "--callee", "leaf", "--arg", "20", "--arg", "22", "-o"])
        .arg(&executable).args(["--cache-dir", "target/native-test-images"]).output().unwrap();
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    assert_eq!(Command::new(&executable).status().unwrap().code(), Some(40));
    let bytes = std::fs::read(&executable).unwrap();
    for instruction in [&[0x4c, 0x89, 0x1c, 0x24][..], &[0x4c, 0x8b, 0x1c, 0x24][..], &[0x4d, 0x31, 0xdb][..]] {
        assert!(bytes.windows(instruction.len()).any(|window| window == instruction));
    }
    let proof = std::fs::read_to_string(directory.join("caller.certificate.hthr")).unwrap();
    for claim in ["StoreStack64(R11)", "LoadStack64(R11)", "NativeIntegerCallContract", "_callee_memory_effects(gprs, flags, stack)(", "_saved_value", "_stack_restored", "_loaded_execution"] {
        assert!(proof.contains(claim), "missing {claim}");
    }
    std::fs::remove_dir_all(directory).unwrap();
}
