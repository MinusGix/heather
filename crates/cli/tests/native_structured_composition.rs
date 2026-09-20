//! Native execution of a structured helper composed with its caller.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn source_composed_helper_executes() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-branches-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for name in ["composed"] {
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .args(["compile-x86", "examples/x86-native/branches.hthr", name, "-o"])
            .arg(dir.join(format!("{name}.s"))).args(["--cache-dir", "target/native-test-images", "--kernel-workers", "1"])
            .output().unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        let certificate = std::fs::read_to_string(dir.join(format!("{name}.certificate.hthr"))).unwrap();
        for claim in ["_source_artifact", "_source_correct", "_layout", "_span", "_exported_bytes", "StructuredArtifact"] {
            assert!(certificate.contains(claim), "missing {claim}");
        }
        assert!(certificate.contains(&format!("branches::{name}")));
    }
    let driver = dir.join("main.c");
    std::fs::write(&driver, r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t composed(uint64_t, uint64_t);
static int check(uint64_t a, uint64_t b) {
    return composed(a,b) == (a != b ? a + b : a - b);
}
int main(void) {
    uint64_t edges[] = {0, 1, 9, 10, 11, UINT64_MAX};
    for (unsigned i=0; i<6; ++i) for (unsigned j=0; j<6; ++j)
        if (!check(edges[i], edges[j])) return 1;
    uint64_t state = 1;
    for (unsigned i=0; i<10000; ++i) {
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t a = state;
        state = state * UINT64_C(6364136223846793005) + 1;
        if (!check(a, state)) return 2;
    }
    puts("10036 pairs passed for composed helper");
    return 0;
}
"#).unwrap();
    let binary = dir.join("branches");
    let linked = Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
        .arg(driver).arg(dir.join("composed.s"))
        .arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let result = Command::new(binary).output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stdout));
    std::fs::remove_dir_all(dir).unwrap();
}
