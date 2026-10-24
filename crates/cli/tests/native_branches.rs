//! Native execution of both recursive branch shapes through ordinary export.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn source_nested_conditionals_execute() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-branches-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for name in ["nested_true", "nested_false", "unsigned_threshold", "take_threshold", "keep_twice", "nudged", "composed", "either"] {
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .args(["compile-x86", "examples/x86-native/branches.hthr", name, "-o"])
            .arg(dir.join(format!("{name}.s"))).args(["--cache-dir", "target/native-test-images", "--kernel-workers", "1"])
            .output().unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        let certificate = std::fs::read_to_string(dir.join(format!("{name}.certificate.hthr"))).unwrap();
        // Each shape goes through the verified lowering: the certificate
        // instantiates `compiled_returns`, and nothing in it is generated
        // per instruction.
        for claim in ["_lowers()", "_agrees(", "_bytes()", "_entry_at()", "_returns<M>", "compiled_returns<M>("] {
            assert!(certificate.contains(claim), "missing {claim}: {}", String::from_utf8_lossy(&result.stderr));
        }
        // A test through a Bool helper or a connective agrees through the
        // decision tree spelled in source operations, which `split_all`
        // matches against the source; a comparison-only tree by `refl`.
        let decides = matches!(name, "composed" | "either");
        assert_eq!(certificate.contains("_expands("), decides, "{name}: expansion route");
        assert!(certificate.contains(&format!("branches::{name}(")));
        assert!(!certificate.contains("StructuredArtifact"), "no per-function artifact");
    }
    let driver = dir.join("main.c");
    std::fs::write(&driver, r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t nested_true(uint64_t, uint64_t);
extern uint64_t nested_false(uint64_t, uint64_t);
extern uint64_t unsigned_threshold(uint64_t, uint64_t);
extern uint64_t take_threshold(uint64_t, uint64_t);
extern uint64_t keep_twice(uint64_t, uint64_t);
extern uint64_t nudged(uint64_t, uint64_t);
extern uint64_t composed(uint64_t, uint64_t);
extern uint64_t either(uint64_t, uint64_t);
static uint64_t keep_below(uint64_t a, uint64_t b) { return a < (UINT64_C(1) << 32) ? a : a - (UINT64_C(1) << 32) + b; }
static int check(uint64_t a, uint64_t b) {
    uint64_t t = a < b ? (b < 10 ? a + b : b ^ a) : a - b;
    uint64_t f = a < b ? b + a : (a < 10 ? a | b : b - a);
    uint64_t u = a < (UINT64_C(1) << 32) ? a + b : a - b;
    uint64_t k = a < (UINT64_C(1) << 32) ? a + b : a - (UINT64_C(1) << 32) + b;
    return nested_true(a,b) == t && nested_false(a,b) == f && unsigned_threshold(a,b) == u && take_threshold(a,b) == k && keep_twice(a,b) == keep_below(keep_below(a, b), b)
        && nudged(a,b) == (a < b ? a + 16 + (b - 1) : a + 65536 + (UINT64_C(1) << 31))
        && composed(a,b) == (a != b ? a + b : a - b)
        && either(a,b) == (a < b || (b == 7 && !((int64_t)a < (int64_t)b)) ? (b != a + b ? b - a : a) : (a ^ b));
}
int main(void) {
    uint64_t edges[] = {0, 1, 7, 9, 10, 11, (UINT64_C(1) << 32) - 1, UINT64_C(1) << 32, (UINT64_C(1) << 32) + 1, UINT64_MAX};
    for (unsigned i=0; i<10; ++i) for (unsigned j=0; j<10; ++j)
        if (!check(edges[i], edges[j])) return 1;
    uint64_t state = 1;
    for (unsigned i=0; i<10000; ++i) {
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t a = state;
        state = state * UINT64_C(6364136223846793005) + 1;
        if (!check(a, state)) return 2;
    }
    puts("10100 pairs passed for every branch shape");
    return 0;
}
"#).unwrap();
    let binary = dir.join("branches");
    let linked = Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
        .arg(driver).arg(dir.join("nested_true.s")).arg(dir.join("nested_false.s")).arg(dir.join("unsigned_threshold.s")).arg(dir.join("take_threshold.s")).arg(dir.join("keep_twice.s")).arg(dir.join("nudged.s")).arg(dir.join("composed.s")).arg(dir.join("either.s"))
        .arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    let result = Command::new(binary).output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stdout));
    std::fs::remove_dir_all(dir).unwrap();
}

// The negative control: a call of a function that decides through a
// connective is refused by the reflector (the caller's agreement could not
// unfold it), naming the issue that lifts the restriction.
#[test]
fn a_call_of_a_deciding_function_is_refused() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-decided-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("calls_either.hthr"), "import bitvec;\nimport bool;\nimport branches;\n\
        fn calls_either(a, b: BitVec(64)) → BitVec(64) { branches::either(a, b).add(a) }\n").unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .arg("compile-x86").arg(dir.join("calls_either.hthr")).args(["calls_either", "-o"])
        .arg(dir.join("calls_either.s")).args(["-L", "examples/x86-native", "--cache-dir", "target/native-test-images", "--kernel-workers", "1"])
        .output().unwrap();
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(stderr.contains("function-ir-verified-decided-callees"), "{stderr}");
    std::fs::remove_dir_all(dir).unwrap();
}
