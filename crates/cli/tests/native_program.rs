//! Whole programs through `compile-x86`'s verified lowering: a function and
//! the functions it calls, compiled by `lower_program` and certified by
//! `compiled_returns`, linked against C references and run.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::process::Command;

#[test]
fn programs_with_calls_execute() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-program-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // Three levels, a call in each arm of a branch, arguments swapped; and
    // values live across two calls of a two-argument leaf.
    let cases = [
        ("program", "program", r#"
static uint64_t twist(uint64_t a, uint64_t b) { return (a - b) ^ b; }
static uint64_t middle(uint64_t a, uint64_t b) { return a < b ? twist(a, b) + a : twist(b, a); }
static uint64_t reference(uint64_t a, uint64_t b) { uint64_t m = middle(b, a); return middle(m, a + b) | twist(a, m); }
"#),
        ("sharing", "caller", r#"
static uint64_t reference(uint64_t left, uint64_t right) {
    uint64_t saved = left | right, first = right - left, second = left - right, shared = first + saved;
    return (shared + shared) + (first + (first + second));
}
"#),
    ];
    for (file, symbol, reference) in cases {
        let assembly = dir.join(format!("{file}.s"));
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .args(["compile-x86", &format!("examples/x86-native/{file}.hthr"), symbol, "-o"]).arg(&assembly)
            .args(["--cache-dir", "target/native-test-images", "--kernel-workers", "1"])
            .output().unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        assert!(String::from_utf8_lossy(&result.stdout).contains("certified program bytes"), "{file} took the verified lowering");
        let certificate = std::fs::read_to_string(dir.join(format!("{file}.certificate.hthr"))).unwrap();
        for claim in ["_lowers()", "_agrees(", "_bytes()", "_entry_at()", "_returns<M>", "compiled_returns<M>(", "CallTo("] {
            assert!(certificate.contains(claim), "{file}: missing {claim}");
        }
        let driver = dir.join(format!("{file}.c"));
        std::fs::write(&driver, format!(r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t {symbol}(uint64_t, uint64_t);
{reference}
int main(void) {{
    uint64_t edges[] = {{0, 1, 2, 9, 10, (UINT64_C(1) << 32) - 1, UINT64_C(1) << 32, UINT64_C(1) << 63, UINT64_MAX}};
    for (unsigned i = 0; i < 9; ++i) for (unsigned j = 0; j < 9; ++j)
        if ({symbol}(edges[i], edges[j]) != reference(edges[i], edges[j])) return 1;
    uint64_t state = 1;
    for (unsigned i = 0; i < 10000; ++i) {{
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t a = state;
        state = state * UINT64_C(6364136223846793005) + 1;
        uint64_t b = i & 1 ? state : state >> (i % 64);
        if ({symbol}(a, b) != reference(a, b)) return 2;
    }}
    puts("10081 pairs passed");
    return 0;
}}
"#)).unwrap();
        let binary = dir.join(file);
        let linked = Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
            .arg(&driver).arg(&assembly).arg("-o").arg(&binary).output().unwrap();
        assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
        let run = Command::new(&binary).output().unwrap();
        assert!(run.status.success(), "{file}: {}", String::from_utf8_lossy(&run.stdout));
    }
    std::fs::remove_dir_all(dir).unwrap();
}
