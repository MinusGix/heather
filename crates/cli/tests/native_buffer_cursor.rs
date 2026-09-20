//! Runtime bytes and cursors exercise one compiled source recognizer.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::path::Path;
use std::process::Command;
#[path = "../src/native/support.rs"]
mod support;

#[test]
fn slow_acceptance_buffer_cursor_runtime_inputs() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = root.join(format!("target/native-buffer-cursor-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let assembly = directory.join("recognize.s");
    let built = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
        .args(["compile-x86", "examples/x86-native/recognize_plus.hthr", "recognize_plus", "--buffer-cursor", "-o"])
        .arg(&assembly).args(["--cache-dir", "target/native-test-images"]).output().unwrap();
    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
    let executable = directory.join("recognize");
    let linked = Command::new("cc").current_dir(&root).args(["-std=c11", "-Wall", "-Wextra", "-Werror", "examples/x86-native/recognize_main.c"])
        .arg(&assembly).arg("-o").arg(&executable).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    for (input, cursor, expected) in [("+", "0", "match 1\n"), ("x", "0", "mismatch 0\n"),
        ("", "0", "end 0\n"), ("x+z", "1", "match 2\n"), ("+", "1", "end 1\n"),
        ("+", "18446744073709551615", "end 18446744073709551615\n")] {
        let output = Command::new(&executable).args([input, cursor]).output().unwrap();
        assert!(output.status.success());
        assert_eq!(String::from_utf8_lossy(&output.stdout), expected);
    }
    let full = "+".repeat(256);
    let output = Command::new(&executable).args([&full, "255"]).output().unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, b"match 256\n");
    assert_eq!(Command::new(&executable).arg("+".repeat(257)).status().unwrap().code(), Some(65));
    let harness = directory.join("controls.c");
    std::fs::write(&harness, r#"
#define _GNU_SOURCE
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
struct reply { uint64_t status, next; };
extern struct reply recognize_plus(const unsigned char *, uint64_t, uint64_t);
int main(void) {
    unsigned char data[256], original[256];
    for (unsigned byte = 0; byte < 256; ++byte) {
        memset(data, (int)byte, sizeof data);
        memcpy(original, data, sizeof data);
        for (unsigned cursor = 0; cursor < 256; ++cursor) {
            struct reply r = recognize_plus(data, 256, cursor);
            if (r.status != (byte == '+' ? 0u : 1u) || r.next != cursor + (byte == '+')) return 1;
        }
        if (memcmp(data, original, sizeof data)) return 2;
    }
    long page = sysconf(_SC_PAGESIZE);
    if (page <= 0) return 3;
    unsigned char *memory = mmap(0, (size_t)page * 2, PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (memory == MAP_FAILED || mprotect(memory + page, (size_t)page, PROT_NONE)) return 4;
    memory[page - 1] = '+';
    struct reply r = recognize_plus(memory + page - 1, 1, 0);
    if (r.status || r.next != 1) return 5;
    r = recognize_plus(memory + page - 1, 1, 1);
    if (r.status != 2 || r.next != 1) return 6;
    r = recognize_plus(memory + page, 0, 0);
    if (r.status != 2 || r.next) return 7;
    r = recognize_plus(0, 0, UINT64_MAX);
    if (r.status != 2 || r.next != UINT64_MAX) return 8;
    return munmap(memory, (size_t)page * 2) ? 9 : 0;
}
"#).unwrap();
    let controls = directory.join("controls");
    let linked = Command::new("cc").args(["-std=c11", "-Wall", "-Wextra", "-Werror"])
        .arg(&harness).arg(&assembly).arg("-o").arg(&controls).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    assert!(Command::new(&controls).status().unwrap().success());
    // Standalone replay plus controls use the same bundled models, under the
    // ordinary checker. Every changed declaration must be refused, not merely
    // fail because a source import or premise name went missing.
    for &(name, source) in support::SUPPORT.iter().chain(support::BUFFER_SUPPORT) {
        std::fs::write(directory.join(format!("{name}.hthr")), source).unwrap();
    }
    let source_path = directory.join("recognize_plus.hthr");
    let source = include_str!("../../../examples/x86-native/recognize_plus.hthr");
    std::fs::write(&source_path, source).unwrap();
    let certificate = std::fs::read_to_string(directory.join("recognize.certificate.hthr")).unwrap();
    let check = |name: &str, text: &str, accepted: bool| {
        let path = directory.join(format!("{name}.hthr"));
        std::fs::write(&path, text).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .args(["check", "--cache-dir", "target/native-test-images", "-L"]).arg(&directory).arg(&path).output().unwrap();
        let diagnostic = String::from_utf8_lossy(&result.stderr);
        if accepted { assert!(result.status.success(), "{name}: {diagnostic}"); }
        else {
            assert!(!result.status.success(), "accepted {name}");
            assert!(!diagnostic.contains("OutOfFuel"), "{name}: {diagnostic}");
            if name == "stale_source" {
                assert!(diagnostic.contains("this has type") && diagnostic.contains("source_expansion_3"), "{name}: {diagnostic}");
            } else { assert!(diagnostic.contains("NotConvertible"), "{name}: {diagnostic}"); }
        }
    };
    check("valid_cursor", &certificate, true);
    for (name, original, replacement) in [
        ("wrong_byte", "bitvec::ofNat(8, 115)", "bitvec::ofNat(8, 116)"),
        ("missing_read_permission", "readable(selected)", "readable(refl)"),
        ("wrong_cursor", " = read_gpr(Rdx, before.gprs)", " = bitvec::zero(64)"),
    ] {
        assert!(certificate.contains(original), "mutation anchor {original}");
        check(name, &certificate.replacen(original, replacement, 1), false);
    }
    let size: usize = std::fs::read_to_string(&assembly).unwrap().lines()
        .filter_map(|line| line.trim().strip_prefix(".byte ")).map(|line| line.split(',').count()).sum();
    let original = format!("fn recognize_plus_native_empty_target_offset() -> Nat {{ {} }}", size - 10);
    let replacement = format!("fn recognize_plus_native_empty_target_offset() -> Nat {{ {} }}", size - 9);
    assert!(certificate.contains(&original));
    check("wrong_branch_target", &certificate.replacen(&original, &replacement, 1), false);
    std::fs::write(&source_path, source.replace("ofNat(64, 43)", "ofNat(64, 45)")).unwrap();
    check("stale_source", &certificate, false);
    let rejected = directory.join("rejected.s");
    let compile_rejected = |file: &Path, function: &str, message: &str| {
        let output = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .arg("compile-x86").arg(file).arg(function).args(["--buffer-cursor", "-o"]).arg(&rejected)
            .arg("-L").arg(&directory).args(["--cache-dir", "target/native-test-images"]).output().unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains(message), "{}", String::from_utf8_lossy(&output.stderr));
        assert!(!rejected.exists());
        assert!(!rejected.with_extension("certificate.hthr").exists());
    };
    std::fs::write(&source_path, format!("import byte_cursor;\n{source}")).unwrap();
    let library = directory.join("byte_cursor.hthr");
    let mut changed = std::fs::read_to_string(&library).unwrap();
    changed.push_str("\n// not the bundled model\n");
    std::fs::write(&library, changed).unwrap();
    compile_rejected(&source_path, "recognize_plus", "differs from the compiler's bundled proof library");
    let wide = directory.join("wide.hthr");
    let mut expression = "byte".to_string();
    for n in 1..=12 { expression = format!("bitvec::bxor(64, {expression}, bitvec::ofNat(64, {n}))"); }
    std::fs::write(&wide, format!("import bitvec; fn wide(byte: BitVec(64), cursor: BitVec(64)) -> BitVec(64) {{ {expression} }}")).unwrap();
    compile_rejected(&wide, "wide", "exceeds the forward short-branch span");
    std::fs::remove_dir_all(directory).unwrap();
}
