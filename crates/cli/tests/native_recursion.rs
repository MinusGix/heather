//! A pure program with recursion, written as an ELF by `heather write-elf`
//! and run as a Linux process (docs/native/runtime-fn-recursion-design.md
//! §6 step 4; `lib/native/runtime/rt_proc_program.hthr` is its theorem):
//! main computes `sum(10)` by a non-tail recursive procedure and exits with
//! 55 within 16 levels; with 9 levels the tenth nested call is refused and
//! it exits with the call-depth status, 139. The same, generated: a
//! `runtime fn` recursion and a `runtime(levels := 16) fn sum_ten()` that
//! calls it (`lib/_tests/native/runtime/runtime_recursion_tests.hthr`).
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::path::{Path, PathBuf};
use std::process::Command;

use heather_cli::showcase;

const PROBES: &str = "lib/_tests/native/runtime/rt_proc_program_tests.hthr";
const GENERATED: &str = "lib/_tests/native/runtime/runtime_recursion_tests.hthr";

fn write_elf(file: &str, source: &str, output: &Path) {
    let root = showcase::repo_root();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    cmd.current_dir(&root)
        .args(["write-elf", file, source, "-o"])
        .arg(output)
        .arg("--cache-dir").arg(showcase::cli_check_images());
    if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
        cmd.arg("--accept-stale-images");
    }
    let result = cmd.output().unwrap();
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
}

/// A directory of its own under `target/`, for one test's files.
fn scratch(name: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = showcase::repo_root().join(format!("target/native-{name}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn exit_code(file: &str, source: &str) -> Option<i32> {
    let dir = scratch(source);
    let binary = dir.join(source);
    write_elf(file, source, &binary);
    let status = Command::new(&binary).status().unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    status.code()
}

#[test]
fn recursive_sum_exits_with_its_value_within_the_levels() {
    assert_eq!(exit_code(PROBES, "sum_program"), Some(55));
}

#[test]
fn recursive_sum_stops_one_level_short() {
    assert_eq!(exit_code(PROBES, "sum_shallow"), Some(139));
}

#[test]
fn generated_program_exits_with_its_value_within_the_levels() {
    assert_eq!(exit_code(GENERATED, "sum_ten_program"), Some(55));
}

#[test]
fn generated_program_stops_one_level_short() {
    assert_eq!(exit_code(GENERATED, "sum_ten_short"), Some(139));
}
