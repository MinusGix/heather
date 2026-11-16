//! The in-place sort example (`examples/sort`): its proofs check, it compiles
//! to x86, links with its C driver, and on every input it writes what Rust's
//! `slice::sort` writes.
//!
//! The theorems (`sort_in_place_sorts`, `sort_in_place_is_insertion_sort`)
//! say the result is the input's bytes in ascending order; this test runs the
//! binary the example's README tells a reader to build.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::process::{Command, Stdio};

fn run(binary: &std::path::Path, bytes: &[u8]) -> Vec<u8> {
    let mut child = Command::new(binary).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(bytes).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success());
    out.stdout
}

/// Inputs: empty, one byte, all alike, already sorted, reversed, both ends of
/// the byte range, and deterministic pseudorandom spans of every length up
/// to 100 over narrow and wide alphabets.
fn cases() -> Vec<Vec<u8>> {
    let mut cases: Vec<Vec<u8>> = vec![vec![], vec![0], vec![255], vec![7; 9], vec![255, 0], (0..=255).collect(), (0..=255).rev().collect()];
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for len in 0..100 {
        let spread = 1 + next() % 256;
        cases.push((0..len).map(|_| (next() % spread) as u8).collect());
    }
    cases
}

#[test]
fn sort_agrees_with_slice_sort() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let output = root.join(format!("target/native-sort-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&output).unwrap();
    let assembly = output.join("sort.s");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["compile-x86", "examples/sort/sort.hthr", "sort_in_place", "-o"])
        .arg(&assembly).arg("--cache-dir").arg(heather_cli::showcase::native_test_images())
        .output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let binary = output.join("bytesort");
    let linked = Command::new("cc").current_dir(&root)
        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "examples/sort/main.c"])
        .arg(&assembly).arg("-o").arg(&binary).output().unwrap();
    assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
    for bytes in &cases() {
        let mut expected = bytes.clone();
        expected.sort();
        assert_eq!(run(&binary, bytes), expected, "on {bytes:?}");
    }
    std::fs::remove_dir_all(output).unwrap();
}
