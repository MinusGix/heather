//! The first program with input: `wc -l` built as a certified read-once
//! executable (docs/native-first-program-design.md) with no toolchain on PATH,
//! then run on files and a pipe. The status is compared with the newline count
//! of what the one read returned, as the certificate states it.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn root() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).join("../..") }

fn scratch(name: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = root().join(format!("target/native-{name}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    directory
}

fn build(directory: &Path, needle: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(root()).env("PATH", directory)
        .args(["build-x86", "examples/x86-native/wc_l.hthr", "count_lines", "--read-loop", "--needle", needle,
            "--advance", "line_body_advances", "--spec", "wc_l", "--computes", "count_lines_input", "-o"])
        .arg(directory.join("wc_l")).args(["--cache-dir", "target/native-test-images"]).output().unwrap()
}

// What the certificate promises for a regular file: one read returns its
// first min(len, 4096) bytes, and the status is their newline count's low byte.
fn expected(input: &[u8]) -> i32 {
    (input.iter().take(4096).filter(|&&b| b == b'\n').count() % 256) as i32
}

#[test]
fn wc_l_counts_what_the_read_returned() {
    let directory = scratch("read-loop");
    let output = build(&directory, "10");
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("wc_l");
    let certificate = std::fs::read_to_string(directory.join("wc_l.certificate.hthr")).unwrap();
    for claim in ["_runs(", "_written(", "_file_correct(", "_loop_written("] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut random = |len: usize| -> Vec<u8> {
        (0..len).map(|_| { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; (seed >> 24) as u8 }).collect()
    };
    let mut inputs: Vec<Vec<u8>> = vec![
        b"".to_vec(), b"hello".to_vec(), b"a\nb\nc\n".to_vec(), b"no newline at the end\nsecond".to_vec(),
        vec![b'\n'; 255], vec![b'\n'; 256], vec![b'\n'; 257], vec![b'\n'; 4096], vec![b'x'; 4096],
    ];
    for len in [1, 17, 4095, 4096, 4097, 9000] { inputs.push(random(len)); }
    // Newline at the last byte the read returns, and just past it.
    let mut edge = vec![b'y'; 4097];
    edge[4095] = b'\n';
    edge[4096] = b'\n';
    inputs.push(edge);
    for (index, input) in inputs.iter().enumerate() {
        let path = directory.join(format!("input-{index}"));
        std::fs::write(&path, input).unwrap();
        let status = Command::new(&executable).stdin(std::fs::File::open(&path).unwrap()).status().unwrap();
        assert_eq!(status.code(), Some(expected(input)), "input {index} ({} bytes)", input.len());
    }
    // A pipe: a small write arrives in one read.
    let mut child = Command::new(&executable).stdin(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(b"one\ntwo\n").unwrap();
    assert_eq!(child.wait().unwrap().code(), Some(2));
    std::fs::remove_dir_all(directory).unwrap();
}

// The loop given a byte its specification does not count: the program's
// ReadLoopComputes fact is about newlines, so the certificate is refused and
// nothing is published.
#[test]
fn a_needle_the_specification_does_not_count_is_refused() {
    let directory = scratch("read-loop-refused");
    let output = build(&directory, "32");
    assert!(!output.status.success(), "a space-counting loop was certified against wc_l");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("unbound") && !stderr.contains("ambiguous"), "{stderr}");
    assert!(!directory.join("wc_l").exists() && !directory.join("wc_l.certificate.hthr").exists());
    std::fs::remove_dir_all(directory).unwrap();
}
