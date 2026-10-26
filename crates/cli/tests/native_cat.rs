//! cat, compiled by the effectful source compiler and written as an ELF by
//! `heather write-elf`, run as a Linux process: it copies stdin to stdout and
//! exits 0, and exits 1 when a read or a write fails
//! (`lib/native/native_cat_executable.hthr` is its theorem).
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use heather_cli::showcase;

/// One `write-elf` of cat through the library gate's image store, its
/// closure in its own load order, as the suite's CLI image warmup builds it.
/// In the suite's stale lanes it replays images an earlier build wrote, as
/// the gate does: without that, every compiler edit made this test rebuild
/// the whole closure from source.
///
/// Not over the gate's world (`docs/library-world-design.md`): the world's
/// front is most of the library, which one process building it alone (the
/// warmup, on a cold store) cannot fit under the CPU rail beside cat's
/// certificate.
fn write_cat(output: &Path) {
    let root = showcase::repo_root();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    cmd.current_dir(&root)
        .args(["write-elf", "lib/native/native_cat_executable.hthr", "cat_source", "-o"])
        .arg(output)
        .arg("--cache-dir").arg(showcase::CLI_CHECK_IMAGES);
    if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
        cmd.arg("--accept-stale-images");
    }
    let result = cmd.output().unwrap();
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
}

fn run(binary: &Path, input: &[u8], stdout: Stdio) -> (Option<i32>, Vec<u8>) {
    let mut child = Command::new(binary).stdin(Stdio::piped()).stdout(stdout).stderr(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    // A writer of its own, so a large input cannot deadlock against a full
    // stdout pipe.
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    assert!(out.stderr.is_empty(), "cat wrote to stderr");
    (out.status.code(), out.stdout)
}

#[test]
fn compiled_cat_runs_as_cat() {
    let root = showcase::repo_root();
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir: PathBuf = root.join(format!("target/native-cat-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let binary = dir.join("cat");
    write_cat(&binary);
    assert!(dir.join("cat.certificate.hthr").exists(), "the certificate is published beside the file");
    assert!(!dir.join("cat.certificate.unchecked.hthr").exists(), "and no unchecked copy is left");
    let file = std::fs::read(&binary).unwrap();
    assert_eq!(&file[..4], b"\x7fELF");

    // Nothing, a line, and more than one buffer's worth of every byte value.
    let every: Vec<u8> = (0..5000u32).map(|i| (i * 7 % 256) as u8).collect();
    for input in [&b""[..], b"hello, cat\n", &every] {
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!(code, Some(0), "cat exits 0 at the end of its input");
        assert_eq!(out, input, "and has sent what it read");
    }

    // A write that fails: stdout is full.
    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&binary, b"no room\n", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
    }

    // A read that fails: stdin is a directory.
    let status = Command::new(&binary).stdin(std::fs::File::open(&dir).unwrap()).stdout(Stdio::null()).status().unwrap();
    assert_eq!(status.code(), Some(1), "a failed read exits 1");

    std::fs::remove_dir_all(dir).unwrap();
}
