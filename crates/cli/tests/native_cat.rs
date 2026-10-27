//! cat, compiled by the effectful source compiler and written as an ELF by
//! `heather write-elf`, run as a Linux process: it copies stdin to stdout and
//! exits 0, and exits 1 when a read or a write fails
//! (`lib/native/native_cat_executable.hthr` is its theorem). Beside it, a
//! program with no proof of its own gets the compiler's theorem in its
//! certificate, and the programs that theorem would not cover are refused
//! with their reason (issues/native-elf-every-program.md).
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
    let result = write_elf("lib/native/native_cat_executable.hthr", "cat_source", output);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
}

fn write_elf(file: &str, source: &str, output: &Path) -> std::process::Output {
    let root = showcase::repo_root();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    cmd.current_dir(&root)
        .args(["write-elf", file, source, "-o"])
        .arg(output)
        .arg("--cache-dir").arg(showcase::CLI_CHECK_IMAGES);
    if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
        cmd.arg("--accept-stale-images");
    }
    cmd.output().unwrap()
}

/// A directory of its own under `target/`, for one test's files.
fn scratch(name: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = showcase::repo_root().join(format!("target/native-{name}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
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
    assert!(out.stderr.is_empty(), "the program wrote to stderr");
    (out.status.code(), out.stdout)
}

#[test]
fn compiled_cat_runs_as_cat() {
    let dir = scratch("cat");
    let binary = dir.join("cat");
    write_cat(&binary);
    let certificate = std::fs::read_to_string(dir.join("cat.certificate.hthr")).expect("the certificate is published beside the file");
    // cat is long enough that its emission is stated a part at a time, and
    // joined by each of the three (crates/cli/src/native/emission.rs).
    for join in ["Stmt::emit_then_of", "Stmt::emit_repeat_of", "Stmt::emit_branch_of"] {
        assert!(certificate.contains(join), "the certificate joins parts by `{join}`");
    }
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

/// The probes `lib/_tests/native/native_compile_tests.hthr` holds, which
/// import none of the certificate's modules.
const PROBES: &str = "lib/_tests/native/native_compile_tests.hthr";

/// A program that is not cat gets the compiler's theorem with no proof of
/// its own: `head -c 10` copies ten bytes of any longer input and exits 0.
#[test]
fn every_written_program_gets_its_theorem() {
    let dir = scratch("head10");
    let binary = dir.join("head10");
    let result = write_elf(PROBES, "head10", &binary);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let certificate = std::fs::read_to_string(dir.join("head10.certificate.hthr")).unwrap();
    for statement in ["theorem head10_elf_fits()", "theorem head10_elf_simulates("] {
        assert!(certificate.contains(statement), "the certificate states `{statement}`");
    }
    let every: Vec<u8> = (0..700u32).map(|i| (i * 7 % 256) as u8).collect();
    for input in [&b"hello, head\n"[..], &every] {
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!(code, Some(0), "head -c 10 exits 0");
        assert_eq!(out, &input[..10], "and has sent the first ten bytes");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// A program the theorem would not cover is not written, and the refusal
/// says why: past the page, a call not compiled, a leaf past the registers,
/// a byte node in a leaf with others.
#[test]
fn refused_programs_name_their_reason() {
    let dir = scratch("refused");
    for (source, reason) in [
        ("big_cat", "`big_cat` does not fit the I/O page: its words, buffers and scratch range take 4608 bytes and the page holds 4096"),
        ("opens", "`opens` is refused at statement 1, a call: `open` is not compiled yet"),
        ("wide_leaf", "`wide_leaf` is refused at statement 1, a computation: the leaf needs 15 registers, one per input and per node, and the pool holds 14"),
        ("mixed_leaf", "`mixed_leaf` is refused at statement 1, a computation: a leaf with a byte node compiles only as that one node"),
    ] {
        let output = dir.join(source);
        let result = write_elf(PROBES, source, &output);
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(!result.status.success(), "`{source}` is refused");
        assert!(stderr.contains(reason), "`{source}`'s refusal says `{reason}`:\n{stderr}");
        assert!(!output.exists(), "and nothing is written for it");
    }
    std::fs::remove_dir_all(dir).unwrap();
}
