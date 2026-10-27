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

/// One `write-elf` of cat through the library gate's image store, over the
/// gate's world (`--world lib`, `docs/library-world-design.md` §3), so its
/// closure replays what the gate built; the suite's CLI image warmup is the
/// gate, run first. In the suite's stale lanes it replays images an earlier
/// build wrote, as the gate does: without that, every compiler edit made
/// this test rebuild the whole closure from source.
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
        .arg("--cache-dir").arg(showcase::CLI_CHECK_IMAGES)
        .args(["--world", "lib"]);
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

/// A program eight times cat's code over (`cat_x8`, in the probes below)
/// builds, its layout and bytes checked by a table of its labels, and runs
/// as cat: write-elf's build grows with the code, not with its square
/// (issues/native-compile-linear-layout.md).
#[test]
fn larger_program_runs_as_cat() {
    let dir = scratch("cat_x8");
    let binary = dir.join("cat_x8");
    let result = write_elf(PROBES, "cat_x8", &binary);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let certificate = std::fs::read_to_string(dir.join("cat_x8.certificate.hthr")).unwrap();
    for by in ["laid_out_of", "piece_by"] {
        assert!(certificate.contains(by), "the certificate's layout and bytes go by the table (`{by}`)");
    }
    let every: Vec<u8> = (0..20000u32).map(|i| (i * 13 % 256) as u8).collect();
    for input in [&b""[..], b"hello, cat\n", &every] {
        let (code, out) = run(&binary, input, Stdio::piped());
        assert_eq!(code, Some(0), "it exits 0 at the end of its input");
        assert_eq!(out, input, "and has sent what it read");
    }
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

/// Leaves S4 does not take whole compile a node at a time and run: forty
/// nodes summing twenty constants into one word, read and written over its
/// own slot; and a leaf that mixes byte loads and stores with arithmetic
/// (issues/native-compile-wider-leaves.md).
#[test]
fn wider_leaves_run() {
    let dir = scratch("wider");
    let long = dir.join("long_leaf");
    let result = write_elf(PROBES, "long_leaf", &long);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let (code, out) = run(&long, b"", Stdio::piped());
    assert_eq!((code, out.len()), (Some(210), 0), "the forty-node leaf sums 1 to 20");
    let mixed = dir.join("mixed_bytes");
    let result = write_elf(PROBES, "mixed_bytes", &mixed);
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let (code, out) = run(&mixed, b"abcdef", Stdio::piped());
    assert_eq!(out, b"Abcdef", "the first byte stored back, less 32");
    assert_eq!(code, Some((97 + 98 + 99 + 100) % 256), "it exits with the first four bytes' sum");
    std::fs::remove_dir_all(dir).unwrap();
}

/// A program the theorem would not cover is not written, and the refusal
/// says why: past the page, a call not compiled, a leaf past the registers
/// with a node too narrow to go a node at a time, a narrow node beside a
/// byte node.
#[test]
fn refused_programs_name_their_reason() {
    let dir = scratch("refused");
    for (source, reason) in [
        ("big_cat", "`big_cat` does not fit the I/O page: its words, buffers, scratch range and saved RSP take 4616 bytes and the page holds 4096"),
        ("opens", "`opens` is refused at statement 1, a call: `open` is not compiled yet"),
        ("narrow_long_leaf", "`narrow_long_leaf` is refused at statement 1, a computation: the leaf needs 41 registers, one per input and per node, and the pool holds 14; it does not compile a node at a time because a node is not at width 64"),
        ("narrow_mixed_leaf", "`narrow_mixed_leaf` is refused at statement 1, a computation: node 2 of the leaf is not at width 64"),
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
