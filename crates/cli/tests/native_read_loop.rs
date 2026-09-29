//! The first program with input: `wc -l` built as a certified executable that
//! reads stdin to its end (docs/native-first-program-design.md,
//! docs/native-read-until-eof-design.md) with no toolchain on PATH, then run
//! on files and on pipes written in bursts. The status and the printed line
//! are compared with the newline count of the whole input, as the certificate
//! states it.
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

fn build(directory: &Path, needle: &str) -> Output { build_with(directory, needle, &[]) }

fn build_with(directory: &Path, needle: &str, extra: &[&str]) -> Output {
    build_raw(directory, needle, &[&["--folds", "line_body_folds"], extra].concat())
}

fn build_raw(directory: &Path, needle: &str, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(root()).env("PATH", directory)
        .args(["build-x86", "examples/x86-native/wc_l.hthr", "count_lines", "--read-loop", "--needle", needle,
            "--advance", "line_body_advances", "--spec", "wc_l", "--computes", "count_lines_input"]).args(extra).arg("-o")
        .arg(directory.join("wc_l")).args(["--cache-dir", "target/native-test-images"]).output().unwrap()
}

fn inputs() -> Vec<Vec<u8>> {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut random = |len: usize| -> Vec<u8> {
        (0..len).map(|_| { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; (seed >> 24) as u8 }).collect()
    };
    let mut inputs: Vec<Vec<u8>> = vec![
        b"".to_vec(), b"hello".to_vec(), b"a\nb\nc\n".to_vec(), b"no newline at the end\nsecond".to_vec(),
        vec![b'\n'; 255], vec![b'\n'; 256], vec![b'\n'; 257], vec![b'\n'; 4096], vec![b'x'; 4096],
    ];
    for len in [1, 17, 4095, 4096, 4097, 9000, 40000] { inputs.push(random(len)); }
    // Newlines on both sides of each page boundary a read may stop at.
    let mut edge = vec![b'y'; 8193];
    for at in [4095, 4096, 8191, 8192] { edge[at] = b'\n'; }
    inputs.push(edge);
    // A count of each width the line prints: 1, 2, 3 and 4 digits, the last
    // across three reads.
    for count in [9, 10, 99, 100, 999, 1000, 9999] { inputs.push(vec![b'\n'; count]); }
    inputs
}

// What `wc -l` prints: every newline, however many reads it took.
fn newlines(input: &[u8]) -> usize { input.iter().filter(|&&b| b == b'\n').count() }

// The status: the count's low byte.
fn expected(input: &[u8]) -> i32 { (newlines(input) % 256) as i32 }

// A pipe written in bursts, so the reads return pieces: the program must
// keep reading until the writer closes it.
fn bursts(executable: &Path) -> Output {
    let mut child = Command::new(executable).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    for piece in [&b"one\ntw"[..], b"o\n", b"", b"three", b"\n\n"] {
        stdin.write_all(piece).unwrap();
        stdin.flush().unwrap();
        std::thread::sleep(std::time::Duration::from_millis(30));
    }
    drop(stdin);
    child.wait_with_output().unwrap()
}

// Failures (docs/native-syscall-failures-design.md): a read of a directory
// fails with EISDIR, a write to a descriptor open only for reading with EBADF,
// and a write to `/dev/full` with ENOSPC. Each exits 1.
fn unreadable_stdin(executable: &Path) -> Output {
    Command::new(executable).stdin(std::fs::File::open("/").unwrap()).output().unwrap()
}
fn unwritable_stdout(executable: &Path, stdout: Stdio) -> Output {
    let mut child = Command::new(executable).stdin(Stdio::piped()).stdout(stdout).spawn().unwrap();
    child.stdin.take().unwrap().write_all(b"one\n").unwrap();
    child.wait_with_output().unwrap()
}

#[test]
fn wc_l_counts_every_line() {
    let directory = scratch("read-loop");
    let output = build(&directory, "10");
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("wc_l");
    let certificate = std::fs::read_to_string(directory.join("wc_l.certificate.hthr")).unwrap();
    for claim in ["_runs(", "_runs_every(", "_written(", "_file_correct(", "_code_written(", "read_count_runs("] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    for (index, input) in inputs().iter().enumerate() {
        let path = directory.join(format!("input-{index}"));
        std::fs::write(&path, input).unwrap();
        let status = Command::new(&executable).stdin(std::fs::File::open(&path).unwrap()).status().unwrap();
        assert_eq!(status.code(), Some(expected(input)), "input {index} ({} bytes)", input.len());
    }
    assert_eq!(bursts(&executable).status.code(), Some(4));
    assert_eq!(unreadable_stdin(&executable).status.code(), Some(1));
    std::fs::remove_dir_all(directory).unwrap();
}

// The loop given a byte its specification does not count: the program's
// ReadEofComputes fact is about newlines, so the certificate is refused and
// nothing is published. What was checked stays, under its unchecked name, and
// the refusal points into it.
#[test]
fn a_needle_the_specification_does_not_count_is_refused() {
    let directory = scratch("read-loop-refused");
    let output = build(&directory, "32");
    assert!(!output.status.success(), "a space-counting loop was certified against wc_l");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("unbound") && !stderr.contains("ambiguous"), "{stderr}");
    assert!(!directory.join("wc_l").exists() && !directory.join("wc_l.certificate.hthr").exists());
    let unchecked = std::fs::read_to_string(directory.join("wc_l.certificate.unchecked.hthr")).unwrap();
    assert!(unchecked.contains("count_lines_native_runs"), "the certificate that was checked");
    assert!(stderr.contains("--> ") && stderr.contains("wc_l.certificate.unchecked.hthr:"), "{stderr}");
    std::fs::remove_dir_all(directory).unwrap();
}

// With `--print`, the count is the output: its decimal digits and a newline
// on stdout, as `decimal_line(wc_l(eof_input(chunks)))` states it, and the
// exit is 0; a failed read or write exits 1.
#[test]
fn wc_l_prints_every_line() {
    let directory = scratch("read-print");
    let output = build_with(&directory, "10", &["--print"]);
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("wc_l");
    let certificate = std::fs::read_to_string(directory.join("wc_l.certificate.hthr")).unwrap();
    assert!(!certificate.contains("Nat::le_antisym"), "size equality must use refl");
    for claim in ["_runs(", "_runs_every(", "write_events(", "decimal_line(", "_code_written(", "_file_correct(", "read_count_print_runs("] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    for (index, input) in inputs().iter().enumerate() {
        let path = directory.join(format!("input-{index}"));
        std::fs::write(&path, input).unwrap();
        let run = Command::new(&executable).stdin(std::fs::File::open(&path).unwrap()).output().unwrap();
        assert_eq!(run.status.code(), Some(0), "input {index}");
        assert_eq!(String::from_utf8_lossy(&run.stdout), format!("{}\n", newlines(input)), "input {index} ({} bytes)", input.len());
    }
    let run = bursts(&executable);
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(0), b"4\n".as_slice()));
    let run = unreadable_stdin(&executable);
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(1), b"".as_slice()));
    assert_eq!(unwritable_stdout(&executable, Stdio::null()).status.code(), Some(0));
    let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(full)).status.code(), Some(1));
    let closed = std::fs::File::open("/").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(closed)).status.code(), Some(1));
    std::fs::remove_dir_all(directory).unwrap();
}

// Counting chunk by chunk needs the program's proof that its step folds
// (docs/native-wc-design.md §3): without it the build is refused, and with
// another theorem in its place the certificate is refused where the fact is
// used, not by a missing name.
#[test]
fn read_loop_needs_its_folds() {
    let directory = scratch("read-loop-no-folds");
    let output = build_raw(&directory, "10", &[]);
    assert!(!output.status.success() && String::from_utf8_lossy(&output.stderr).contains("--folds"));
    assert!(!directory.join("wc_l").exists());
    let output = build_raw(&directory, "10", &["--folds", "line_body_advances"]);
    assert!(!output.status.success(), "a theorem that is not LoopFolds was accepted as --folds");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("unbound") && !stderr.contains("ambiguous"), "{stderr}");
    assert!(!directory.join("wc_l").exists());
    std::fs::remove_dir_all(directory).unwrap();
}

