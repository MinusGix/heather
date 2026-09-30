//! The first program with input: `wc -l` built as a certified executable that
//! reads stdin to its end (docs/native-first-program-design.md,
//! docs/native-read-until-eof-design.md) with no toolchain on PATH, then run
//! on files and on pipes written in bursts. The status and the printed line
//! are compared with the newline count of the whole input, as the certificate
//! states it.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

mod native_support;
use native_support::*;

// `wc_l_program`, the program's bundle, is all a build names.
fn build(directory: &Path, source: &Path, extra: &[&str]) -> Output { build_x86(directory, source, "wc_l_program", extra, "wc_l") }

fn published(directory: &Path) -> [PathBuf; 2] { [directory.join("wc_l"), directory.join("wc_l.certificate.hthr")] }

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

const BURSTS: &[&[u8]] = &[b"one\ntw", b"o\n", b"", b"three", b"\n\n"];

#[test]
fn wc_l_counts_every_line() {
    let directory = scratch("read-loop");
    let output = build(&directory, &example("wc_l"), &[]);
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
    assert_eq!(bursts(&executable, BURSTS).status.code(), Some(4));
    assert_eq!(unreadable_stdin(&executable).status.code(), Some(1));
    std::fs::remove_dir_all(directory).unwrap();
}

// An author's mistakes are refused at the author's source, by the check of
// the program's bundle, and nothing is published: the loop given a byte its
// specification does not count (its ReadEofComputes fact is about newlines),
// and a theorem that is not the step's LoopFolds in its place.
#[test]
fn a_program_that_is_wrong_is_refused_at_its_source() {
    let directory = scratch("read-loop-refused");
    for (fact, edits) in [
        ("count_lines_input", &[("CountProgram(line_body, newline(), wc_l)", "CountProgram(line_body, BitVec::ofNat(32), wc_l)")][..]),
        ("line_body_advances", &[("CountProgram(line_body_advances(), line_body_folds(), count_lines_input)",
            "CountProgram(line_body_advances(), line_body_advances(), count_lines_input)")][..]),
    ] {
        let source = mistaken(&directory, "wc_l", edits);
        let output = build(&directory, &source, &[]);
        assert_refused_at(&output, &source, &published(&directory));
        assert!(String::from_utf8_lossy(&output.stderr).contains(fact), "refused elsewhere than at `{fact}`");
    }
    std::fs::remove_dir_all(directory).unwrap();
}

// With `--print`, the count is the output: its decimal digits and a newline
// on stdout, as `decimal_line(wc_l(eof_input(chunks)))` states it, and the
// exit is 0; a failed read or write exits 1.
#[test]
fn wc_l_prints_every_line() {
    let directory = scratch("read-print");
    let output = build(&directory, &example("wc_l"), &["--print"]);
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
    let run = bursts(&executable, BURSTS);
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(0), b"4\n".as_slice()));
    let run = unreadable_stdin(&executable);
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(1), b"".as_slice()));
    assert_eq!(unwritable_stdout(&executable, Stdio::null(), b"one\n").status.code(), Some(0));
    let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(full), b"one\n").status.code(), Some(1));
    let closed = std::fs::File::open("/").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(closed), b"one\n").status.code(), Some(1));
    std::fs::remove_dir_all(directory).unwrap();
}
