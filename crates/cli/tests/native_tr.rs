//! `tr a-z A-Z`, built as a certified executable that reads stdin a page at a
//! time, maps each chunk in place through its byte map and writes it before
//! the next read (docs/native-tr-design.md, docs/native-stream-filter-design.md:
//! a stream filter that keeps nothing). The output is compared with the input
//! mapped and, where the host has one, with `LC_ALL=C tr a-z A-Z` reading the
//! same input.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Output, Stdio};

mod native_support;
use native_support::*;

// The program's bundle is all a build names.
fn build(directory: &Path, function: &str, extra: &[&str]) -> Output { build_x86(directory, &example("tr"), function, extra, "tr") }

fn upcase(input: &[u8]) -> Vec<u8> { input.iter().map(|b| b.to_ascii_uppercase()).collect() }

fn inputs() -> Vec<Vec<u8>> {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut random = |len: usize| -> Vec<u8> {
        (0..len).map(|_| { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; (seed >> 24) as u8 }).collect()
    };
    let mut inputs: Vec<Vec<u8>> = vec![
        b"".to_vec(), b"a".to_vec(), b"hello, World!\n".to_vec(), b"`az{ AZ@".to_vec(), (0..=255).collect(),
    ];
    // Each side of every page boundary a read may stop at, and well past one.
    for len in [4095, 4096, 4097, 8192, 8193, 100_003] {
        inputs.push(random(len));
    }
    inputs
}

// The host's `tr` on the same input, when there is one.
fn host_tr(input: &[u8]) -> Option<Vec<u8>> {
    let mut child = Command::new("tr").args(["a-z", "A-Z"]).env("LC_ALL", "C")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().ok()?;
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let output = child.wait_with_output().ok()?;
    writer.join().unwrap();
    output.status.success().then_some(output.stdout)
}

// A chunk is written before the next is read: with stdin held open, the
// first burst's image arrives while the program waits on its next read.
fn streams(executable: &Path) -> (Vec<u8>, Output) {
    let mut child = Command::new(executable).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let mut stdout = child.stdout.take().unwrap();
    stdin.write_all(b"first burst\n").unwrap();
    stdin.flush().unwrap();
    let mut early = vec![0u8; 12];
    stdout.read_exact(&mut early).unwrap();
    stdin.write_all(b"second\n").unwrap();
    drop(stdin);
    let mut rest = Vec::new();
    stdout.read_to_end(&mut rest).unwrap();
    early.extend(rest);
    (early, child.wait_with_output().unwrap())
}

// A byte map named on its own (not a program), and a program given `--arg`s
// (a function of two arguments), are refused before anything is certified,
// and nothing is published. Then the program itself, run.
#[test]
fn tr_maps_stdin_to_stdout() {
    let directory = scratch("tr");
    for (function, extra, reason) in [("upcase", &[][..], "is not a Filter program"), ("tr_program", &["--arg", "1"][..], "two --arg values")] {
        let output = build(&directory, function, extra);
        assert!(!output.status.success(), "{function} {extra:?} was certified");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains(reason), "{stderr}");
        assert!(!directory.join("tr").exists() && !directory.join("tr.certificate.hthr").exists());
    }

    let output = build(&directory, "tr_program", &[]);
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("tr");
    let certificate = std::fs::read_to_string(directory.join("tr.certificate.hthr")).unwrap();
    for claim in ["_runs(", "_runs_every(", "_sends(", "read_filter_runs(", "filter_quiet_tail(", "_code_written(", "_file_correct("] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    let mut compared = 0;
    for (index, input) in inputs().iter().enumerate() {
        let path = directory.join(format!("input-{index}"));
        std::fs::write(&path, input).unwrap();
        let run = Command::new(&executable).stdin(std::fs::File::open(&path).unwrap()).output().unwrap();
        assert_eq!(run.status.code(), Some(0), "input {index}");
        assert!(run.stdout == upcase(input), "input {index} ({} bytes)", input.len());
        let run = piped(&executable, input);
        assert!(run.stdout == upcase(input), "input {index} on a pipe");
        if let Some(host) = host_tr(input) {
            assert!(run.stdout == host, "input {index} against the host's tr");
            compared += 1;
        }
    }
    eprintln!("compared with the host's tr on {compared} inputs");
    let (streamed, run) = streams(&executable);
    assert_eq!((run.status.code(), streamed.as_slice()), (Some(0), b"FIRST BURST\nSECOND\n".as_slice()));
    let run = Command::new(&executable).stdin(std::fs::File::open("/").unwrap()).output().unwrap();
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(1), b"".as_slice()));
    assert_eq!(unwritable_stdout(&executable, Stdio::null(), b"one two\n").status.code(), Some(0));
    let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(full), b"one two\n").status.code(), Some(1));
    std::fs::remove_dir_all(directory).unwrap();
}
