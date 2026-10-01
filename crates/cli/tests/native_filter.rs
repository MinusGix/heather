//! `tr -s '\n'` and `tr -d '\r'`, built as certified executables from their
//! stream filters (docs/native-stream-filter-design.md): a step whose output
//! is shorter than its input and, for `tr -s`, depends on the state the
//! earlier bytes left, across reads. The output is compared with the input
//! filtered and, where the host has one, with `LC_ALL=C tr` reading the same
//! input.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::path::Path;
use std::process::{Command, Output, Stdio};

mod native_support;
use native_support::*;

fn build(directory: &Path, name: &str, program: &str) -> Output { build_x86(directory, &example(name), program, &[], name) }

// What `tr -s '\n'` prints: every run of newlines as one.
fn squeezed(input: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    for &b in input { if !(b == b'\n' && out.last() == Some(&b'\n')) { out.push(b); } }
    out
}
// What `tr -d '\r'` prints: the input less its carriage returns.
fn stripped(input: &[u8]) -> Vec<u8> { input.iter().copied().filter(|&b| b != b'\r').collect() }

fn inputs() -> Vec<Vec<u8>> {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut random = |len: usize, alphabet: &[u8]| -> Vec<u8> {
        (0..len).map(|_| { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; alphabet[(seed >> 24) as usize % alphabet.len()] }).collect()
    };
    let mut inputs: Vec<Vec<u8>> = vec![
        b"".to_vec(), b"\n".to_vec(), b"\n\n\n".to_vec(), b"\r\r\r".to_vec(), b"a\r\nb\r\n\r\n".to_vec(), b"a\n\n\nb\n\nc".to_vec(),
    ];
    let bytes: Vec<u8> = (0..=255).collect();
    for len in [1, 17, 4095, 4096, 4097, 9000, 40000] {
        inputs.push(random(len, &bytes));
        inputs.push(random(len, b"\n\n\r\ra"));
    }
    // A run of newlines across each page boundary a read may stop at.
    let mut edge = vec![b'y'; 8193];
    for at in [4094, 4095, 4096, 4097, 8191, 8192] { edge[at] = b'\n'; }
    inputs.push(edge);
    inputs
}

// The host's `tr` on the same input, when there is one.
fn host_tr(args: &[&str], input: &[u8]) -> Option<Vec<u8>> {
    let mut child = Command::new("tr").args(args).env("LC_ALL", "C").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().ok()?;
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let output = child.wait_with_output().ok()?;
    writer.join().unwrap();
    output.status.success().then_some(output.stdout)
}

// The program, run over the inputs, from files and pipes and against the
// host; then its failures.
fn runs(executable: &Path, expected: fn(&[u8]) -> Vec<u8>, host: &[&str]) {
    let mut compared = 0;
    for (index, input) in inputs().iter().enumerate() {
        let path = executable.with_file_name(format!("input-{index}"));
        std::fs::write(&path, input).unwrap();
        let run = Command::new(executable).stdin(std::fs::File::open(&path).unwrap()).output().unwrap();
        assert_eq!(run.status.code(), Some(0), "input {index}");
        assert!(run.stdout == expected(input), "input {index} ({} bytes)", input.len());
        let run = piped(executable, input);
        assert!(run.stdout == expected(input), "input {index} on a pipe");
        if let Some(theirs) = host_tr(host, input) {
            assert!(run.stdout == theirs, "input {index} against the host's tr");
            compared += 1;
        }
    }
    eprintln!("compared with the host's tr {host:?} on {compared} inputs");
    let run = Command::new(executable).stdin(std::fs::File::open("/").unwrap()).output().unwrap();
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(1), b"".as_slice()));
    let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
    assert_eq!(unwritable_stdout(executable, Stdio::from(full), b"one\n").status.code(), Some(1));
}

// The state crosses reads: a newline at the end of one read and one at the
// start of the next are one run.
#[test]
fn tr_squeezes_newline_runs() {
    let directory = scratch("tr-s");
    let output = build(&directory, "tr_s", "tr_s_program");
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("tr_s");
    let certificate = std::fs::read_to_string(directory.join("tr_s.certificate.hthr")).unwrap();
    for claim in ["_runs(", "_runs_every(", "_sends(", "read_filter_runs(", "_code_written(", "_file_correct("] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    runs(&executable, squeezed, &["-s", "\n"]);
    let run = bursts(&executable, &[b"a\n", b"\nb\n", b"", b"\n", b"c"]);
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(0), b"a\nb\nc".as_slice()));
    std::fs::remove_dir_all(directory).unwrap();
}

// A chunk that emits nothing writes nothing: all carriage returns run to the
// end with stdout full and still exit 0.
#[test]
fn tr_deletes_carriage_returns() {
    let directory = scratch("tr-d");
    let output = build(&directory, "tr_d", "tr_d_program");
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("tr_d");
    runs(&executable, stripped, &["-d", "\r"]);
    let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(full), b"\r\r\r").status.code(), Some(0));
    std::fs::remove_dir_all(directory).unwrap();
}
