//! `wc`, built as a certified executable that reads stdin to its end with its
//! state kept in registers across the reads, and prints lines, words and bytes
//! as GNU `wc` prints them on a pipe (docs/native-wc-design.md). The output is
//! compared with the counts of the whole input and, where the host has one,
//! with `LC_ALL=C POSIXLY_CORRECT=1 wc` reading the same pipe.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::path::Path;
use std::process::{Command, Output, Stdio};

mod native_support;
use native_support::*;

// `wc_program`, the program's bundle, is all a build names.
fn build(directory: &Path, source: &Path) -> Output { build_x86(directory, source, "wc_program", &[], "wc") }

// Whitespace in the C locale, as POSIX has it: GNU also splits at 0xA0 unless
// POSIXLY_CORRECT is set.
fn space(byte: u8) -> bool { matches!(byte, b'\t' | b'\n' | 0x0b | 0x0c | b'\r' | b' ') }

// What `wc` prints on a pipe: seven columns a count, one space between.
fn expected(input: &[u8]) -> String {
    let lines = input.iter().filter(|&&b| b == b'\n').count();
    let words = input.split(|&b| space(b)).filter(|piece| !piece.is_empty()).count();
    format!("{lines:7} {words:7} {:7}\n", input.len())
}

fn inputs() -> Vec<Vec<u8>> {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut random = |len: usize, alphabet: &[u8]| -> Vec<u8> {
        (0..len).map(|_| { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; alphabet[(seed >> 24) as usize % alphabet.len()] }).collect()
    };
    let mut inputs: Vec<Vec<u8>> = vec![
        b"".to_vec(), b"hello".to_vec(), b"hello world\n".to_vec(), b"  leading and trailing  ".to_vec(),
        b"a\tb\nc\x0bd\x0ce\rf g".to_vec(), b"\x00\x01 \xa0 \xff\n".to_vec(), vec![b' '; 4096], vec![b'x'; 4096],
    ];
    let bytes: Vec<u8> = (0..=255).collect();
    for len in [1, 17, 4095, 4096, 4097, 9000, 40000] {
        inputs.push(random(len, &bytes));
        inputs.push(random(len, b"ab \n\t"));
    }
    // A word on each side of every page boundary a read may stop at, and one
    // across it.
    let mut edge = vec![b'y'; 8193];
    for at in [4094, 4096, 8191] { edge[at] = b' '; }
    inputs.push(edge);
    inputs
}

// The host's `wc` on a pipe, when there is one.
fn host_wc(input: &[u8]) -> Option<String> {
    let mut child = Command::new("wc").env("LC_ALL", "C").env("POSIXLY_CORRECT", "1")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().ok()?;
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let output = child.wait_with_output().ok()?;
    writer.join().unwrap();
    output.status.success().then(|| String::from_utf8_lossy(&output.stdout).into_owned())
}

// Bursts, one of them in the middle of a word: the in-word flag has to
// survive the read between.
const BURSTS: &[&[u8]] = &[b"one tw", b"o\nthr", b"", b"ee  ", b"four\n\n"];

// A program whose printed counts are named in another order than its proof
// states them, or whose counts are listed in another order than its proof
// bounds them, is refused at its own source, and nothing is published. Then
// the program itself, run.
#[test]
fn wc_counts_lines_words_and_bytes() {
    let directory = scratch("wc");
    for edits in [
        &[("wc_lines, wc_words, wc_bytes) {", "wc_words, wc_lines, wc_bytes) {")][..],
        &[("[λ s => s.lines, λ s => s.words, λ s => s.bytes]", "[λ s => s.words, λ s => s.lines, λ s => s.bytes]")][..],
    ] {
        let source = mistaken(&directory, "wc", edits);
        assert_refused_at(&build(&directory, &source), &source, &[directory.join("wc"), directory.join("wc.certificate.hthr")]);
    }

    let output = build(&directory, &example("wc"));
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("wc");
    let certificate = std::fs::read_to_string(directory.join("wc.certificate.hthr")).unwrap();
    assert!(!directory.join("wc.certificate.unchecked.hthr").exists(), "the refused build's unchecked copy is replaced, then removed");
    for claim in ["_runs(", "_runs_every(", "three_fields_line(", "_code_written(", "_file_correct("] {
        assert!(certificate.contains(claim), "missing {claim}");
    }
    let mut compared = 0;
    for (index, input) in inputs().iter().enumerate() {
        let path = directory.join(format!("input-{index}"));
        std::fs::write(&path, input).unwrap();
        let run = Command::new(&executable).stdin(std::fs::File::open(&path).unwrap()).output().unwrap();
        assert_eq!(run.status.code(), Some(0), "input {index}");
        assert_eq!(String::from_utf8_lossy(&run.stdout), expected(input), "input {index} ({} bytes)", input.len());
        let run = piped(&executable, input);
        assert_eq!(String::from_utf8_lossy(&run.stdout), expected(input), "input {index} on a pipe");
        if let Some(host) = host_wc(input) {
            assert_eq!(String::from_utf8_lossy(&run.stdout), host, "input {index} against the host's wc");
            compared += 1;
        }
    }
    eprintln!("compared with the host's wc on {compared} inputs");
    let run = bursts(&executable, BURSTS);
    assert_eq!((run.status.code(), String::from_utf8_lossy(&run.stdout).into_owned()), (Some(0), expected(b"one two\nthree  four\n\n")));
    let run = Command::new(&executable).stdin(std::fs::File::open("/").unwrap()).output().unwrap();
    assert_eq!((run.status.code(), run.stdout.as_slice()), (Some(1), b"".as_slice()));
    assert_eq!(unwritable_stdout(&executable, Stdio::null(), b"one two\n").status.code(), Some(0));
    let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(full), b"one two\n").status.code(), Some(1));
    std::fs::remove_dir_all(directory).unwrap();
}
