//! `wc` as a command (docs/native-wc-command-design.md), built as a certified
//! executable: it parses its command line, stats its operands for the width,
//! reads each one with its state kept in registers across the reads, and
//! prints a row of the columns its options select, then a total. The table
//! of §2 is run against the expected output and, where the host has one,
//! against `LC_ALL=C wc` with the same arguments in the same directory; the
//! counts are compared with the whole input's on a sweep of piped inputs.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::Write;
use std::path::Path;
use std::process::{Command, Output, Stdio};

mod native_support;
use native_support::*;

// `wc_command`, the command's bundle, is all a build names.
fn build(directory: &Path, source: &Path) -> Output { build_x86(directory, source, "wc_command", &[], "wc") }

// Whitespace in the C locale, as POSIX has it: GNU also splits at 0xA0
// unless POSIXLY_CORRECT is set (and coreutils 9.4 disagrees with itself on
// other high bytes), so the host is only asked about ASCII inputs.
fn space(byte: u8) -> bool { matches!(byte, b'\t' | b'\n' | 0x0b | 0x0c | b'\r' | b' ') }

// What `wc` prints for one input on a pipe: no name, and seven columns a
// count, since a pipe is not a regular file.
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

/// Where a run's stdin comes from.
#[derive(Clone, Copy)]
enum Input<'a> { Null, File(&'a str), Pipe(&'a [u8]) }

// `program args…` in `directory`, stdin from `input`: its status and stdout.
fn run(program: &Path, directory: &Path, args: &[&str], input: Input) -> Option<(Option<i32>, String)> {
    let mut command = Command::new(program);
    command.args(args).current_dir(directory).env("LC_ALL", "C").stdout(Stdio::piped()).stderr(Stdio::null());
    command.stdin(match input {
        Input::Null => Stdio::null(),
        Input::File(name) => Stdio::from(std::fs::File::open(directory.join(name)).ok()?),
        Input::Pipe(_) => Stdio::piped(),
    });
    let mut child = command.spawn().ok()?;
    let writer = match input {
        Input::Pipe(bytes) => {
            let (mut stdin, bytes) = (child.stdin.take().unwrap(), bytes.to_vec());
            Some(std::thread::spawn(move || { let _ = stdin.write_all(&bytes); }))
        }
        _ => None,
    };
    let output = child.wait_with_output().ok()?;
    if let Some(writer) = writer { writer.join().unwrap(); }
    Some((output.status.code(), String::from_utf8_lossy(&output.stdout).into_owned()))
}

// The host's `wc`, when there is one and it is GNU's.
fn host_wc() -> Option<std::path::PathBuf> {
    let version = Command::new("wc").arg("--version").output().ok()?;
    String::from_utf8_lossy(&version.stdout).contains("GNU coreutils").then(|| "wc".into())
}

// §2's table: f1 is two lines, three words, six bytes; f2 one line, two
// words, twelve bytes; `-l` is a file holding f1's bytes; `d` a directory.
// Each case's command line, stdin, status and stdout; GNU accepts long
// options (§2's deviations), so that case is not asked of the host.
const TABLE: &[(&[&str], Input, i32, &str)] = &[
    (&["f1"], Input::Null, 0, "2 3 6 f1\n"),
    (&["f1", "f2"], Input::Null, 0, " 2  3  6 f1\n 1  2 12 f2\n 3  5 18 total\n"),
    (&["-l", "f1"], Input::Null, 0, "2 f1\n"),
    (&["-lc", "f1"], Input::Null, 0, "2 6 f1\n"),
    (&["-c", "-m", "f1"], Input::Null, 0, "6 6 f1\n"),
    (&["-w", "f1", "f2"], Input::Null, 0, " 3 f1\n 2 f2\n 5 total\n"),
    (&["f1", "nosuch", "f2"], Input::Null, 1, " 2  3  6 f1\n 1  2 12 f2\n 3  5 18 total\n"),
    (&["nosuch", "f2"], Input::Null, 1, " 1  2 12 f2\n 1  2 12 total\n"),
    (&["d"], Input::Null, 1, "      0       0       0 d\n"),
    (&[], Input::Pipe(b"x"), 0, "      0       1       1\n"),
    (&[], Input::File("f1"), 0, "2 3 6\n"),
    (&[], Input::File("d"), 1, "      0       0       0\n"),
    (&["-", "f1"], Input::File("f2"), 0, " 1  2 12 -\n 2  3  6 f1\n 3  5 18 total\n"),
    (&["-", "f1"], Input::Pipe(b"one\n"), 0, "      1       1       4 -\n      2       3       6 f1\n      3       4      10 total\n"),
    (&["--", "-l"], Input::Null, 0, "2 3 6 -l\n"),
    (&["-x"], Input::Null, 1, ""),
    (&["--lines", "f1"], Input::Null, 1, ""),
    (&["f1", "-l"], Input::Null, 0, "2 f1\n"),
    (&["-l", "--", "f1"], Input::Null, 0, "2 f1\n"),
];

// A command whose column counts what another column means, or whose count
// is not what its proof folds, is refused at its own source, and nothing is
// published. Then the command itself, run.
#[test]
fn wc_is_gnu_wc_on_its_command_lines() {
    let directory = scratch("wc");
    for edits in [
        &[("Column('l', λ s => s.lines, wc_lines)", "Column('l', λ s => s.lines, wc_words)")][..],
        &[("Column('w', λ s => s.words, wc_words)", "Column('w', λ s => s.lines, wc_words)")][..],
    ] {
        let source = mistaken(&directory, "wc", edits);
        assert_refused_at(&build(&directory, &source), &source, &[directory.join("wc"), directory.join("wc.certificate.hthr")]);
    }

    let output = build(&directory, &example("wc"));
    assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
    let executable = directory.join("wc");
    let certificate = std::fs::read_to_string(directory.join("wc.certificate.hthr")).unwrap();
    assert!(!directory.join("wc.certificate.unchecked.hthr").exists(), "the refused build's unchecked copy is replaced, then removed");
    for claim in ["_runs(", "_runs_every(", "_stdout(", "_status(", "command_runs(", "_column0_means(", "_code_written(", "_file_correct("] {
        assert!(certificate.contains(claim), "missing {claim}");
    }

    // §2's table, in a directory of its own.
    let cases = directory.join("cases");
    std::fs::create_dir_all(cases.join("d")).unwrap();
    for (name, bytes) in [("f1", &b"a b\nc\n"[..]), ("f2", b"hello world\n"), ("-l", b"a b\nc\n")] {
        std::fs::write(cases.join(name), bytes).unwrap();
    }
    let host = host_wc();
    let mut compared = 0;
    for &(args, input, status, stdout) in TABLE {
        let ran = run(&executable, &cases, args, input).unwrap();
        assert_eq!(ran, (Some(status), stdout.to_string()), "wc {}", args.join(" "));
        if let Some(host) = host.as_ref().filter(|_| !args.iter().any(|a| a.starts_with("--") && a.len() > 2)) {
            assert_eq!(run(host, &cases, args, input).unwrap(), ran, "wc {} against the host's wc", args.join(" "));
            compared += 1;
        }
    }

    // The counts, on a pipe, against the whole input's.
    for (index, input) in inputs().iter().enumerate() {
        let ran = run(&executable, &cases, &[], Input::Pipe(input)).unwrap();
        assert_eq!(ran, (Some(0), expected(input)), "input {index} ({} bytes)", input.len());
        if let Some(host) = host.as_ref().filter(|_| input.is_ascii()) {
            assert_eq!(run(host, &cases, &[], Input::Pipe(input)).unwrap(), ran, "input {index} against the host's wc");
            compared += 1;
        }
    }
    eprintln!("compared with the host's wc on {compared} command lines and inputs");
    let ran = bursts(&executable, BURSTS);
    assert_eq!((ran.status.code(), String::from_utf8_lossy(&ran.stdout).into_owned()), (Some(0), expected(b"one two\nthree  four\n\n")));
    assert_eq!(unwritable_stdout(&executable, Stdio::null(), b"one two\n").status.code(), Some(0));
    let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
    assert_eq!(unwritable_stdout(&executable, Stdio::from(full), b"one two\n").status.code(), Some(1));
    std::fs::remove_dir_all(directory).unwrap();
}

// Bursts, one of them in the middle of a word: the in-word flag has to
// survive the read between.
const BURSTS: &[&[u8]] = &[b"one tw", b"o\nthr", b"", b"ee  ", b"four\n\n"];
