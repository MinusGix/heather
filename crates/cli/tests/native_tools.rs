//! `tr a-z A-Z`, `yes`, `head -c 10`, `wc -l`, `echo` and `yes STR` over
//! the command line, `cat FILE…` over open and close, and `wc [-clw]` and
//! `head -n N` over decimal output and input, and `grep -F PATTERN` over a
//! procedure (issues/native-compiled-procedures.md), written with the builder (`native_build`),
//! compiled by the effectful source compiler and written as ELFs by
//! `heather write-elf`, run as Linux processes beside GNU's
//! (issues/native-source-bytes.md, issues/native-source-builder.md,
//! issues/native-source-argv.md, issues/native-compile-other-calls.md,
//! issues/native-decimal-io.md), tr through a word function it calls, compiled
//! into the same file (docs/native-one-compiler-design.md), and
//! `heather reflect`'s program of that function
//! (issues/native-build-reflected-helpers.md).
//! None has
//! a theorem of its own: `lib/native/native_tools.hthr` holds only the
//! tools, and `native_compile_correct` is the proof of each.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use heather_cli::showcase;

/// One `write-elf` of `symbol` through the image store native_cat.rs uses,
/// over the gate's world as cat's is (the gate builds it, and the suite starts
/// this target once the images it replays are built), in the stale lanes
/// replaying images an earlier build wrote.
fn write_tool(symbol: &str, output: &Path) { write_program("lib/native/native_tools.hthr", symbol, output, false) }

/// `write_tool` of a program in any module; `both_allocators` has
/// `write-elf` run native_alloc's allocator on its fork beside its own and
/// refuse unless they agree (affordable only for a small tool).
fn write_program(module: &str, symbol: &str, output: &Path, both_allocators: bool) {
    let root = showcase::repo_root();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    if both_allocators {
        cmd.env("HEATHER_ELF_ALLOCATOR", "both");
    }
    cmd.current_dir(&root)
        .args(["write-elf", module, symbol, "-o"])
        .arg(output)
        .arg("--cache-dir").arg(showcase::cli_check_images());
    if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
        cmd.arg("--accept-stale-images");
    }
    let result = cmd.output().unwrap();
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    assert!(!output.with_extension("certificate.unchecked.hthr").exists(), "no unchecked certificate is left");
}

fn scratch(name: &str) -> PathBuf {
    let root = showcase::repo_root();
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("target/native-{name}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A seeded xorshift, the seed printed, so a failing input can be made
/// again.
struct Bytes(u64);

impl Bytes {
    fn seeded(what: &str) -> Bytes {
        let seed = std::env::var("HEATHER_TOOLS_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or_else(|| {
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos() as u64 | 1
        });
        eprintln!("{what}: HEATHER_TOOLS_SEED={seed}");
        Bytes(seed)
    }

    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn take(&mut self, n: usize, of: impl Fn(u64) -> u8) -> Vec<u8> { (0..n).map(|_| of(self.next())).collect() }
}

/// A process on `input`, its exit code and what it wrote.
fn run(program: &mut Command, input: &[u8], stdout: Stdio) -> (Option<i32>, Vec<u8>) {
    let mut child = program.stdin(Stdio::piped()).stdout(stdout).stderr(Stdio::null()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    // A writer of its own, so a large input cannot deadlock against a full
    // stdout pipe.
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    (out.status.code(), out.stdout)
}

fn gnu_tr() -> Command {
    let mut tr = Command::new("tr");
    tr.env("LC_ALL", "C").args(["a-z", "A-Z"]);
    tr
}

#[test]
fn compiled_tr_runs_as_gnu_tr() {
    let dir = scratch("tr");
    let binary = dir.join("tr");
    // write-elf's allocator proposes native_alloc's homes.
    write_program("lib/native/native_tools.hthr", "tr_upper_tool", &binary, true);
    let file = std::fs::read(&binary).unwrap();
    assert_eq!(&file[..4], b"\x7fELF");

    // Nothing, the letters' edges, every byte value past one buffer, and
    // random text and bytes.
    let mut random = Bytes::seeded("tr");
    let every: Vec<u8> = (0..5000u32).map(|i| (i * 7 % 256) as u8).collect();
    let text = random.take(20000, |r| b"abcxyzABCXYZ`{@[ \n019"[(r % 21) as usize]);
    let bytes = random.take(70000, |r| r as u8);
    for input in [&b""[..], b"hello, World! az AZ `{@[\n", &every, &text, &bytes] {
        let (code, out) = run(&mut Command::new(&binary), input, Stdio::piped());
        let (gnu_code, gnu_out) = run(&mut gnu_tr(), input, Stdio::piped());
        assert_eq!(code, Some(0), "tr exits 0 at the end of its input");
        assert_eq!(code, gnu_code, "as GNU's does");
        assert!(out == gnu_out, "and sends what GNU's sends ({} bytes in)", input.len());
    }

    // A write that fails: stdout is full, and both exit 1.
    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&mut Command::new(&binary), b"no room\n", Stdio::from(full.try_clone().unwrap()));
        let (gnu_code, _) = run(&mut gnu_tr(), b"no room\n", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
        assert_eq!(code, gnu_code, "as GNU's does");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

/// tr with each byte through `raise_letter`, a function compiled into the
/// same file and called (docs/native-one-compiler-design.md §2.2): the
/// same outputs as GNU's, and so as the tr above.
#[test]
fn compiled_tr_calling_a_function_runs_as_gnu_tr() {
    let dir = scratch("tr-called");
    let binary = dir.join("tr");
    write_program("lib/native/native_tools.hthr", "tr_upper_called_tool", &binary, true);
    let mut random = Bytes::seeded("tr-called");
    let every: Vec<u8> = (0..5000u32).map(|i| (i * 7 % 256) as u8).collect();
    let text = random.take(20000, |r| b"abcxyzABCXYZ`{@[ \n019"[(r % 21) as usize]);
    let bytes = random.take(70000, |r| r as u8);
    for input in [&b""[..], b"hello, World! az AZ `{@[\n", &every, &text, &bytes] {
        let (code, out) = run(&mut Command::new(&binary), input, Stdio::piped());
        let (gnu_code, gnu_out) = run(&mut gnu_tr(), input, Stdio::piped());
        assert_eq!(code, Some(0), "tr exits 0 at the end of its input");
        assert_eq!(code, gnu_code, "as GNU's does");
        assert!(out == gnu_out, "and sends what GNU's sends ({} bytes in)", input.len());
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// tr with each read's bytes raised by `raise_span`, a function lent the
/// buffer that stores into it and calls `raise_letter` on each byte
/// (docs/native-one-compiler-design.md §2.6): the write after the call
/// sends what the function left, which is what GNU's sends.
#[test]
fn compiled_tr_calling_a_function_that_rewrites_its_buffer_runs_as_gnu_tr() {
    let dir = scratch("tr-span");
    let binary = dir.join("tr");
    write_program("lib/native/native_tools.hthr", "tr_upper_span_tool", &binary, true);
    let mut random = Bytes::seeded("tr-span");
    let every: Vec<u8> = (0..5000u32).map(|i| (i * 7 % 256) as u8).collect();
    let text = random.take(20000, |r| b"abcxyzABCXYZ`{@[ \n019"[(r % 21) as usize]);
    let bytes = random.take(70000, |r| r as u8);
    for input in [&b""[..], b"hello, World! az AZ `{@[\n", &every, &text, &bytes] {
        let (code, out) = run(&mut Command::new(&binary), input, Stdio::piped());
        let (gnu_code, gnu_out) = run(&mut gnu_tr(), input, Stdio::piped());
        assert_eq!(code, Some(0), "tr exits 0 at the end of its input");
        assert_eq!(code, gnu_code, "as GNU's does");
        assert!(out == gnu_out, "and sends what GNU's sends ({} bytes in)", input.len());
    }

    // A write that fails: stdout is full, and both exit 1.
    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&mut Command::new(&binary), b"no room\n", Stdio::from(full.try_clone().unwrap()));
        let (gnu_code, _) = run(&mut gnu_tr(), b"no room\n", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
        assert_eq!(code, gnu_code, "as GNU's does");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

/// A procedure and a function in one file, the procedure's body calling the
/// function and `main` both: 'a' and 'b' raised and summed is the status
/// (`raised_twice_runs`).
#[test]
fn a_procedure_and_a_function_compile_into_one_file() {
    let dir = scratch("raised-twice");
    let binary = dir.join("raised");
    write_program("lib/_tests/native/native_build_tests.hthr", "raised_twice", &binary, false);
    let (code, out) = run(&mut Command::new(&binary), b"", Stdio::piped());
    assert_eq!(code, Some(131));
    assert!(out.is_empty());
    std::fs::remove_dir_all(dir).unwrap();
}

/// A tool that calls a `runtime fn` (`raise_sum`, which calls another): the
/// generator's program of it is compiled into the tool's file and called,
/// and the status is the function's value (`raised_sum_runs`,
/// `raised_sum_status`, lib/_tests/native/runtime/runtime_tool_tests.hthr).
#[test]
fn a_tool_calls_a_runtime_fn() {
    let dir = scratch("raised-sum");
    let binary = dir.join("raised");
    write_program("lib/_tests/native/runtime/runtime_tool_tests.hthr", "raised_sum", &binary, true);
    let (code, out) = run(&mut Command::new(&binary), b"", Stdio::piped());
    assert_eq!(code, Some(131));
    assert!(out.is_empty());
    std::fs::remove_dir_all(dir).unwrap();
}

/// The first `n` bytes a process writes, then the process killed.
fn first_bytes(program: &mut Command, n: usize) -> Vec<u8> {
    let mut child = program.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn().unwrap();
    let mut out = vec![0u8; n];
    child.stdout.take().unwrap().read_exact(&mut out).unwrap();
    let _ = child.kill();
    let _ = child.wait();
    out
}

#[test]
fn compiled_yes_runs_as_gnu_yes() {
    let dir = scratch("yes");
    let binary = dir.join("yes");
    write_tool("yes_tool", &binary);

    // `yes_line()`: what GNU's says given it.
    let mut random = Bytes::seeded("yes");
    for n in [1, 13, 14, 4096, 1 + (random.next() % 100000) as usize] {
        let ours = first_bytes(&mut Command::new(&binary), n);
        let gnu = first_bytes(Command::new("yes").arg("yes, heather"), n);
        assert!(ours == gnu, "the first {n} bytes are GNU's");
    }

    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let status = Command::new(&binary).stdout(Stdio::from(full)).stderr(Stdio::null()).status().unwrap();
        assert_eq!(status.code(), Some(1), "a failed write exits 1");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn compiled_head_runs_as_gnu_head() {
    let dir = scratch("head");
    let binary = dir.join("head");
    write_tool("head_c10_tool", &binary);

    // Shorter than ten bytes, exactly ten, and longer than a buffer.
    let mut random = Bytes::seeded("head");
    let bytes = random.take(70000, |r| r as u8);
    for input in [&b""[..], b"abc", b"0123456789", b"0123456789abcdef", &bytes] {
        let (code, out) = run(&mut Command::new(&binary), input, Stdio::piped());
        let (gnu_code, gnu_out) = run(Command::new("head").args(["-c", "10"]), input, Stdio::piped());
        assert_eq!(code, Some(0), "head exits 0");
        assert_eq!(code, gnu_code, "as GNU's does");
        assert!(out == gnu_out, "and sends what GNU's sends ({} bytes in)", input.len());
    }

    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&mut Command::new(&binary), b"no room\n", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn compiled_wc_counts_lines_as_gnu_wc() {
    let dir = scratch("wc");
    let binary = dir.join("wc");
    write_tool("wc_l_tool", &binary);

    // Its count is its exit status, which Linux keeps the low byte of.
    let mut random = Bytes::seeded("wc");
    let lines = random.take(30000, |r| b"ab\n"[(r % 3) as usize]);
    let bytes = random.take(70000, |r| r as u8);
    for input in [&b""[..], b"no newline", b"one\n", b"\n\n\n", &lines, &bytes] {
        let (code, _) = run(&mut Command::new(&binary), input, Stdio::null());
        let (_, gnu_out) = run(Command::new("wc").arg("-l"), input, Stdio::piped());
        let count: u64 = String::from_utf8(gnu_out).unwrap().trim().parse().unwrap();
        assert_eq!(code, Some((count % 256) as i32), "wc's status is GNU's count ({} bytes in)", input.len());
    }

    std::fs::remove_dir_all(dir).unwrap();
}

/// wc -l with each read's newlines counted by `count_newlines`, a function
/// lent the buffer: compiled into the same file by the function compiler
/// and passed the buffer's address and capacity by the call
/// (docs/native-one-compiler-design.md §2.3). GNU's counts, and so the
/// counts of the wc above, whose loop is the program's own.
#[test]
fn compiled_wc_calling_a_function_over_its_buffer_counts_as_gnu_wc() {
    let dir = scratch("wc-called");
    let binary = dir.join("wc");
    write_program("lib/native/native_tools.hthr", "wc_l_called_tool", &binary, true);

    let mut random = Bytes::seeded("wc-called");
    let lines = random.take(30000, |r| b"ab\n"[(r % 3) as usize]);
    let bytes = random.take(70000, |r| r as u8);
    // Reads of every length up to the buffer's 256 bytes and past it: a
    // newline at each end of a read, and none.
    let ends: Vec<u8> = (0..1024u32).map(|i| if i % 256 == 0 || i % 256 == 255 { b'\n' } else { b'x' }).collect();
    for input in [&b""[..], b"no newline", b"one\n", b"\n\n\n", &ends, &lines, &bytes] {
        let (code, _) = run(&mut Command::new(&binary), input, Stdio::null());
        let (_, gnu_out) = run(Command::new("wc").arg("-l"), input, Stdio::piped());
        let count: u64 = String::from_utf8(gnu_out).unwrap().trim().parse().unwrap();
        assert_eq!(code, Some((count % 256) as i32), "wc's status is GNU's count ({} bytes in)", input.len());
    }

    std::fs::remove_dir_all(dir).unwrap();
}

/// Argument lists GNU's `echo` and `yes` take as text (none starts with
/// `-`, which GNU's read as flags): none, empty ones, spaces and bytes past
/// ASCII inside one, many, and random ones.
fn argument_lists(random: &mut Bytes) -> Vec<Vec<Vec<u8>>> {
    let mut lists: Vec<Vec<Vec<u8>>> = vec![
        vec![],
        vec![b"".to_vec()],
        vec![b"hello".to_vec()],
        vec![b"hello,".to_vec(), b"world".to_vec()],
        vec![b"".to_vec(), b"".to_vec(), b"x".to_vec()],
        vec![b"two  spaces\tand a tab".to_vec(), "h\u{e9}ather \u{3bb}".as_bytes().to_vec()],
        (0..200).map(|i| format!("w{i}").into_bytes()).collect(),
    ];
    for _ in 0..4 {
        let count = (random.next() % 12) as usize;
        lists.push((0..count).map(|_| {
            let len = (random.next() % 40) as usize;
            random.take(len, |r| b"az AZ09.,\t\\\"'*?"[(r % 15) as usize])
        }).collect());
    }
    lists
}

fn with_args(program: impl AsRef<std::ffi::OsStr>, args: &[Vec<u8>]) -> Command {
    use std::os::unix::ffi::OsStrExt;
    let mut cmd = Command::new(program);
    cmd.args(args.iter().map(|a| std::ffi::OsStr::from_bytes(a)));
    cmd
}

#[test]
fn compiled_echo_runs_as_gnu_echo() {
    let dir = scratch("echo");
    let binary = dir.join("echo");
    write_tool("echo_tool", &binary);

    let mut random = Bytes::seeded("echo");
    for args in argument_lists(&mut random) {
        let (code, out) = run(&mut with_args(&binary, &args), b"", Stdio::piped());
        let (gnu_code, gnu_out) = run(&mut with_args("echo", &args), b"", Stdio::piped());
        assert_eq!(code, Some(0), "echo exits 0");
        assert_eq!(code, gnu_code, "as GNU's does");
        assert!(out == gnu_out, "and sends what GNU's sends ({} arguments)", args.len());
    }

    // An argument as long as the buffer is echoed; one byte longer exits 1
    // where it would be written.
    let (code, out) = run(&mut with_args(&binary, &[vec![b'a'; 1024]]), b"", Stdio::piped());
    assert_eq!((code, out.len()), (Some(0), 1025), "an argument the buffer holds is echoed");
    let (code, out) = run(&mut with_args(&binary, &[b"short".to_vec(), vec![b'a'; 1025]]), b"", Stdio::piped());
    assert_eq!((code, out), (Some(1), b"short ".to_vec()), "a longer one exits 1");

    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&mut with_args(&binary, &[b"no room".to_vec()]), b"", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn compiled_yes_takes_its_line_as_gnu_yes() {
    let dir = scratch("yes_args");
    let binary = dir.join("yes");
    write_tool("yes_args_tool", &binary);

    let mut random = Bytes::seeded("yes STR");
    for args in argument_lists(&mut random) {
        let line: usize = args.iter().map(|a| a.len() + 1).sum::<usize>().max(2);
        if line > 1024 {
            continue;
        }
        for n in [1, line, 3 * line + 1, 5000] {
            let ours = first_bytes(&mut with_args(&binary, &args), n);
            let gnu = first_bytes(&mut with_args("yes", &args), n);
            assert!(ours == gnu, "the first {n} bytes are GNU's ({} arguments)", args.len());
        }
    }

    // A line longer than the buffer exits 1 before writing.
    let (code, out) = run(&mut with_args(&binary, &[vec![b'a'; 600], vec![b'b'; 600]]), b"", Stdio::piped());
    assert_eq!((code, out.len()), (Some(1), 0), "a line past the buffer exits 1 with nothing sent");

    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let status = with_args(&binary, &[b"STR".to_vec()]).stdout(Stdio::from(full)).stderr(Stdio::null()).status().unwrap();
        assert_eq!(status.code(), Some(1), "a failed write exits 1");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

/// A process on `input`, its exit code and what it wrote to stdout and
/// stderr.
fn run_both(program: &mut Command, input: &[u8], stdout: Stdio) -> (Option<i32>, Vec<u8>, Vec<u8>) {
    let mut child = program.stdin(Stdio::piped()).stdout(stdout).stderr(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    (out.status.code(), out.stdout, out.stderr)
}

#[test]
fn compiled_cat_files_runs_as_gnu_cat() {
    let dir = scratch("cat_files");
    let binary = dir.join("cat");
    write_tool("cat_files_tool", &binary);

    // Files run from their folder, so the names are short: random bytes
    // past a buffer, text, an empty file, a folder, a name that is not
    // there, a symbolic link to itself, a name too long for Linux and `-`.
    let mut random = Bytes::seeded("cat FILE");
    std::fs::write(dir.join("bytes"), random.take(70000, |r| r as u8)).unwrap();
    std::fs::write(dir.join("text"), random.take(3000, |r| b"ab \n"[(r % 4) as usize])).unwrap();
    std::fs::write(dir.join("empty"), b"").unwrap();
    std::fs::create_dir(dir.join("folder")).unwrap();
    std::os::unix::fs::symlink("loop", dir.join("loop")).unwrap();
    let long = "n".repeat(300);
    let cases: Vec<Vec<&str>> = vec![
        vec![],
        vec!["-"],
        vec!["text"],
        vec!["bytes", "text", "empty"],
        vec!["text", "-", "text"],
        vec!["missing"],
        vec!["text", "missing", "bytes"],
        vec!["folder", "text"],
        vec![&long, "text"],
        vec!["missing", "-", "folder", "empty"],
        vec!["loop", "text"],
    ];
    let input = random.take(5000, |r| r as u8);
    for args in &cases {
        let ours = run_both(Command::new(&binary).current_dir(&dir).args(args), &input, Stdio::piped());
        let gnu = run_both(Command::new("cat").env("LC_ALL", "C").current_dir(&dir).args(args), &input, Stdio::piped());
        assert_eq!(ours.0, gnu.0, "cat {args:?} exits as GNU's does");
        assert!(ours.1 == gnu.1, "cat {args:?} sends what GNU's sends");
        assert_eq!(String::from_utf8_lossy(&ours.2), String::from_utf8_lossy(&gnu.2), "cat {args:?} says what GNU's says");
    }

    // A name longer than the name buffer exits 1 before opening it.
    let longer = "n".repeat(513);
    let (code, out, _) = run_both(Command::new(&binary).current_dir(&dir).args(["text", &longer]), b"", Stdio::piped());
    assert_eq!(code, Some(1), "a name past the buffer exits 1");
    assert!(out == std::fs::read(dir.join("text")).unwrap(), "after the files before it");

    // A write that fails: both say "cat: write error: …" and exit 1.
    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let ours = run_both(Command::new(&binary).current_dir(&dir).arg("text"), b"", Stdio::from(full.try_clone().unwrap()));
        let gnu = run_both(Command::new("cat").env("LC_ALL", "C").current_dir(&dir).arg("text"), b"", Stdio::from(full));
        assert_eq!(ours.0, Some(1), "a failed write exits 1");
        assert_eq!((ours.0, String::from_utf8_lossy(&ours.2)), (gnu.0, String::from_utf8_lossy(&gnu.2)), "as GNU's does, saying what it says");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

/// GNU's `wc` under `LC_ALL=C`, given `args`.
fn gnu_wc(args: &[&str]) -> Command {
    let mut wc = Command::new("wc");
    wc.env("LC_ALL", "C").args(args);
    wc
}

#[test]
fn compiled_wc_prints_counts_as_gnu_wc() {
    let dir = scratch("wc_counts");
    let binary = dir.join("wc");
    write_tool("wc_counts_tool", &binary);

    // Nothing, words between every kind of space, control bytes and bytes
    // past ASCII inside and between words (neither start nor end one),
    // text past a buffer, and random bytes, under every set of flags, one
    // count printed bare and more in columns.
    let mut random = Bytes::seeded("wc");
    let text = random.take(30000, |r| b"ab \t\n\x0b\x0c\r\x01\x7f\x80\xff"[(r % 12) as usize]);
    let bytes = random.take(70000, |r| r as u8);
    let inputs: [&[u8]; 6] = [b"", b"one\n", b"no newline", b"a\tb\x0bc\x0cd\re  f\n\n", b"\x01 a\x80b \xff\x00", &text];
    let flags: [&[&str]; 9] = [&[], &["-c"], &["-l"], &["-w"], &["-l", "-c"], &["-lw"], &["-cwl"], &["-w", "-c"], &["-l", "-wc"]];
    for args in flags {
        for input in inputs.iter().copied().chain([&bytes[..]]) {
            let (code, out) = run(Command::new(&binary).args(args), input, Stdio::piped());
            let (gnu_code, gnu_out) = run(&mut gnu_wc(args), input, Stdio::piped());
            assert_eq!(code, Some(0), "wc {args:?} exits 0");
            assert_eq!(code, gnu_code, "as GNU's does");
            assert_eq!(String::from_utf8_lossy(&out), String::from_utf8_lossy(&gnu_out),
                "wc {args:?} prints what GNU's prints ({} bytes in)", input.len());
        }
    }

    // A flag it does not know exits 1, as GNU's does.
    for args in [&["-x"][..], &["-lx"]] {
        let (code, _) = run(Command::new(&binary).args(args), b"", Stdio::piped());
        let (gnu_code, _) = run(&mut gnu_wc(args), b"", Stdio::piped());
        assert_eq!(code, Some(1), "wc {args:?} exits 1");
        assert_eq!(code, gnu_code, "as GNU's does");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn compiled_head_takes_its_count_as_gnu_head() {
    let dir = scratch("head_n");
    let binary = dir.join("head");
    write_tool("head_n_tool", &binary);

    // Lines past a buffer and random bytes, under counts of none (ten),
    // zero, one, more lines than the input has, the largest word, and a
    // count in each spelling.
    let mut random = Bytes::seeded("head -n");
    let lines = random.take(30000, |r| b"ab\n"[(r % 3) as usize]);
    let bytes = random.take(70000, |r| r as u8);
    let count = format!("{}", 1 + random.next() % 5000);
    let counts: Vec<Vec<&str>> = vec![
        vec![],
        vec!["-n", "0"],
        vec!["-n", "1"],
        vec!["-n3"],
        vec!["-n", "007"],
        vec!["-n", &count],
        vec!["-n", "99999999"],
        vec!["-n", "18446744073709551615"],
    ];
    for args in &counts {
        for input in [&b""[..], b"no newline", b"one\ntwo\nthree\n", &lines, &bytes] {
            let ours = run_both(Command::new(&binary).args(args), input, Stdio::piped());
            let gnu = run_both(Command::new("head").env("LC_ALL", "C").args(args), input, Stdio::piped());
            assert_eq!(ours.0, Some(0), "head {args:?} exits 0");
            assert_eq!(ours.0, gnu.0, "as GNU's does");
            assert!(ours.1 == gnu.1, "head {args:?} sends what GNU's sends ({} bytes in)", input.len());
        }
    }

    // Counts that are not numbers, and one past the largest word: both say
    // GNU's error and exit 1.
    for n in ["", "x", "1x", "99999999999999999999x", "18446744073709551616", "99999999999999999999999"] {
        let ours = run_both(Command::new(&binary).args(["-n", n]), b"a\n", Stdio::piped());
        let gnu = run_both(Command::new("head").env("LC_ALL", "C").args(["-n", n]), b"a\n", Stdio::piped());
        assert_eq!(ours.0, Some(1), "head -n {n:?} exits 1");
        assert_eq!((ours.0, String::from_utf8_lossy(&ours.2)), (gnu.0, String::from_utf8_lossy(&gnu.2)), "head -n {n:?} says what GNU's says");
        assert!(ours.1.is_empty(), "and sends nothing");
    }

    // A missing count exits 1.
    let (code, _, _) = run_both(Command::new(&binary).arg("-n"), b"a\n", Stdio::piped());
    assert_eq!(code, Some(1), "head -n with no count exits 1");

    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(Command::new(&binary).args(["-n", "1"]), b"no room\n", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn compiled_decimals_round_trip_the_widest_words() {
    let dir = scratch("decimal_echo");
    let binary = dir.join("decimal_echo");
    write_program("lib/_tests/native/native_decimal_tests.hthr", "decimal_echo_tool", &binary, false);

    // Zero, every power of ten and the number below it, the signed edges,
    // the largest word, and random words.
    let mut random = Bytes::seeded("decimal echo");
    let mut values: Vec<u64> = vec![0, 1, 9, (1 << 63) - 1, 1 << 63, (1 << 63) + 1, u64::MAX - 1, u64::MAX];
    values.extend((1..20).flat_map(|k| [10u64.pow(k) - 1, 10u64.pow(k)]));
    values.extend((0..16).map(|_| random.next() >> (random.next() % 64)));
    for v in values {
        let (code, out, _) = run_both(Command::new(&binary).arg(v.to_string()), b"", Stdio::piped());
        assert_eq!(code, Some(0), "{v} reads back");
        assert_eq!(String::from_utf8_lossy(&out), format!("{v}\n{}\n", v as i64), "{v} prints as itself and as a signed word");
    }

    // Leading zeros read; past the largest word, not all digits, or empty,
    // it exits 1.
    let (code, out, _) = run_both(Command::new(&binary).arg("000042"), b"", Stdio::piped());
    assert_eq!((code, String::from_utf8_lossy(&out).into_owned()), (Some(0), "42\n42\n".to_string()), "leading zeros read");
    for text in ["18446744073709551616", "18446744073709551620", "99999999999999999999", "184467440737095516150", "12a", "-1", ""] {
        let (code, out, _) = run_both(Command::new(&binary).arg(text), b"", Stdio::piped());
        assert_eq!(code, Some(1), "{text:?} is refused");
        assert!(out.is_empty(), "with nothing printed");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

/// `heather reflect` writes the checked-in program of `raise_letter` again,
/// byte for byte (lib/native/native_tool_words_program.hthr): the library
/// gate checks that module's agreement against the function, and this that
/// it is what the command writes now (issues/native-build-reflected-helpers.md).
#[test]
fn reflected_word_program_is_current() {
    let root = showcase::repo_root();
    let dir = scratch("reflect");
    let output = dir.join("native_tool_words_program.hthr");
    let result = Command::new(env!("CARGO_BIN_EXE_heather"))
        .current_dir(&root)
        .args(["reflect", "lib/native/native_tool_words.hthr", "raise_letter", "-o"]).arg(&output)
        .arg("--cache-dir").arg(showcase::cli_check_images())
        .output().unwrap();
    assert!(result.status.success(), "{}{}", String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    assert!(!output.with_extension("unchecked.hthr").exists(), "no unchecked module is left");
    let written = std::fs::read_to_string(&output).unwrap();
    let checked_in = std::fs::read_to_string(root.join("lib/native/native_tool_words_program.hthr")).unwrap();
    assert!(written == checked_in, "lib/native/native_tool_words_program.hthr is stale: regenerate it with `heather reflect lib/native/native_tool_words.hthr raise_letter -o …`");
    std::fs::remove_dir_all(dir).unwrap();
}

/// `grep -F PATTERN` against GNU's under `LC_ALL=C`: the lines written and
/// the exit status, over lines of a two-letter alphabet, random bytes (no
/// NUL, which GNU reads as a binary file, and a newline at least every 200
/// bytes, inside the tool's line buffer), an unterminated last line, and
/// patterns empty, short, long and past ASCII. Its line test is a procedure
/// called from two sites (docs/native-procedures-design.md).
#[test]
fn compiled_grep_f_runs_as_gnu_grep() {
    let dir = scratch("grep");
    let binary = dir.join("grep");
    write_tool("grep_f_tool", &binary);

    let mut random = Bytes::seeded("grep");
    let letters = random.take(30000, |r| b"ab\n"[(r % 3) as usize]);
    let mut bytes = Vec::with_capacity(70000);
    for k in 0..70000 {
        bytes.push(if k % 200 == 199 { b'\n' } else { random.next() as u8 % 255 + 1 });
    }
    // A newline in a pattern is GNU's pattern separator, which the tool
    // does not implement: a random byte of 10 (one seed in 85 or so) made
    // `picked` a two-pattern list GNU matched and the tool did not.
    let picked: Vec<u8> = bytes[1000..1003].iter().map(|&b| if b == b'\n' { b'a' } else { b }).collect();
    let patterns: Vec<Vec<u8>> = vec![b"ab".to_vec(), b"aba".to_vec(), b"".to_vec(), b"b".to_vec(), b"abababab".to_vec(), picked, vec![0xe9, b'a']];
    for input in [&b""[..], b"ab\nba\naab\n", b"no newline ab", b"\n\n\n", &letters, &bytes] {
        for pattern in &patterns {
            let (code, out) = run(&mut with_args(&binary, std::slice::from_ref(pattern)), input, Stdio::piped());
            let mut gnu = with_args("grep", &[b"-F".to_vec(), b"--".to_vec(), pattern.clone()]);
            let (gnu_code, gnu_out) = run(gnu.env("LC_ALL", "C"), input, Stdio::piped());
            assert_eq!(code, gnu_code, "grep -F's status is GNU's (pattern {pattern:?}, {} bytes in)", input.len());
            assert!(out == gnu_out, "grep -F writes GNU's lines (pattern {pattern:?}, {} bytes in)", input.len());
        }
    }
    let (code, _) = run(&mut Command::new(&binary), b"ab\n", Stdio::piped());
    assert_eq!(code, Some(2), "with no pattern it exits 2, as GNU's does");

    std::fs::remove_dir_all(dir).unwrap();
}

/// A process on `input`, its exit code and what it wrote to stderr; stdout
/// is dropped.
fn run_stderr(program: &mut Command, input: &[u8]) -> (Option<i32>, Vec<u8>) {
    let mut child = program.stdin(Stdio::piped()).stdout(Stdio::null()).stderr(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let out = child.wait_with_output().unwrap();
    writer.join().unwrap();
    (out.status.code(), out.stderr)
}

/// Lines of random lengths up to `longest` over `alphabet` (random bytes
/// but the newline when it is empty), `count` of them, the last without its
/// newline when `open_end`.
fn random_lines(random: &mut Bytes, count: usize, longest: u64, alphabet: &[u8], open_end: bool) -> Vec<u8> {
    let mut out = Vec::new();
    for k in 0..count {
        let len = random.next() % (longest + 1);
        for _ in 0..len {
            let r = random.next();
            out.push(if alphabet.is_empty() { (r % 255) as u8 + (((r % 255) as u8 >= b'\n') as u8) } else { alphabet[(r % alphabet.len() as u64) as usize] });
        }
        if !(open_end && k + 1 == count) {
            out.push(b'\n');
        }
    }
    out
}

/// `tac` against GNU's: its lines last first, over nothing, blank lines, a
/// last line with no newline (which GNU writes first, as it is), lines
/// longer than the tool's read buffer (so a line is read in parts into its
/// arena cell), and random bytes. Its lines are a list in an arena
/// (docs/native-heap-arena-design.md); running out of it is a defined exit,
/// GNU's message and status 1, which GNU's does not meet at these sizes.
#[test]
fn compiled_tac_runs_as_gnu_tac() {
    let dir = scratch("tac");
    let binary = dir.join("tac");
    write_program("lib/native/native_heap_tools.hthr", "tac_tool", &binary, false);

    let mut random = Bytes::seeded("tac");
    let letters = random_lines(&mut random, 3000, 12, b"ab", false);
    let long = random_lines(&mut random, 40, 9000, b"xyz \t", true);
    let bytes = random_lines(&mut random, 500, 300, b"", true);
    for input in [&b""[..], b"\n", b"a", b"a\n", b"a\nb\nc\n", b"a\nb", b"\n\n\n", b"x\n\ny", &letters, &long, &bytes] {
        let (code, out) = run(&mut Command::new(&binary), input, Stdio::piped());
        let (gnu_code, gnu_out) = run(Command::new("tac").env("LC_ALL", "C"), input, Stdio::piped());
        assert_eq!(code, Some(0), "tac exits 0 ({} bytes in)", input.len());
        assert_eq!(code, gnu_code, "as GNU's does");
        assert!(out == gnu_out, "tac writes GNU's lines ({} bytes in)", input.len());
    }

    let huge = vec![b'a'; 1100000];
    let (code, err) = run_stderr(&mut Command::new(&binary), &huge);
    assert_eq!(code, Some(1), "running out of arena exits 1");
    assert_eq!(err, b"tac: memory exhausted\n", "with GNU's message");

    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&mut Command::new(&binary), b"no\nroom\n", Stdio::from(full.try_clone().unwrap()));
        let (gnu_code, _) = run(&mut Command::new("tac"), b"no\nroom\n", Stdio::from(full));
        assert_eq!(code, Some(1), "a failed write exits 1");
        assert_eq!(code, gnu_code, "as GNU's does");
    }

    std::fs::remove_dir_all(dir).unwrap();
}

/// `sort` against GNU's under `LC_ALL=C`: lines ordered by their bytes
/// unsigned, a prefix first, alike lines kept, a last line without a
/// newline given one, over nothing, blank lines, prefixes, duplicates, bytes
/// past ASCII and lines longer than the read buffer. Its lines are a list in
/// an arena it never changes (docs/native-heap-arena-design.md §3);
/// running out of it exits 2 with GNU's message.
#[test]
fn compiled_sort_runs_as_gnu_sort() {
    let dir = scratch("sort");
    let binary = dir.join("sort");
    write_program("lib/native/native_heap_tools.hthr", "sort_tool", &binary, false);

    let mut random = Bytes::seeded("sort");
    let letters = random_lines(&mut random, 1500, 6, b"abc", false);
    let long = random_lines(&mut random, 30, 9000, b"ab", true);
    let bytes = random_lines(&mut random, 400, 40, b"", true);
    let fixed: &[&[u8]] = &[b"", b"\n", b"a", b"b\na\n", b"abc\nab\na\nabd\n", b"b\nb\na\nb", b"\n\nz\n\n", b"\xff\n\x01\na\n\x80", b"same\nsame\nsame\n"];
    for input in fixed.iter().copied().chain([&letters[..], &long, &bytes]) {
        let (code, out) = run(&mut Command::new(&binary), input, Stdio::piped());
        let (gnu_code, gnu_out) = run(Command::new("sort").env("LC_ALL", "C"), input, Stdio::piped());
        assert_eq!(code, Some(0), "sort exits 0 ({} bytes in)", input.len());
        assert_eq!(code, gnu_code, "as GNU's does");
        assert!(out == gnu_out, "sort writes GNU's lines ({} bytes in)", input.len());
    }

    let huge = vec![b'a'; 1100000];
    let (code, err) = run_stderr(&mut Command::new(&binary), &huge);
    assert_eq!(code, Some(2), "running out of arena exits 2");
    assert_eq!(err, b"sort: memory exhausted\n", "with GNU's message");

    if let Ok(full) = std::fs::OpenOptions::new().write(true).open("/dev/full") {
        let (code, _) = run(&mut Command::new(&binary), b"no\nroom\n", Stdio::from(full.try_clone().unwrap()));
        let (gnu_code, _) = run(Command::new("sort").env("LC_ALL", "C"), b"no\nroom\n", Stdio::from(full));
        assert_eq!(code, Some(2), "a failed write exits 2");
        assert_eq!(code, gnu_code, "as GNU's does");
    }

    std::fs::remove_dir_all(dir).unwrap();
}
