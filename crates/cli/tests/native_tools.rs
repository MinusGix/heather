//! `tr a-z A-Z`, `yes`, `head -c 10` and `wc -l`, written with the builder
//! (`native_build`), compiled by the effectful source compiler and written as
//! ELFs by `heather write-elf`, run as Linux processes beside GNU's
//! (issues/native-source-bytes.md, issues/native-source-builder.md). None has
//! a theorem of its own: `lib/native/native_tools.hthr` holds only the
//! tools, and `native_compile_correct` is the proof of each.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use heather_cli::showcase;

/// One `write-elf` of `symbol` through the image store native_cat.rs uses
/// (its closure is a part of cat's), in the stale lanes replaying images an
/// earlier build wrote.
fn write_tool(symbol: &str, output: &Path) {
    let root = showcase::repo_root();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
    cmd.current_dir(&root)
        .args(["write-elf", "lib/native/native_tools.hthr", symbol, "-o"])
        .arg(output)
        .arg("--cache-dir").arg(showcase::CLI_CHECK_IMAGES);
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
    write_tool("tr_upper_source", &binary);
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
    write_tool("yes_source", &binary);

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
    write_tool("head_c10_source", &binary);

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
    write_tool("wc_l_source", &binary);

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
