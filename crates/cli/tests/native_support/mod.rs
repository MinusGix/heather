//! Shared drivers for the native executable gates. `Built` is the callee
//! profile's (`native_calls`,
//! `native_stack_local`, `native_summary`). Each test still spawns its own
//! `build-x86` child in its own binary: the child elaborates one monolithic
//! `caller_native_certificate` module per example (the leaf summary inside it
//! is emitted per placement profile and never published to the image store),
//! so the certificate cost cannot be shared across examples; only the
//! 28-module support prefix is, through `target/native-test-images`, which
//! `scripts/test`'s native warmup populates. The three stay separate binaries
//! so the runner can schedule them independently (`native_summary` is the
//! exclusive last target, issues/native-summary-test-cpu-margin.md).
//! The rest is the stdin programs' (`native_read_loop`, `native_wc`,
//! `native_tr`, `native_filter`): a scratch directory, a build by the program's name, a
//! program's source with an author's mistake in it, and the ways its stdin
//! and stdout are fed and fail.
#![allow(dead_code)] // each binary uses a different subset
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

pub fn root() -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).join("../..") }

/// A fresh `target/native-<name>-<pid>-<nonce>`.
pub fn scratch(name: &str) -> PathBuf {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = root().join(format!("target/native-{name}-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    directory
}

/// `build-x86 <source> <name> <extra> -o <directory>/<output>`, with no
/// toolchain on PATH.
pub fn build_x86(directory: &Path, source: &Path, name: &str, extra: &[&str], output: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(root()).env("PATH", directory)
        .arg("build-x86").arg(source).arg(name).args(extra).arg("-o").arg(directory.join(output))
        .args(["--cache-dir", "target/native-test-images"]).output().unwrap()
}

pub fn example(name: &str) -> PathBuf { PathBuf::from(format!("examples/x86-native/{name}.hthr")) }

/// The example with an author's mistake in it: each `(from, to)` replaced
/// once, written under the example's own name in `directory`.
pub fn mistaken(directory: &Path, name: &str, edits: &[(&str, &str)]) -> PathBuf {
    let mut text = std::fs::read_to_string(root().join(example(name))).unwrap();
    for (from, to) in edits {
        assert!(text.contains(from), "{name} has no `{from}`");
        text = text.replacen(from, to, 1);
    }
    let path = directory.join(format!("{name}.hthr"));
    std::fs::write(&path, text).unwrap();
    path
}

/// A build refused where the author is wrong: at their own source, not by a
/// missing name, with nothing published.
pub fn assert_refused_at(output: &Output, source: &Path, published: &[PathBuf]) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "certified: {stderr}");
    assert!(!stderr.contains("unbound") && !stderr.contains("ambiguous"), "{stderr}");
    let at = format!("{}:", source.file_name().unwrap().to_string_lossy());
    assert!(stderr.contains("--> ") && stderr.contains(&at), "refused elsewhere than {at}: {stderr}");
    for path in published { assert!(!path.exists(), "{} was published", path.display()); }
}

/// The input written to a pipe from another thread.
pub fn piped(executable: &Path, input: &[u8]) -> Output {
    let mut child = Command::new(executable).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    let writer = std::thread::spawn(move || { let _ = stdin.write_all(&input); });
    let output = child.wait_with_output().unwrap();
    writer.join().unwrap();
    output
}

/// A pipe written in bursts, so the reads return pieces: the program must
/// keep reading until the writer closes it.
pub fn bursts(executable: &Path, pieces: &[&[u8]]) -> Output {
    let mut child = Command::new(executable).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let mut stdin = child.stdin.take().unwrap();
    for piece in pieces {
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
pub fn unreadable_stdin(executable: &Path) -> Output {
    Command::new(executable).stdin(std::fs::File::open("/").unwrap()).output().unwrap()
}
pub fn unwritable_stdout(executable: &Path, stdout: Stdio, input: &[u8]) -> Output {
    let mut child = Command::new(executable).stdin(Stdio::piped()).stdout(stdout).spawn().unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}

pub struct Built {
    directory: PathBuf,
    pub executable: PathBuf,
}

impl Built {
    /// `build-x86 examples/x86-native/<example>.hthr caller --callee leaf`
    /// with the two inputs, into a unique `target/native-<name>-<pid>-<nonce>/caller`.
    pub fn callee_example(name: &str, example: &str, inputs: [&str; 2]) -> Built {
        Self::callee_example_with_options(name, example, inputs, &[])
    }

    pub fn callee_example_with_options(name: &str, example: &str, inputs: [&str; 2], options: &[&str]) -> Built {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let directory = root.join(format!("target/native-{name}-{}-{nonce}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let executable = directory.join("caller");
        let output = Command::new(env!("CARGO_BIN_EXE_heather")).current_dir(&root)
            .env("PATH", &directory)
            .args(["build-x86", &format!("examples/x86-native/{example}.hthr"), "caller", "--callee", "leaf",
                "--arg", inputs[0], "--arg", inputs[1], "-o"])
            .arg(&executable).args(options).args(["--cache-dir", "target/native-test-images"]).output().unwrap();
        assert!(output.status.success(), "build-x86 {}: {}", output.status, String::from_utf8_lossy(&output.stderr));
        Built { directory, executable }
    }

    /// Exit status of the produced executable.
    pub fn run(&self) -> Option<i32> {
        Command::new(&self.executable).status().unwrap().code()
    }

    /// The ELF image as written.
    pub fn bytes(&self) -> Vec<u8> {
        std::fs::read(&self.executable).unwrap()
    }

    /// The companion `caller.certificate.hthr`.
    pub fn certificate(&self) -> String {
        std::fs::read_to_string(self.directory.join("caller.certificate.hthr")).unwrap()
    }

    /// Remove the build directory; a failed assertion leaves it for inspection.
    pub fn finish(self) {
        std::fs::remove_dir_all(self.directory).unwrap();
    }
}
