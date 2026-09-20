//! Shared driver for the callee-profile executable gates (`native_calls`,
//! `native_stack_local`, `native_summary`). Each test still spawns its own
//! `build-x86` child in its own binary: the child elaborates one monolithic
//! `caller_native_certificate` module per example (the leaf summary inside it
//! is emitted per placement profile and never published to the image store),
//! so the certificate cost cannot be shared across examples; only the
//! 28-module support prefix is, through `target/native-test-images`, which
//! `scripts/test`'s native warmup populates. The three stay separate binaries
//! so the runner can schedule them independently (`native_summary` is the
//! exclusive last target, issues/native-summary-test-cpu-margin.md).
#![allow(dead_code)] // each binary uses a different subset
use std::path::{Path, PathBuf};
use std::process::Command;

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
