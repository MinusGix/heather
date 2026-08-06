//! Compile in a fingerprint of the kernel's source.
//!
//! `docs/cache-v1-design.md` §6: a cache entry is meaningful only against the
//! kernel that produced it, so every entry must be invalidated when that
//! kernel changes. The alternative — a hand-maintained epoch constant someone
//! remembers to bump — fails silently in exactly the direction that matters,
//! so v1 derives the fingerprint from the build instead.
//!
//! It is conservative: this hashes the *text* of `crates/kernel/src`, so a
//! comment change discards the cache. That is the cheap direction to be wrong
//! in. The fingerprint this should become — over the kernel's semantics rather
//! than its bytes — is recorded on `KERNEL_SEMANTICS` in `src/lib.rs`.
//!
//! A missing or unreadable kernel source tree **panics** the build rather than
//! falling back to a constant: a fallback would let two differently-built
//! binaries agree on a fingerprint, which is the one thing this must not do.

use std::path::{Path, PathBuf};

/// The crate's own SHA-256, pulled in by path: the build script needs the
/// same hash the crate uses, and cannot depend on the crate it is building.
#[path = "src/sha256.rs"]
#[allow(dead_code)]
mod sha256;

use sha256::{Sha256, hex};

fn main() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR");
    let src = Path::new(&manifest).join("..").join("kernel").join("src");
    let src = src.canonicalize().unwrap_or_else(|e| {
        panic!("heather-cache: cannot read the kernel source at {}: {e}", src.display())
    });

    let mut files = Vec::new();
    collect(&src, &mut files);
    files.sort();
    assert!(!files.is_empty(), "heather-cache: no kernel sources under {}", src.display());

    let mut h = Sha256::new();
    for f in &files {
        // The path is hashed too, so that moving code between files — which
        // can change nothing textually in aggregate — still moves the
        // fingerprint.
        let rel = f.strip_prefix(&src).unwrap_or(f);
        h.update(rel.to_string_lossy().as_bytes());
        h.update(b"\0");
        h.update(&std::fs::read(f).unwrap_or_else(|e| panic!("cannot read {}: {e}", f.display())));
        h.update(b"\0");
    }
    println!("cargo:rustc-env=HEATHER_KERNEL_SEMANTICS={}", hex(&h.finish()));
    println!("cargo:rerun-if-changed={}", src.display());
    println!("cargo:rerun-if-changed=build.rs");
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("heather-cache: cannot list {}: {e}", dir.display()));
    for e in entries {
        let p = e.expect("dir entry").path();
        if p.is_dir() {
            collect(&p, out);
        } else if p.extension().is_some_and(|x| x == "rs") {
            out.push(p);
        }
    }
}
