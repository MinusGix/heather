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
    let crates = Path::new(&manifest).join("..");
    let kernel = source_root(&crates, "kernel");
    println!(
        "cargo:rustc-env=HEATHER_KERNEL_SEMANTICS={}",
        hex(&fingerprint(&[("kernel", &kernel)], &[]))
    );

    // Persistent module images depend on frontend decisions as well as the
    // kernel judgment. Include every source tree which parses or elaborates
    // their payload; the binary format itself has an explicit version.
    let syntax = source_root(&crates, "syntax");
    let elab = source_root(&crates, "elab");
    let prelude = elab.join("prelude.hthr").canonicalize()
        .unwrap_or_else(|e| panic!("heather-cache: cannot read the prelude: {e}"));
    println!(
        "cargo:rustc-env=HEATHER_ELABORATOR_SEMANTICS={}",
        hex(&fingerprint(
            &[("kernel", &kernel), ("syntax", &syntax), ("elab", &elab)],
            &[("prelude", &prelude)],
        ))
    );
    for src in [&kernel, &syntax, &elab] {
        println!("cargo:rerun-if-changed={}", src.display());
    }
    println!("cargo:rerun-if-changed={}", prelude.display());
    println!("cargo:rerun-if-changed=build.rs");
}

fn source_root(crates: &Path, name: &str) -> PathBuf {
    let src = crates.join(name).join("src");
    src.canonicalize().unwrap_or_else(|e| {
        panic!("heather-cache: cannot read the {name} source at {}: {e}", src.display())
    })
}

fn fingerprint(roots: &[(&str, &PathBuf)], extra: &[(&str, &PathBuf)]) -> [u8; 32] {
    let mut h = Sha256::new();
    for (label, src) in roots {
        let mut files = Vec::new();
        collect(src, &mut files);
        files.sort();
        assert!(!files.is_empty(), "heather-cache: no sources under {}", src.display());
        for f in &files {
            h.update(label.as_bytes());
            h.update(b"/");
            let rel = f.strip_prefix(src).unwrap_or(f);
            h.update(rel.to_string_lossy().as_bytes());
            h.update(b"\0");
            h.update(&std::fs::read(f).unwrap_or_else(|e| panic!("cannot read {}: {e}", f.display())));
            h.update(b"\0");
        }
    }
    for (label, file) in extra {
        h.update(label.as_bytes());
        h.update(b"\0");
        h.update(&std::fs::read(file).unwrap_or_else(|e| panic!("cannot read {}: {e}", file.display())));
        h.update(b"\0");
    }
    h.finish()
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
