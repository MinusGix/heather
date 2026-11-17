//! The README's code is checked code.
//!
//! Every ` ```rust ` block in `README.md` (Heather is fenced as Rust for the
//! syntax highlighting) sits under a comment `<!-- checked: <path> -->`
//! naming the file it is taken from, and each of its declarations (a run of
//! lines between blank lines) is in that file, as written but for where its
//! lines break. A `…` in a declaration stands for text the README leaves out
//! (a proof body), so a statement can be shown without its proof. The
//! README's own examples are files in `examples/readme/`, which are checked
//! here like a showcase row; the library's are checked by the whole-library
//! gate.
//!
//! The README is read by `include_str!`, so `scripts/test --pr` selects this
//! binary when the README changes (its dep-info names the file).

use std::path::PathBuf;
use std::process::Command;

use heather_cli::showcase;

const README: &str = include_str!("../../../README.md");

fn root() -> PathBuf {
    showcase::repo_root()
}

/// Whitespace runs as one space, and none just inside brackets or before a
/// comma: a line broken after `(` or before `)` reads as the one-line text.
fn normalize(text: &str) -> String {
    let words: Vec<&str> = text.split_whitespace().collect();
    let joined = words.join(" ");
    let mut out = String::with_capacity(joined.len());
    let chars: Vec<char> = joined.chars().collect();
    for (i, &c) in chars.iter().enumerate() {
        if c == ' ' {
            let before = if i > 0 { chars[i - 1] } else { ' ' };
            let after = chars.get(i + 1).copied().unwrap_or(' ');
            if matches!(before, '(' | '[') || matches!(after, ')' | ']' | ',') {
                continue;
            }
        }
        out.push(c);
    }
    out
}

struct Block {
    /// The README line the block's fence opens on, from 1.
    line: usize,
    source: String,
    text: String,
}

fn blocks() -> Vec<Block> {
    let lines: Vec<&str> = README.lines().collect();
    let mut out = vec![];
    let mut i = 0;
    while i < lines.len() {
        if lines[i].trim() != "```rust" {
            i += 1;
            continue;
        }
        let source = i.checked_sub(1)
            .and_then(|j| lines[j].trim().strip_prefix("<!-- checked:"))
            .and_then(|rest| rest.strip_suffix("-->"))
            .map(|path| path.trim().to_string())
            .unwrap_or_else(|| panic!("README.md:{}: a `rust` block needs `<!-- checked: <path> -->` on the line above it", i + 1));
        let start = i + 1;
        let mut end = start;
        while end < lines.len() && lines[end].trim() != "```" {
            end += 1;
        }
        assert!(end < lines.len(), "README.md:{}: the block is never closed", i + 1);
        out.push(Block { line: i + 1, source, text: lines[start..end].join("\n") });
        i = end + 1;
    }
    out
}

/// Does `haystack` hold the pieces, in order?
fn holds_in_order(haystack: &str, pieces: &[String]) -> bool {
    let mut at = 0;
    for piece in pieces {
        match haystack[at..].find(piece.as_str()) {
            Some(found) => at += found + piece.len(),
            None => return false,
        }
    }
    true
}

#[test]
fn every_readme_declaration_is_in_its_file() {
    let blocks = blocks();
    assert!(!blocks.is_empty(), "README.md has no `rust` blocks; this test reads the wrong file");
    let mut missing = vec![];
    for block in &blocks {
        let path = root().join(&block.source);
        let file = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("README.md:{}: cannot read {}: {e}", block.line, block.source));
        let file = normalize(&file);
        for declaration in block.text.split("\n\n").filter(|d| !d.trim().is_empty()) {
            let pieces: Vec<String> = declaration.split('…').map(normalize).filter(|p| !p.is_empty()).collect();
            if !holds_in_order(&file, &pieces) {
                missing.push(format!("README.md:{} ({}):\n{declaration}", block.line, block.source));
            }
        }
    }
    assert!(missing.is_empty(), "README declarations not found as written in the file they cite:\n\n{}", missing.join("\n\n"));
}

/// The README's own example files elaborate and pass the kernel.
#[test]
fn readme_examples_check() {
    let dir = root().join("examples/readme");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read examples/readme")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("hthr"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "examples/readme has no .hthr files");
    for file in files {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_heather"));
        cmd.current_dir(root()).arg("check");
        // As the showcase gate runs a row: width one, through the shared CLI
        // image store, replaying the library's images.
        cmd.env("HEATHER_KERNEL_WORKERS", "1");
        cmd.arg("--cache").arg("--cache-dir").arg(showcase::cli_check_images());
        if std::env::var("HEATHER_SEMANTIC_IMAGES").as_deref() == Ok("accept-stale") {
            cmd.arg("--accept-stale-images");
        }
        let relative = file.strip_prefix(root()).expect("under the repo").to_path_buf();
        cmd.arg(&relative);
        let out = cmd.output().expect("run heather check");
        let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
        text.push_str(&String::from_utf8_lossy(&out.stderr));
        assert!(out.status.success(), "{} did not check:\n{text}", relative.display());
        assert!(text.contains(&format!("{}: ok", relative.display())), "{} checked without the ok line:\n{text}", relative.display());
    }
}

#[test]
fn normalize_reads_broken_lines_as_one() {
    assert_eq!(normalize("f(\n    a,\n    b\n)"), "f(a, b)");
    assert_eq!(normalize("record R {\n    x: u64,\n    y: [u32; 8]\n}"), "record R { x: u64, y: [u32; 8] }");
    assert!(holds_in_order("theorem t(): A { proof }", &["theorem t(): A {".into(), "}".into()]));
}
