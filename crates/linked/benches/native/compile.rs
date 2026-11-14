//! What compiling the linked SHA-256 costs: `heather compile-x86` for each
//! SHA-256 row of `crates/linked/generated/EXPORTS.tsv`, as `scripts/linked`
//! runs it (the release binary, the generator, the certificate checked),
//! timed by the wall clock.
//!
//! *Cold* is a row compiled against an empty native-image store of its own,
//! so it pays for elaborating and imaging every library module it imports;
//! *warm* is the same row again over that store, which is what a round that
//! changed nothing the module imports pays (generation and the certificate
//! check). Each row is compiled alone, one after another, so a time is not
//! shared with another compile's threads.

use std::path::Path;
use std::process::Command;
use std::time::Instant;

pub struct Compiled {
    pub symbol: String,
    pub cold: Option<f64>,
    pub warm: Option<f64>,
}

/// The SHA-256 rows as the compiler reads the table: module, function,
/// symbol, entries.
fn rows(heather: &Path, root: &Path) -> Vec<[String; 4]> {
    let Ok(output) = Command::new(heather).arg("linked-exports").arg(root.join("crates/linked/generated")).arg("--rows").output() else {
        return Vec::new();
    };
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let mut f = line.split('\t');
            let row = [f.next()?, f.next()?, f.next()?, f.next().unwrap_or("")].map(String::from);
            row[2].starts_with("sha256_").then_some(row)
        })
        .collect()
}

/// One compile into a directory of its own, which compile-x86 writes the
/// assembly and the certificate into (it refuses to overwrite either).
fn compile(heather: &Path, root: &Path, row: &[String; 4], store: &Path, dir: &Path) -> Option<f64> {
    let _ = std::fs::remove_dir_all(dir);
    std::fs::create_dir_all(dir).ok()?;
    let out = dir.join(format!("{}.s", row[2]));
    let mut command = Command::new(heather);
    command.current_dir(root).arg("compile-x86").arg(&row[0]).arg(&row[1]).arg("--symbol").arg(&row[2]);
    for entry in row[3].split_whitespace() {
        command.arg("--entry").arg(entry);
    }
    command.arg("-o").arg(out).arg("--cache-dir").arg(store);
    let started = Instant::now();
    let output = command.output().ok()?;
    let seconds = started.elapsed().as_secs_f64();
    if !output.status.success() {
        eprintln!("compile-x86 {} {} failed:\n{}", row[0], row[1], String::from_utf8_lossy(&output.stderr));
        return None;
    }
    Some(seconds)
}

/// Every SHA-256 row cold and warm; with `only`, that symbol's row alone.
pub fn run(heather: &Path, root: &Path, work: &Path, only: Option<&str>) -> Vec<Compiled> {
    let mut compiled = Vec::new();
    for row in rows(heather, root) {
        if only.is_some_and(|symbol| symbol != row[2]) {
            continue;
        }
        let store = work.join(format!("store.{}", row[2]));
        let _ = std::fs::remove_dir_all(&store);
        let out = work.join(format!("out.{}", row[2]));
        eprintln!("bench-native: compiling {} cold, then warm", row[2]);
        let cold = compile(heather, root, &row, &store, &out);
        let warm = cold.and_then(|_| compile(heather, root, &row, &store, &out));
        let _ = std::fs::remove_dir_all(&store);
        let _ = std::fs::remove_dir_all(&out);
        compiled.push(Compiled { symbol: row[2].clone(), cold, warm });
    }
    compiled
}
