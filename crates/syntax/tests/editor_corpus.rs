use std::fs;
use std::path::{Path, PathBuf};

use heather_syntax::parse_file;

fn fixture_dir(kind: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tree-sitter-heather/test/fixtures")
        .join(kind)
}

fn fixtures(kind: &str) -> Vec<PathBuf> {
    let mut paths: Vec<_> = fs::read_dir(fixture_dir(kind))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "hthr"))
        .collect();
    paths.sort();
    paths
}

#[test]
fn differential_positive_fixtures_parse_with_heather() {
    for path in fixtures("positive") {
        let source = fs::read_to_string(&path).unwrap();
        parse_file(&source).unwrap_or_else(|error| {
            panic!("{}: {} at {:?}", path.display(), error.msg, error.span)
        });
    }
}

#[test]
fn negative_and_recovery_fixtures_are_rejected_by_heather() {
    for kind in ["negative", "recovery"] {
        for path in fixtures(kind) {
            let source = fs::read_to_string(&path).unwrap();
            assert!(parse_file(&source).is_err(), "{} unexpectedly parsed", path.display());
        }
    }
}
