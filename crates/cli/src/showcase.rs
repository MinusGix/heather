//! The showcase manifest, `docs/showcase/showcases.tsv`, as data.
//!
//! The manifest's header is the specification; this is its reader. It exists
//! so the tests that gate the showcase and the tests that *replay* it do not
//! each carry their own copy of "which file, over which `-L` dirs, at which
//! tier" — four such copies is what
//! `issues/showcase-harness.md` was filed about.
//!
//! Read at run time rather than `include_str!`-ed, because the consumers want
//! the rows (to iterate, to cross-check an array against) and not a string;
//! every consumer runs inside the repo, where the file is.

use std::path::{Path, PathBuf};

/// How a showcase is gated. The manifest's header documents each tier for a
/// human; this is the same list for a program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tier {
    /// The in-process prefix of `crates/elab/tests/showcase_calculator.rs`.
    Suite,
    /// Included by some other in-process test target.
    Test,
    /// In-process only: the CLI cannot check this file at all — a stem that
    /// is not an identifier, or a deliberate hole only its generator fills.
    /// See the manifest's note per row, and `issues/showcase-hyphen-stems.md`.
    TestOnly,
    /// The release-CLI gate, `crates/cli/tests/showcase.rs`.
    Cli,
    /// Nothing checks it, by design; the note says why.
    Unchecked,
}

impl Tier {
    fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "suite" => Self::Suite,
            "test" => Self::Test,
            "test-only" => Self::TestOnly,
            "cli" => Self::Cli,
            "unchecked" => Self::Unchecked,
            _ => return None,
        })
    }
}

#[derive(Clone, Debug)]
pub struct Showcase {
    /// The module name, which is the file stem.
    pub name: String,
    /// Repo-relative path to the file.
    pub path: PathBuf,
    /// The `-L` dirs, repo-relative. The file's own directory is searched
    /// first by the loader and is deliberately never listed.
    pub search: Vec<PathBuf>,
    pub tier: Tier,
    pub note: String,
}

/// The repo root, from this crate's manifest directory.
pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().expect("repo root")
}

pub fn manifest_path() -> PathBuf {
    repo_root().join("docs/showcase/showcases.tsv")
}

/// Every row of the manifest, in file order.
///
/// Panics with the offending line rather than returning an error: every
/// caller is a test, and a malformed manifest is a repo defect with exactly
/// one useful response.
pub fn manifest() -> Vec<Showcase> {
    let path = manifest_path();
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read the showcase manifest at {}: {e}", path.display()));
    let mut rows = Vec::new();
    for (n, line) in text.lines().enumerate() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').map(str::trim).collect();
        let [name, search, tier, note] = fields.as_slice() else {
            panic!(
                "{}:{}: expected 4 tab-separated columns, got {}",
                path.display(),
                n + 1,
                fields.len()
            );
        };
        let tier = Tier::parse(tier)
            .unwrap_or_else(|| panic!("{}:{}: unknown tier `{tier}`", path.display(), n + 1));
        rows.push(Showcase {
            name: (*name).to_string(),
            path: PathBuf::from(format!("docs/showcase/{name}.hthr")),
            search: if *search == "-" {
                Vec::new()
            } else {
                search.split(',').map(|d| PathBuf::from(d.trim())).collect()
            },
            tier,
            note: (*note).to_string(),
        });
    }
    rows
}

/// The rows at one tier.
pub fn at_tier(tier: Tier) -> Vec<Showcase> {
    manifest().into_iter().filter(|s| s.tier == tier).collect()
}
