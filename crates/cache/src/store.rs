//! The on-disk cache file (`docs/cache-v1-design.md` §8).
//!
//! One tab-separated text file per repository, inspectable with `cat` and
//! `grep`, because the first question anyone asks of a cache is "what does it
//! think it knows":
//!
//! ```text
//! heather-cache	1
//! kernel-semantics	<64 hex>
//! checksum	<64 hex>
//! ok	<64 hex check key>	<64 hex interface hash>	<name>
//! ```
//!
//! Two properties the format buys deliberately. **Extra fields are ignored by
//! the reader**, which is the room rung 2 needs: a replay trace lands as a
//! fifth column that an older reader skips, so attaching one is not a format
//! break. And **the verdict is a column**, not implied, so a recorded failure
//! is possible later without one either.
//!
//! What the checksum is and is not: integrity against accident — truncation, a
//! bit flip, a half-written file — checked on load. It is not a defence
//! against an adversary, who can recompute it. Rung 1's trusted base is "the
//! OS gave us a file nobody tampered with"; §6 of the design says so plainly
//! rather than implying more.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::merkle::Hash;
use crate::sha256::{hex, unhex};

/// The format version. Bumped when the *file* shape changes; the kernel
/// fingerprint below covers changes to what the entries mean.
pub const FORMAT: &str = "1";

/// The file within the cache directory.
pub const FILE: &str = "entries-v1.tsv";

/// One recorded verdict. Keyed by check key; the rest is metadata.
#[derive(Clone, PartialEq, Eq)]
pub struct Entry {
    pub iface: Hash,
    /// Human-facing only. Identity is the key (Unison's rule: names are
    /// metadata over hashes).
    pub name: String,
}

/// A loaded (or fresh) cache file.
pub struct Store {
    pub dir: PathBuf,
    /// Ordered by key hex, so the written file is a deterministic function of
    /// its contents — a cache that rewrote itself differently each run would
    /// be unreviewable and would defeat the checksum's purpose.
    pub entries: BTreeMap<String, Entry>,
    pub dirty: bool,
}

/// Why a cache file was not usable. Every variant ends the same way — the file
/// is discarded and the run is a full check — but the *reason* is printed,
/// because "the cache silently did nothing" is the failure this design is
/// least able to afford.
pub enum Rejected {
    /// No file. Not an error and not reported: a first run.
    Absent,
    /// Written by a different kernel. The loud, expected one.
    KernelChanged { entries: usize },
    Malformed(String),
}

impl Rejected {
    pub fn message(&self) -> Option<String> {
        match self {
            Rejected::Absent => None,
            Rejected::KernelChanged { entries } => Some(format!(
                "cache: kernel semantics changed since these {entries} entries were \
                 written — discarding, this run is a full check"
            )),
            Rejected::Malformed(why) => Some(format!(
                "cache: {why} — discarding, this run is a full check"
            )),
        }
    }
}

impl Store {
    pub fn empty(dir: PathBuf) -> Store {
        Store { dir, entries: BTreeMap::new(), dirty: false }
    }

    pub fn path(dir: &Path) -> PathBuf {
        dir.join(FILE)
    }

    /// Load `dir`'s cache, or say why it could not be trusted.
    pub fn load(dir: PathBuf, kernel_semantics: &str) -> Result<Store, (Store, Rejected)> {
        let path = Store::path(&dir);
        let text = match std::fs::read_to_string(&path) {
            Ok(t) => t,
            Err(_) => return Err((Store::empty(dir), Rejected::Absent)),
        };
        match parse(&text, kernel_semantics) {
            Ok(entries) => Ok(Store { dir, entries, dirty: false }),
            Err(r) => Err((Store::empty(dir), r)),
        }
    }

    pub fn insert(&mut self, key: Hash, iface: Hash, name: &str) {
        let k = hex(&key);
        if self.entries.contains_key(&k) {
            return;
        }
        self.entries.insert(k, Entry { iface, name: name.to_string() });
        self.dirty = true;
    }

    pub fn contains(&self, key: &Hash) -> bool {
        self.entries.contains_key(&hex(key))
    }

    /// Write the whole file. Whole-file rather than append-only: the checksum
    /// covers the body, and a cache is small enough (one line per declaration)
    /// that incremental writing would buy nothing but a way to be
    /// half-written.
    pub fn save(&self, kernel_semantics: &str) -> std::io::Result<()> {
        std::fs::create_dir_all(&self.dir)?;
        let body = self.body();
        let mut out = String::new();
        out.push_str(&format!("heather-cache\t{FORMAT}\n"));
        out.push_str(&format!("kernel-semantics\t{kernel_semantics}\n"));
        out.push_str(&format!("checksum\t{}\n", hex(&crate::sha256::sha256(body.as_bytes()))));
        out.push_str(&body);
        // Write beside and rename: a run interrupted mid-write must leave the
        // previous cache intact rather than a truncated one that the checksum
        // would (correctly, but pointlessly) reject on every later run.
        let tmp = self.dir.join(format!("{FILE}.tmp"));
        std::fs::write(&tmp, out)?;
        std::fs::rename(&tmp, Store::path(&self.dir))
    }

    fn body(&self) -> String {
        let mut s = String::new();
        for (k, e) in &self.entries {
            s.push_str(&format!("ok\t{k}\t{}\t{}\n", hex(&e.iface), e.name));
        }
        s
    }
}

fn parse(text: &str, kernel_semantics: &str) -> Result<BTreeMap<String, Entry>, Rejected> {
    let mut lines = text.lines();
    let bad = |why: &str| Rejected::Malformed(why.to_string());

    let header = lines.next().ok_or_else(|| bad("the cache file is empty"))?;
    let version = header
        .strip_prefix("heather-cache\t")
        .ok_or_else(|| bad("the cache file does not start with a `heather-cache` header"))?;
    if version != FORMAT {
        return Err(Rejected::Malformed(format!(
            "the cache file is format {version}, this build writes {FORMAT}"
        )));
    }

    let sem = lines.next().ok_or_else(|| bad("the cache file has no `kernel-semantics` line"))?;
    let sem = sem
        .strip_prefix("kernel-semantics\t")
        .ok_or_else(|| bad("the cache file has no `kernel-semantics` line"))?;

    let sum = lines.next().ok_or_else(|| bad("the cache file has no `checksum` line"))?;
    let sum = sum
        .strip_prefix("checksum\t")
        .ok_or_else(|| bad("the cache file has no `checksum` line"))?;

    let body: String = lines.map(|l| format!("{l}\n")).collect();
    if hex(&crate::sha256::sha256(body.as_bytes())) != sum {
        return Err(bad("the cache file's checksum does not match its contents"));
    }

    // Checked *after* the checksum, so a stale-kernel file is reported as a
    // stale kernel rather than as corruption.
    let mut entries = BTreeMap::new();
    for line in body.lines() {
        let f: Vec<&str> = line.split('\t').collect();
        // A short line is corruption; a *long* one is a newer writer's extra
        // column and is read up to what this version understands (§8).
        if f.len() < 4 || f[0] != "ok" {
            return Err(bad("the cache file has a malformed entry line"));
        }
        let key = f[1];
        let iface = unhex(f[2]).ok_or_else(|| bad("a cache entry's interface hash is not a hash"))?;
        if unhex(key).is_none() {
            return Err(bad("a cache entry's key is not a hash"));
        }
        entries.insert(key.to_string(), Entry { iface, name: f[3].to_string() });
    }

    if sem != kernel_semantics {
        return Err(Rejected::KernelChanged { entries: entries.len() });
    }
    Ok(entries)
}
