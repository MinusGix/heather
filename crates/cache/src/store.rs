//! The on-disk cache file (`docs/infrastructure/cache-v1-design.md` §8).
//!
//! One tab-separated text file per store, inspectable with `cat` and `grep`,
//! because the first question anyone asks of a cache is "what does it think it
//! knows". The file holds one **section per kernel** that has written to it
//! (`issues/verdict-store-one-kernel.md`), most recently used first:
//!
//! ```text
//! heather-cache	4
//! kernel	<64 hex fingerprint>	<last used, unix seconds>	<64 hex checksum>
//! ok	<64 hex check key>	<64 hex interface hash>	<name>
//! …
//! kernel	<another kernel's fingerprint>	<last used>	<checksum>
//! ok	…
//! ```
//!
//! A reader believes only its own kernel's section; the others are carried
//! through its save untouched, so checkouts with different kernels sharing a
//! store through `HEATHER_CACHE_DIR` keep each other's verdicts instead of
//! wiping them. A section leaves the file by **age** — unused for
//! [`MAX_AGE_SECS`], or beyond the [`MAX_KERNELS`] most recently used — never
//! because some other kernel saved last. Trust is unchanged: a verdict is only
//! ever accepted under the kernel that recorded it.
//!
//! Two properties the format buys deliberately. **Extra fields are ignored by
//! the reader**, which is the room rung 2 needs: a replay trace lands as a
//! fifth column that an older reader skips, so attaching one is not a format
//! break. And **the verdict is a column**, not implied, so a recorded failure
//! is possible later without one either.
//!
//! What the checksum is and is not: integrity against accident — truncation, a
//! bit flip, a half-written file — checked on load, per section, over its
//! entry lines. It is not a defence against an adversary, who can recompute
//! it. Rung 1's trusted base is "the OS gave us a file nobody tampered with";
//! §6 of the design says so plainly rather than implying more.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::merkle::Hash;
use crate::sha256::{hex, unhex};

/// The format version. Bumped when the *file* shape changes **or when the
/// keys in it stop meaning what they meant** — the kernel fingerprint covers
/// only a changed kernel, and the hashing scheme is ours, not the kernel's.
///
/// `2`: the structural hash walker replaced the rendering-and-rewrite path
/// (`docs/infrastructure/cache-v1-design.md` §12). Every key moved, so every v1 entry is a
/// lie about a declaration it no longer describes. The two would in fact never
/// collide — the domain strings bumped with them — but a silently unmatchable
/// entry is a cache that quietly does nothing, and the version line makes it
/// say so instead.
///
/// `3`: levels are canonical and hashed as their normal form
/// (`issues/kernel-compact-level.md`); the domain strings bumped with it.
///
/// `4`: one section per kernel (`issues/verdict-store-one-kernel.md`). Only
/// the file's *shape* moved — every key still means what it meant at `3` — so
/// a `3` file is still read ([`LEGACY_FORMAT`]): its one kernel becomes one
/// section, and the first save rewrites it at `4`. That keeps the bump from
/// costing every shared store a cold run.
pub const FORMAT: &str = "4";

/// The single-kernel layout before sections: a `kernel-semantics` line and a
/// `checksum` line under the header, then the entries. Read, never written.
pub const LEGACY_FORMAT: &str = "3";

/// A kernel's section is dropped by the next save when no run of that kernel
/// has saved (or refreshed its stamp) for this long. Long enough that a
/// worktree left alone over a holiday comes back warm; short enough that the
/// kernels of a busy week of rounds do not pile up.
pub const MAX_AGE_SECS: u64 = 30 * 24 * 60 * 60;

/// At most this many kernels' sections are kept, the most recently used. A
/// bound on the file whatever the clock says.
pub const MAX_KERNELS: usize = 16;

/// A loaded section's stamp is refreshed by a save once it is this old, even
/// when the run recorded nothing new: a kernel whose every declaration hits
/// is in use, and must not age out for being fully warm.
pub const REFRESH_SECS: u64 = 24 * 60 * 60;

/// A save whose base file is at least this large appends a journal file
/// ([`JOURNAL`]) holding only the entries it added, instead of rewriting the
/// base. The base of a shared test store holds every kernel's section of the
/// last month (over a hundred megabytes, most of it other kernels'), and the
/// library gate's build workers save after every module: rewriting it each
/// time more than doubled the gate's CPU
/// (`issues/verdict-store-append-only-saves.md`). A small store is still
/// rewritten whole, which keeps it one file to `cat`.
pub const JOURNAL_ABOVE_BYTES: u64 = 1 << 20;

/// Once a store's journal holds this many files, the save that finds them
/// folds them into the base (one rewrite per this many saves).
pub const COMPACT_AT_FILES: usize = 64;

/// The directory beside [`FILE`] holding journal files: each one a whole cache
/// file of [`FORMAT`] with one section, the entries one save added. A reader
/// believes a journal section exactly as it would the base's (its kernel,
/// its checksum); a damaged journal file is that file's entries missed and
/// is dropped by the next compaction.
pub const JOURNAL: &str = "entries-v1.d";

/// The file within the cache directory.
///
/// **Deliberately not renamed with the format bump.** A new filename would
/// leave the old file sitting unread and the run would look like a first run;
/// keeping the path is what routes a stale file through `parse` and turns the
/// bump into the message "the cache file is format 1, this build writes 4".
/// The version lives in the header, and the `v1` in the name is a fossil.
pub const FILE: &str = "entries-v1.tsv";

/// One recorded verdict. Keyed by check key; the rest is metadata.
#[derive(Clone, PartialEq, Eq)]
pub struct Entry {
    pub iface: Hash,
    /// Human-facing only. Identity is the key (Unison's rule: names are
    /// metadata over hashes).
    pub name: String,
}

/// A loaded (or fresh) cache: this kernel's section of the file.
pub struct Store {
    pub dir: PathBuf,
    /// Ordered by key hex, so the written file is a deterministic function of
    /// its contents — a cache that rewrote itself differently each run would
    /// be unreviewable and would defeat the checksum's purpose.
    pub entries: BTreeMap<String, Entry>,
    pub dirty: bool,
    /// The loaded section's last-used stamp (unix seconds), when there was
    /// one: what [`Store::wants_save`] reads to keep a warm kernel from
    /// ageing out.
    pub used: Option<u64>,
    /// The keys inserted since the last save: what a journal save writes.
    /// Behind a lock because a save takes `&self` (the build worker saves
    /// after every module and keeps the store).
    fresh: std::sync::Mutex<std::collections::BTreeSet<String>>,
}

/// Why a cache file was not usable. Every variant ends the same way — this
/// run starts with no verdicts and is a full check — but the *reason* is
/// printed, because "the cache silently did nothing" is the failure this
/// design is least able to afford.
pub enum Rejected {
    /// No file. Not an error and not reported: a first run.
    Absent,
    /// The file holds sections for other kernels and none for this one. The
    /// loud, expected one. Those sections are kept for their kernels.
    KernelChanged { entries: usize, kernels: usize },
    /// The file, or this kernel's section of it, is damaged. A save rewrites
    /// it.
    Malformed(String),
}

impl Rejected {
    pub fn message(&self) -> Option<String> {
        match self {
            Rejected::Absent => None,
            Rejected::KernelChanged { entries, kernels } => Some(format!(
                "cache: kernel semantics changed — none of these {entries} entries \
                 ({kernels} other kernel{}) were written by this one; they are kept for \
                 their own kernels, this run is a full check",
                if *kernels == 1 { "" } else { "s" }
            )),
            Rejected::Malformed(why) => Some(format!(
                "cache: {why} — discarding, this run is a full check"
            )),
        }
    }
}

/// The clock sections age by. A clock before the epoch reads as 0, which only
/// ever keeps sections longer.
pub fn now_secs() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

impl Store {
    pub fn empty(dir: PathBuf) -> Store {
        Store { dir, entries: BTreeMap::new(), dirty: false, used: None, fresh: Default::default() }
    }

    pub fn journal(dir: &Path) -> PathBuf {
        dir.join(JOURNAL)
    }

    pub fn path(dir: &Path) -> PathBuf {
        dir.join(FILE)
    }

    /// Load `kernel_semantics`'s section of `dir`'s cache, or say why there
    /// is none to trust: the base file's section, then every journal file's
    /// section for the same kernel ([`JOURNAL`]).
    pub fn load(dir: PathBuf, kernel_semantics: &str) -> Result<Store, (Store, Rejected)> {
        let base = Store::load_base(&dir, kernel_semantics);
        let journal = read_journal(&dir);
        let mut extra: BTreeMap<String, Entry> = BTreeMap::new();
        let mut extra_used: Option<u64> = None;
        let mut other_kernels = std::collections::BTreeSet::new();
        let mut other_entries = 0;
        for (_, text) in &journal {
            let Ok(sections) = parse(text) else { continue };
            for s in sections {
                if s.kernel != kernel_semantics {
                    other_kernels.insert(s.kernel.to_string());
                    other_entries += s.lines.len();
                    continue;
                }
                if let Ok(entries) = s.entries() {
                    extra.extend(entries);
                    extra_used = extra_used.max(s.used);
                }
            }
        }
        match base {
            Ok(mut store) => {
                store.entries.extend(extra);
                store.used = store.used.max(extra_used);
                Ok(store)
            }
            // The base has nothing of this kernel's, but its journal does:
            // a kernel whose saves have all been journal files so far.
            Err((mut store, Rejected::Absent | Rejected::KernelChanged { .. })) if extra_used.is_some() => {
                store.entries = extra;
                store.used = extra_used;
                Ok(store)
            }
            Err((store, Rejected::KernelChanged { entries, kernels })) => {
                Err((store, Rejected::KernelChanged { entries: entries + other_entries, kernels: kernels.max(other_kernels.len()) }))
            }
            Err((store, Rejected::Absent)) if !other_kernels.is_empty() => {
                Err((store, Rejected::KernelChanged { entries: other_entries, kernels: other_kernels.len() }))
            }
            Err(e) => Err(e),
        }
    }

    /// The base file's section for `kernel_semantics`.
    fn load_base(dir: &Path, kernel_semantics: &str) -> Result<Store, (Store, Rejected)> {
        let dir = dir.to_path_buf();
        let path = Store::path(&dir);
        let text = match std::fs::read_to_string(&path) {
            Ok(t) => t,
            Err(_) => return Err((Store::empty(dir), Rejected::Absent)),
        };
        let sections = match parse(&text) {
            Ok(s) => s,
            Err(r) => return Err((Store::empty(dir), r)),
        };
        let Some(mine) = sections.iter().find(|s| s.kernel == kernel_semantics) else {
            let entries = sections.iter().map(|s| s.lines.len()).sum();
            let kernels = sections.len();
            return Err((Store::empty(dir), Rejected::KernelChanged { entries, kernels }));
        };
        // Only this kernel's section is verified entry by entry: another
        // kernel's damage is that kernel's miss (and is dropped by the next
        // save), never this reader's.
        match mine.entries() {
            Ok(entries) => Ok(Store { dir, entries, dirty: false, used: mine.used, fresh: Default::default() }),
            Err(r) => Err((Store::empty(dir), r)),
        }
    }

    pub fn insert(&mut self, key: Hash, iface: Hash, name: &str) {
        let k = hex(&key);
        if self.entries.contains_key(&k) {
            return;
        }
        self.entries.insert(k.clone(), Entry { iface, name: name.to_string() });
        self.fresh.get_mut().unwrap_or_else(|e| e.into_inner()).insert(k);
        self.dirty = true;
    }

    pub fn contains(&self, key: &Hash) -> bool {
        self.entries.contains_key(&hex(key))
    }

    /// Whether a save at `now` would change anything worth writing: new
    /// entries, or a loaded section whose stamp is old enough that it should
    /// be refreshed before it ages out ([`REFRESH_SECS`]).
    pub fn wants_save(&self, now: u64) -> bool {
        self.dirty || self.used.is_some_and(|used| now.saturating_sub(used) >= REFRESH_SECS)
    }

    /// Write the file at the current time. See [`Store::save_at`].
    pub fn save(&self, kernel_semantics: &str) -> std::io::Result<()> {
        self.save_at(kernel_semantics, now_secs())
    }

    /// Record this run's verdicts. When the base file is large
    /// ([`JOURNAL_ABOVE_BYTES`]) and this kernel's stamp is not due a
    /// refresh, only the entries added since the last save are written, as a
    /// journal file; otherwise the base is rewritten whole
    /// ([`Store::rewrite_at`]), folding the journal in.
    pub fn save_at(&self, kernel_semantics: &str, now: u64) -> std::io::Result<()> {
        self.save_with(kernel_semantics, now, JOURNAL_ABOVE_BYTES)
    }

    /// [`Store::save_at`] with the journal threshold given: tests use a small
    /// one so a handful of entries exercises the journal.
    pub fn save_with(&self, kernel_semantics: &str, now: u64, journal_above: u64) -> std::io::Result<()> {
        let stamp_due = self.used.is_some_and(|used| now.saturating_sub(used) >= REFRESH_SECS);
        let base_len = std::fs::metadata(Store::path(&self.dir)).map_or(0, |m| m.len());
        if stamp_due || base_len < journal_above {
            return self.rewrite_at(kernel_semantics, now);
        }
        self.append(kernel_semantics, now)?;
        let files = std::fs::read_dir(Store::journal(&self.dir))
            .map_or(0, |d| d.filter_map(Result::ok).filter(|e| e.path().extension().is_some_and(|x| x == "tsv")).count());
        if files >= COMPACT_AT_FILES {
            self.rewrite_at(kernel_semantics, now)?;
        }
        Ok(())
    }

    /// Write the entries added since the last save as one journal file.
    fn append(&self, kernel_semantics: &str, now: u64) -> std::io::Result<()> {
        let fresh: Vec<String> = std::mem::take(&mut *self.fresh.lock().unwrap_or_else(|e| e.into_inner())).into_iter().collect();
        if fresh.is_empty() {
            return Ok(());
        }
        let entries: BTreeMap<String, Entry> =
            fresh.iter().filter_map(|k| self.entries.get(k).map(|e| (k.clone(), e.clone()))).collect();
        let body = body(&entries);
        let sum = hex(&crate::sha256::sha256(body.as_bytes()));
        let text = format!("heather-cache\t{FORMAT}\nkernel\t{kernel_semantics}\t{now}\t{sum}\n{body}");
        let journal = Store::journal(&self.dir);
        std::fs::create_dir_all(&journal)?;
        let name = unique_name();
        let tmp = journal.join(format!("{name}.tmp"));
        std::fs::write(&tmp, text)?;
        std::fs::rename(&tmp, journal.join(format!("{name}.tsv")))
    }

    /// Write the whole base file, this kernel's section stamped `now`, with
    /// every journal file folded in and then removed. One compaction at a
    /// time (a lock file in the journal directory); a save that finds one
    /// running leaves its entries in the journal for the next.
    pub fn rewrite_at(&self, kernel_semantics: &str, now: u64) -> std::io::Result<()> {
        std::fs::create_dir_all(&self.dir)?;
        let journal_dir = Store::journal(&self.dir);
        let _lock = if journal_dir.is_dir() {
            let lock = std::fs::OpenOptions::new().create(true).truncate(false).write(true).open(journal_dir.join(".compact.lock"))?;
            match lock.try_lock() {
                Ok(()) => Some(lock),
                Err(std::fs::TryLockError::WouldBlock) => {
                    // Another process is compacting; this save's entries go
                    // to the journal instead.
                    return self.append(kernel_semantics, now);
                }
                Err(std::fs::TryLockError::Error(e)) => return Err(e),
            }
        } else {
            None
        };
        // Several processes may share one cache directory (the native test
        // binaries run side by side against `target/cli-check-images`, and
        // several checkouts may share one through `HEATHER_CACHE_DIR`), so
        // the file on disk can have gained entries — and other kernels'
        // sections — since this run loaded it. Union this kernel's in rather
        // than letting the last writer drop the others' verdicts, and carry
        // every other kernel's section through verbatim. A file that does not
        // parse is simply not merged, exactly as `load` would not have
        // trusted it; a damaged section is dropped.
        let on_disk = std::fs::read_to_string(Store::path(&self.dir)).ok();
        let journal = read_journal(&self.dir);
        let sections = on_disk.as_deref().and_then(|text| parse(text).ok()).unwrap_or_default();
        let journal_sections: Vec<Section> =
            journal.iter().filter_map(|(_, text)| parse(text).ok()).flatten().collect();
        let mut mine = self.entries.clone();
        // Every other kernel: its base section's lines and its journal
        // sections', each line as written (a newer writer's extra columns
        // ride along), one line per key.
        let mut others: BTreeMap<&str, (u64, BTreeMap<&str, &str>)> = BTreeMap::new();
        for s in sections.iter().chain(journal_sections.iter()) {
            let Ok(theirs) = s.entries() else { continue };
            if s.kernel == kernel_semantics {
                for (k, e) in theirs {
                    mine.entry(k).or_insert(e);
                }
            } else {
                // A legacy section has no stamp: it is aged from now.
                let used = s.used.unwrap_or(now);
                let slot = others.entry(s.kernel).or_insert((used, BTreeMap::new()));
                slot.0 = slot.0.max(used);
                for line in &s.lines {
                    let key = line.split('\t').nth(1).unwrap_or("");
                    slot.1.entry(key).or_insert(line);
                }
            }
        }
        let mut others: Vec<(u64, &str, BTreeMap<&str, &str>)> = others
            .into_iter()
            .filter(|(_, (used, _))| now.saturating_sub(*used) < MAX_AGE_SECS)
            .map(|(k, (used, lines))| (used, k, lines))
            .collect();
        // Most recently used first, ties by fingerprint, so the file is a
        // deterministic function of what it holds.
        others.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
        others.truncate(MAX_KERNELS - 1);

        let mut out = String::new();
        out.push_str(&format!("heather-cache\t{FORMAT}\n"));
        let body = body(&mine);
        let sum = hex(&crate::sha256::sha256(body.as_bytes()));
        out.push_str(&format!("kernel\t{kernel_semantics}\t{now}\t{sum}\n"));
        out.push_str(&body);
        for (used, kernel, lines) in &others {
            let mut h = crate::sha256::Sha256::new();
            for l in lines.values() {
                h.update(l.as_bytes());
                h.update(b"\n");
            }
            out.push_str(&format!("kernel\t{kernel}\t{used}\t{}\n", hex(&h.finish())));
            for l in lines.values() {
                out.push_str(l);
                out.push('\n');
            }
        }
        // Write beside and rename: a run interrupted mid-write must leave the
        // previous cache intact rather than a truncated one that the checksum
        // would (correctly, but pointlessly) reject on every later run.
        // The temporary name is per writer, so two concurrent saves never
        // interleave into one torn file; each rename is atomic.
        let tmp = self.dir.join(format!("{FILE}.{}.tmp", unique_name()));
        std::fs::write(&tmp, out)?;
        std::fs::rename(&tmp, Store::path(&self.dir))?;
        // Only the journal files read above: one written meanwhile stays for
        // the next compaction.
        for (path, _) in &journal {
            let _ = std::fs::remove_file(path);
        }
        self.fresh.lock().unwrap_or_else(|e| e.into_inner()).clear();
        Ok(())
    }
}

/// A file name no other writer uses: process id and the clock's nanoseconds.
fn unique_name() -> String {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    format!("{}-{nonce}", std::process::id())
}

/// Every journal file of `dir`, path and text, in name order. A file removed
/// between the listing and the read (a compaction) is skipped.
fn read_journal(dir: &Path) -> Vec<(PathBuf, String)> {
    let Ok(listing) = std::fs::read_dir(Store::journal(dir)) else { return Vec::new() };
    let mut paths: Vec<PathBuf> = listing
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "tsv"))
        .collect();
    paths.sort();
    paths.into_iter().filter_map(|p| std::fs::read_to_string(&p).ok().map(|t| (p, t))).collect()
}

fn body(entries: &BTreeMap<String, Entry>) -> String {
    let mut s = String::new();
    for (k, e) in entries {
        s.push_str(&format!("ok\t{k}\t{}\t{}\n", hex(&e.iface), e.name));
    }
    s
}

/// One kernel's section, as read: its entry lines are kept as text until
/// someone asks for them, so a reader pays to verify only its own kernel's.
struct Section<'a> {
    kernel: &'a str,
    /// `None` for a [`LEGACY_FORMAT`] file, which recorded no stamp.
    used: Option<u64>,
    sum: &'a str,
    lines: Vec<&'a str>,
}

impl<'a> Section<'a> {
    fn checksum_matches(&self) -> bool {
        let mut h = crate::sha256::Sha256::new();
        for l in &self.lines {
            h.update(l.as_bytes());
            h.update(b"\n");
        }
        hex(&h.finish()) == self.sum
    }

    /// The section's entries, or why it cannot be trusted.
    fn entries(&self) -> Result<BTreeMap<String, Entry>, Rejected> {
        let bad = |why: &str| Rejected::Malformed(why.to_string());
        if !self.checksum_matches() {
            return Err(bad("the cache file's checksum does not match its contents"));
        }
        let mut entries = BTreeMap::new();
        for line in &self.lines {
            let f: Vec<&str> = line.split('\t').collect();
            // A short line is corruption; a *long* one is a newer writer's
            // extra column and is read up to what this version understands
            // (§8).
            if f.len() < 4 || f[0] != "ok" {
                return Err(bad("the cache file has a malformed entry line"));
            }
            let key = f[1];
            let iface =
                unhex(f[2]).ok_or_else(|| bad("a cache entry's interface hash is not a hash"))?;
            if unhex(key).is_none() {
                return Err(bad("a cache entry's key is not a hash"));
            }
            entries.insert(key.to_string(), Entry { iface, name: f[3].to_string() });
        }
        Ok(entries)
    }
}

/// The file's shape: a version header, then sections. Checksums and entry
/// fields are checked per section ([`Section::entries`]), so that a stale
/// kernel is reported as a stale kernel rather than as corruption, and so
/// that one kernel's damaged section is not every kernel's.
fn parse(text: &str) -> Result<Vec<Section<'_>>, Rejected> {
    let mut lines = text.lines();
    let bad = |why: &str| Rejected::Malformed(why.to_string());

    let header = lines.next().ok_or_else(|| bad("the cache file is empty"))?;
    let version = header
        .strip_prefix("heather-cache\t")
        .ok_or_else(|| bad("the cache file does not start with a `heather-cache` header"))?;
    if version == LEGACY_FORMAT {
        return parse_legacy(lines);
    }
    if version != FORMAT {
        return Err(Rejected::Malformed(format!(
            "the cache file is format {version}, this build writes {FORMAT}"
        )));
    }

    let mut sections: Vec<Section> = Vec::new();
    for line in lines {
        if let Some(rest) = line.strip_prefix("kernel\t") {
            let f: Vec<&str> = rest.split('\t').collect();
            if f.len() < 3 || unhex(f[0]).is_none() || unhex(f[2]).is_none() {
                return Err(bad("the cache file has a malformed `kernel` line"));
            }
            let used = f[1]
                .parse::<u64>()
                .map_err(|_| bad("a cache section's last-used stamp is not a number"))?;
            if sections.iter().any(|s| s.kernel == f[0]) {
                return Err(bad("the cache file has two sections for one kernel"));
            }
            sections.push(Section { kernel: f[0], used: Some(used), sum: f[2], lines: Vec::new() });
        } else {
            let s = sections
                .last_mut()
                .ok_or_else(|| bad("the cache file has an entry before any `kernel` line"))?;
            s.lines.push(line);
        }
    }
    if sections.is_empty() {
        return Err(bad("the cache file has no `kernel` section"));
    }
    Ok(sections)
}

/// A [`LEGACY_FORMAT`] file: one kernel, as one unstamped section.
fn parse_legacy<'a>(mut lines: std::str::Lines<'a>) -> Result<Vec<Section<'a>>, Rejected> {
    let bad = |why: &str| Rejected::Malformed(why.to_string());
    let kernel = lines
        .next()
        .and_then(|l| l.strip_prefix("kernel-semantics\t"))
        .ok_or_else(|| bad("the cache file has no `kernel-semantics` line"))?;
    let sum = lines
        .next()
        .and_then(|l| l.strip_prefix("checksum\t"))
        .ok_or_else(|| bad("the cache file has no `checksum` line"))?;
    Ok(vec![Section { kernel, used: None, sum, lines: lines.collect() }])
}
