//! The instrumentation registry: named timers, named counters, scoped rows
//! and one dump (`docs/instrumentation-design.md`).
//!
//! One place where a check's time is attributed, replacing what used to be
//! `stats::time_kernel` and `omega_cert::OmegaPhases::timed` — the same
//! function written twice — plus five hand-rolled roll-up printers and four
//! environment switches.
//!
//! **Nesting: timers are exclusive, scopes are inclusive.** A bracket running
//! inside another bracket charges only itself; on exit it subtracts what its
//! nested brackets claimed, so every timer column is *self* time and one
//! row's timer columns sum to at most that row's total. A scope row is the
//! opposite by design: a module's total covers its declarations, and the
//! difference between a module's total and the sum of its declarations is the
//! module-level work — parsing, import resolution, image decode, replay,
//! publication.
//!
//! Cost when nobody is measuring: two `Instant::now()` per *phase* entry,
//! where a phase is a whole declaration gate, one of the four parts of a
//! declaration, one unification, one resolution, one head-shape probe, one
//! diagnostic note, one omega stage or one module-image operation — never a
//! conversion step and never an evaluator step (those are counted, in
//! `heather_kernel::stats`). Row collection costs one branch per scope entry
//! when it is off. Always compiled, never feature-gated, so the build that
//! ships is the build that was measured; the expensive samplers — the
//! conversion-miss table, its excerpts, `HEATHER_CONV_MISS_TRACE` — stay
//! behind `value-metrics`.
//!
//! Thread-local by design and not thread-safe: a caller measures the
//! elaborator it drives on its own thread and nothing else.
//!
//! **`HEATHER_TIMINGS_DIR`** is the suite-wide form: every *named* thread
//! other than `main` keeps an *ambient* copy of every scope row, and when it
//! exits writes them to `<dir>/<executable>.<thread>.<n>.tsv`. libtest runs
//! each test on a thread named after it, so one run of the test suite leaves a
//! table per test with no test changed (`scripts/run-test-targets.mjs`,
//! `HEATHER_SUITE_DECLS`). The ambient rows are a second buffer: `enable`,
//! `collecting` and `take_rows` mean exactly what they mean without it, so a
//! test of the instrumentation itself still sees collection off until it
//! turns it on. `main` is left out so a CLI child the tests spawn, which
//! inherits the variable, does not collect behind its own `--timings`.

use std::cell::{Cell, RefCell};
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use heather_kernel::stats as kstats;

use crate::{ValueMetrics, ValueMetricsSnapshot};

// ---------------------------------------------------------------------------
// The named timers and counters
// ---------------------------------------------------------------------------

macro_rules! registry {
    (timers { $($t:ident = $tname:literal),* $(,)? }
     counters { $($c:ident = $cname:literal),* $(,)? }) => {
        /// A named phase. Adding one means adding a bracket at exactly one
        /// call site; the dump's columns follow from this list.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #[repr(usize)]
        pub enum Timer { $($t,)* }

        /// A named event the elaborator counts. Kernel-side counters live in
        /// `heather_kernel::stats` and are read through it.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #[repr(usize)]
        pub enum Counter { $($c,)* }

        impl Timer {
            pub const ALL: &'static [Timer] = &[$(Timer::$t,)*];
            /// TSV column name.
            pub const NAMES: &'static [&'static str] = &[$($tname,)*];
        }

        impl Counter {
            pub const ALL: &'static [Counter] = &[$(Counter::$c,)*];
            /// TSV column name.
            pub const NAMES: &'static [&'static str] = &[$($cname,)*];
        }

        const TIMERS: usize = [$(Timer::$t,)*].len();
        const COUNTERS: usize = [$(Counter::$c,)*].len();
    };
}

registry! {
    timers {
        Parse = "parse_ns",
        Prelude = "prelude_ns",
        KernelGate = "kernel_gate_ns",
        DeclType = "decl_type_ns",
        DeclBody = "decl_body_ns",
        DeclEmit = "decl_emit_ns",
        DeclCommit = "decl_commit_ns",
        Lower = "lower_ns",
        ElabWhnf = "elab_whnf_ns",
        DiagNote = "diag_note_ns",
        Lint = "lint_ns",
        Unify = "unify_ns",
        Resolve = "resolve_ns",
        Matching = "matching_ns",
        ProjectionSubst = "projection_subst_ns",
        ProjectionEmit = "projection_emit_ns",
        InstanceMatch = "instance_match_ns",
        Gendefs = "gendefs_ns",
        OmegaReflect = "omega_reflect_ns",
        OmegaSearch = "omega_search_ns",
        OmegaCutsat = "omega_cutsat_ns",
        OmegaRender = "omega_render_ns",
        OmegaParse = "omega_parse_ns",
        OmegaReconstruct = "omega_reconstruct_ns",
        OmegaCheck = "omega_check_ns",
        ImageDecode = "image_decode_ns",
        ImageRecheck = "image_recheck_ns",
        ImagePublish = "image_publish_ns",
        CacheHash = "cache_hash_ns",
        MerkleWalk = "merkle_walk_ns",
        Cow = "cow_ns",
    }
    counters {
        DeclsGated = "decls_gated",
        GendefsPushed = "gendefs_pushed",
        ResolveGoals = "resolve_goals",
        UnifyCalls = "unify_calls",
        CacheHashes = "cache_hashes",
        DiagNotes = "diag_notes",
        DiagCandidates = "diag_candidates",
        CowCopies = "cow_copies",
        ProjectionNamed = "projection_named",
        ProjectionStructural = "projection_structural",
        InstanceMatchCalls = "instance_match_calls",
    }
}

struct Registry {
    timers: [Cell<u64>; TIMERS],
    counters: [Cell<u64>; COUNTERS],
    /// Nanoseconds charged to brackets nested inside the bracket currently
    /// innermost on this thread — what the exclusive rule subtracts.
    nested: Cell<u64>,
    collecting: Cell<bool>,
    rows: RefCell<Vec<ItemTiming>>,
    /// Where this thread's ambient rows go when it exits
    /// (`HEATHER_TIMINGS_DIR`), and the rows. Decided when the registry is
    /// first touched, because a thread-local destructor cannot ask which
    /// thread it is on.
    dump_to: Option<PathBuf>,
    ambient: RefCell<Vec<ItemTiming>>,
}

impl Default for Registry {
    fn default() -> Self {
        let dump_to = thread_dump_path();
        Registry {
            timers: [const { Cell::new(0) }; TIMERS],
            counters: [const { Cell::new(0) }; COUNTERS],
            nested: Cell::new(0),
            collecting: Cell::new(false),
            rows: RefCell::new(Vec::new()),
            dump_to,
            ambient: RefCell::new(Vec::new()),
        }
    }
}

impl Drop for Registry {
    fn drop(&mut self) {
        let Some(path) = self.dump_to.take() else { return };
        let rows = std::mem::take(self.ambient.get_mut());
        if !rows.is_empty() {
            // Best effort: a thread exiting has nowhere to report a failure.
            let _ = std::fs::write(path, render(&rows));
        }
    }
}

fn timings_dir() -> Option<&'static PathBuf> {
    static DIR: OnceLock<Option<PathBuf>> = OnceLock::new();
    DIR.get_or_init(|| std::env::var_os("HEATHER_TIMINGS_DIR").filter(|v| !v.is_empty()).map(PathBuf::from))
        .as_ref()
}

/// `<dir>/<executable>.<thread>.<n>.tsv` for a named thread other than
/// `main`, when `HEATHER_TIMINGS_DIR` is set. The executable loses Cargo's
/// `-<hash>` suffix; `n` keeps two threads of one name apart.
fn thread_dump_path() -> Option<PathBuf> {
    static SEQ: AtomicUsize = AtomicUsize::new(0);
    let dir = timings_dir()?;
    let thread = std::thread::current();
    let name = thread.name().filter(|n| *n != "main")?;
    let exe = std::env::current_exe().ok()
        .and_then(|p| p.file_stem().map(|s| s.to_string_lossy().into_owned()))
        .unwrap_or_else(|| "unknown".to_string());
    let exe = match exe.rsplit_once('-') {
        Some((stem, hash)) if hash.len() == 16 && hash.bytes().all(|b| b.is_ascii_hexdigit()) => stem.to_string(),
        _ => exe,
    };
    let safe = |s: &str| s.chars().map(|c| if c.is_ascii_alphanumeric() || "_-:".contains(c) { c } else { '_' }).collect::<String>();
    let n = SEQ.fetch_add(1, Ordering::Relaxed);
    Some(dir.join(format!("{}.{}.{n}.tsv", safe(&exe), safe(name))))
}

thread_local! {
    static REG: Registry = Registry::default();
}

/// A run that forgets to drain cannot grow the buffer without bound. Hit only
/// by a caller that enabled collection and never dumped; the dump says so.
const ROW_CAP: usize = 1 << 20;

// ---------------------------------------------------------------------------
// Brackets
// ---------------------------------------------------------------------------

/// An open timer bracket. Charges its own elapsed time, minus whatever nested
/// brackets claimed, to its phase when it finishes.
#[must_use = "a timer guard must be held for the phase it measures"]
pub struct Guard {
    timer: Timer,
    started: Instant,
    /// The enclosing bracket's nested-time accumulator, restored on exit.
    outer_nested: u64,
}

impl Guard {
    /// End the bracket and return its **inclusive** elapsed nanoseconds — what
    /// a caller that also keeps its own per-invocation record wants.
    pub fn finish(self) -> u64 {
        let elapsed = self.started.elapsed().as_nanos() as u64;
        let timer = self.timer;
        let outer = self.outer_nested;
        std::mem::forget(self);
        charge(timer, elapsed, outer);
        elapsed
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        let elapsed = self.started.elapsed().as_nanos() as u64;
        charge(self.timer, elapsed, self.outer_nested);
    }
}

fn charge(timer: Timer, elapsed: u64, outer_nested: u64) {
    REG.with(|r| {
        let inner = r.nested.get();
        let own = elapsed.saturating_sub(inner);
        let cell = &r.timers[timer as usize];
        cell.set(cell.get().saturating_add(own));
        // What this bracket cost is nested time for whatever encloses it.
        r.nested.set(outer_nested.saturating_add(elapsed));
    });
}

/// Open a bracket on `timer`.
pub fn guard(timer: Timer) -> Guard {
    let outer_nested = REG.with(|r| r.nested.replace(0));
    Guard { timer, started: Instant::now(), outer_nested }
}

/// Run `f` inside a bracket on `timer`.
pub fn timed<T>(timer: Timer, f: impl FnOnce() -> T) -> T {
    let g = guard(timer);
    let out = f();
    drop(g);
    out
}

/// Charge `ns` to `timer` as if a bracket had just closed around it — for the
/// handful of sites that already hold their own clock for a per-invocation
/// record. Registers as nested time for the enclosing bracket, so the
/// exclusive rule still holds.
pub fn add(timer: Timer, ns: u64) {
    REG.with(|r| {
        let cell = &r.timers[timer as usize];
        cell.set(cell.get().saturating_add(ns));
        r.nested.set(r.nested.get().saturating_add(ns));
    });
}

/// Bump a named elaborator counter.
#[inline]
pub fn count(counter: Counter) {
    REG.with(|r| {
        let cell = &r.counters[counter as usize];
        cell.set(cell.get().wrapping_add(1));
    });
}

// ---------------------------------------------------------------------------
// Copy-on-write
// ---------------------------------------------------------------------------

// The elaborator's registries are persistent by `Rc` sharing: a clone, a
// checkpoint or a semantic image holds the same maps, and the first write
// after one copies what it writes through. That copy is usually of a
// *current-module* layer — the part that grows with the module — so a write
// made once per declaration while something else holds the layer is
// O(module) per declaration, and a large module goes quadratic without any
// counter moving. It happened twice before this seam existed
// (issues/check-module-delta-certificate-cost.md: the journal clone, the
// per-slice replay checkpoint), both found only by a profiler.
//
// [`make_mut`] is `Rc::make_mut` with the copying case made visible: the
// `cow_copies` column counts writes that copied, `cow_ns` is the time they
// took, and the per-site table beside a `--timings` file (`*.cow-sites.txt`)
// names the write that paid, through `#[track_caller]`.

thread_local! {
    static COW_SITES: RefCell<std::collections::BTreeMap<(&'static str, u32, &'static str), (u64, u64)>> =
        const { RefCell::new(std::collections::BTreeMap::new()) };
}

/// `Rc::make_mut`, counted and timed when it copies. Every registry
/// copy-on-write write goes through here.
#[track_caller]
#[inline]
pub fn make_mut<T: Clone>(rc: &mut std::sync::Arc<T>) -> &mut T {
    if std::sync::Arc::strong_count(rc) == 1 && std::sync::Arc::weak_count(rc) == 0 {
        return std::sync::Arc::make_mut(rc);
    }
    cow_copy(std::panic::Location::caller(), rc)
}

#[cold]
#[inline(never)]
fn cow_copy<'a, T: Clone>(site: &'static std::panic::Location<'static>, rc: &'a mut std::sync::Arc<T>) -> &'a mut T {
    count(Counter::CowCopies);
    let guard = guard(Timer::Cow);
    std::sync::Arc::make_mut(rc);
    let ns = guard.finish();
    COW_SITES.with(|sites| {
        let mut sites = sites.borrow_mut();
        let entry = sites.entry((site.file(), site.line(), std::any::type_name::<T>())).or_default();
        entry.0 += 1;
        entry.1 += ns;
    });
    std::sync::Arc::get_mut(rc).expect("make_mut left the value unshared")
}

/// `alloc::vec::Vec<heather_kernel::term::Type>` as `Vec<Type>`: every
/// module path dropped, generics kept.
fn short_type(ty: &str) -> String {
    let mut out = String::new();
    let mut word = String::new();
    let mut chars = ty.chars().peekable();
    while let Some(c) = chars.next() {
        if c == ':' && chars.peek() == Some(&':') {
            chars.next();
            word.clear();
        } else if c.is_alphanumeric() || c == '_' {
            word.push(c);
        } else {
            out.push_str(&word);
            word.clear();
            out.push(c);
        }
    }
    out + &word
}

/// This thread's copying writes by site and copied type since the last call,
/// costliest first: `copies\tms\ttype\tfile:line`. Empty when nothing
/// copied. The type is what tells a cheap copy from a costly one: a
/// persistent `GlobalCtx` or the committed world's handle struct copies in
/// O(1), a registry layer in O(what it holds).
pub fn take_cow_sites() -> String {
    let sites = COW_SITES.with(|sites| std::mem::take(&mut *sites.borrow_mut()));
    let mut rows: Vec<_> = sites.into_iter().collect();
    rows.sort_by_key(|(_, (_, ns))| std::cmp::Reverse(*ns));
    let mut out = String::new();
    for ((file, line, ty), (copies, ns)) in rows {
        use std::fmt::Write as _;
        let ty = short_type(ty);
        let _ = writeln!(out, "{copies}\t{:.1}\t{ty}\t{file}:{line}", ns as f64 / 1e6);
    }
    out
}

// ---------------------------------------------------------------------------
// The kernel-gate compatibility surface
// ---------------------------------------------------------------------------

/// Nanoseconds spent in the kernel gate on this thread since the last
/// [`reset_kernel_ns`].
///
/// What counts is deliberately narrow and unchanged by the registry: the
/// `typing::check_*` calls that gate a *finished* declaration (and the meta
/// layer's equivalents in `quote.rs`). The elaborator's other trips into the
/// kernel — `whnf`, `conv_type`, every unification step — stay on the
/// elaborate side of the split, because they are elaboration deciding
/// something, not the kernel re-checking a result. So
/// `elaborate = total − parse − kernel-gate` remains "the elaborator's own
/// work, including the conversion it does while working", which is the
/// quantity a frontend regression would move
/// (`docs/frontend-benchmarking.md`).
pub fn kernel_ns() -> u64 {
    REG.with(|r| r.timers[Timer::KernelGate as usize].get())
}

/// Zero the kernel-gate accumulator. Call before the elaboration you want to
/// attribute.
pub fn reset_kernel_ns() {
    REG.with(|r| r.timers[Timer::KernelGate as usize].set(0));
}

/// Run `f`, charging its duration to the kernel gate.
pub(crate) fn time_kernel<T>(f: impl FnOnce() -> T) -> T {
    count(Counter::DeclsGated);
    timed(Timer::KernelGate, f)
}

/// Fold a kernel worker's numbers for one deferred item back in
/// (`docs/parallel-kernel-gate-design.md` §7).
///
/// The kernel *counters* gain the worker's delta on this thread, so every
/// scope still open — the module row, the run row — accounts for work done
/// off it; a count is a count at any width. The worker's **clock** is not
/// added to the timer cell, and that is the width-independence rule: an
/// enclosing row's phase columns are wall, its `total_ns` is wall, and CPU
/// summed across eight workers does not fit inside either. What the enclosing
/// rows are charged instead is the join's own wall — the time this thread
/// really spent blocked — by [`add`] at the join
/// (`docs/parallel-kernel-gate-design.md` §7).
///
/// The worker's clock goes where it was spent: the item row named by `row`,
/// which closed while the worker was still running, is patched in place, its
/// `total_ns` growing by the same amount as its phases so that the exclusive
/// rule (`phases <= total`) survives the patch. `--timings` therefore keeps
/// its shape at every width: one `kernel_gate_ns` per declaration, and no row
/// claiming more phase time than it took.
pub(crate) fn fold_deferred_kernel(
    row: Option<&(String, String)>,
    ns: u64,
    kernel: &kstats::Snapshot,
) {
    kstats::merge(kernel);
    patch_item_row(row, ns, kernel);
}

/// The same patch for a verdict the serial replay *reused* rather than
/// re-earned (`docs/parallel-kernel-gate-design.md` §5.2): the declaration's
/// row still says what its proof cost, and the cost is the worker's, since
/// that is who paid it.
///
/// The counters are deliberately **not** merged here. The discarded pass's own
/// join already merged every worker's delta into this thread, and the
/// enclosing module and run rows kept it — a discarded pass's timer cells are
/// not rolled back (§7). Only the item rows were thrown away with the pass,
/// and those are exactly what this restores.
pub(crate) fn fold_reused_kernel(row: &(String, String), ns: u64, kernel: &kstats::Snapshot) {
    patch_item_row(Some(row), ns, kernel);
}

fn patch_item_row(row: Option<&(String, String)>, ns: u64, kernel: &kstats::Snapshot) {
    REG.with(|r| {
        let Some((module, item)) = row else { return };
        let mut rows = r.rows.borrow_mut();
        let Some(found) = rows.iter_mut().rev().find(|candidate| {
            candidate.kind == ScopeKind::Item
                && candidate.module == *module
                && candidate.item == *item
        }) else {
            return;
        };
        found.total_ns = found.total_ns.saturating_add(ns);
        found.kernel_ns = found.kernel_ns.saturating_add(ns);
        let gate = &mut found.timers[Timer::KernelGate as usize];
        *gate = gate.saturating_add(ns);
        found.kernel = found.kernel.plus(kernel);
    });
}

// ---------------------------------------------------------------------------
// Scopes and rows
// ---------------------------------------------------------------------------

/// What one row of the dump is about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScopeKind {
    /// One surface declaration, including the generated declarations and the
    /// elaborator-side conversion performed while processing it.
    Item,
    /// One module of the import closure, replay and publication included.
    Module,
    /// The whole invocation.
    Run,
}

impl ScopeKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ScopeKind::Item => "item",
            ScopeKind::Module => "module",
            ScopeKind::Run => "run",
        }
    }
}

/// One attributed scope: what it cost and what it did.
///
/// `kernel_ns` is the final declaration-gate subset of `total_ns`; the
/// remainder is the elaborator's own work. On an item row it is
/// parser-independent, because both module paths parse the whole file before
/// the first item scope opens.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemTiming {
    pub kind: ScopeKind,
    pub module: String,
    pub item: String,
    pub total_ns: u64,
    pub kernel_ns: u64,
    /// Self time per named phase, in [`Timer::ALL`] order.
    pub timers: [u64; TIMERS],
    /// Named elaborator events, in [`Counter::ALL`] order.
    pub counters: [u64; COUNTERS],
    /// What the kernel counted while this scope was open.
    pub kernel: kstats::Snapshot,
    /// Value-machine activity attributable to this scope when the opt-in
    /// `value-metrics` collector is enabled.
    pub value_metrics: Option<ValueMetricsSnapshot>,
}

impl ItemTiming {
    /// Time not accounted for by any named phase.
    pub fn other_ns(&self) -> u64 {
        self.total_ns.saturating_sub(self.timers.iter().sum())
    }
}

/// An open scope. Pushes one row when dropped, if collection is on.
#[must_use = "a scope guard must be held for the work it attributes"]
pub struct ScopeGuard {
    open: Option<Open>,
}

struct Open {
    /// Collection was on at open (the row goes to `rows`); the thread keeps
    /// ambient rows (it also goes to `ambient`).
    explicit: bool,
    ambient: bool,
    kind: ScopeKind,
    module: String,
    item: String,
    started: Instant,
    timers: [u64; TIMERS],
    counters: [u64; COUNTERS],
    kernel: kstats::Snapshot,
    value_metrics: Option<ValueMetricsSnapshot>,
}

thread_local! {
    /// The declaration scopes open on this thread, innermost last. Maintained
    /// only while collection is on (a `ScopeGuard` with no `Open` touches
    /// nothing), and read by the deferred kernel gate to remember which row a
    /// queued check's numbers belong to.
    static ITEMS: RefCell<Vec<(String, String)>> = const { RefCell::new(Vec::new()) };
}

/// The innermost declaration scope open on this thread, if any.
pub(crate) fn current_item() -> Option<(String, String)> {
    ITEMS.with(|s| s.borrow().last().cloned())
}

impl Drop for ScopeGuard {
    fn drop(&mut self) {
        let Some(open) = self.open.take() else { return };
        if open.kind == ScopeKind::Item {
            ITEMS.with(|s| {
                s.borrow_mut().pop();
            });
        }
        let total_ns = open.started.elapsed().as_nanos() as u64;
        let (timers, counters) = REG.with(|r| {
            let mut t = [0u64; TIMERS];
            for (i, cell) in r.timers.iter().enumerate() {
                t[i] = cell.get().wrapping_sub(open.timers[i]);
            }
            let mut c = [0u64; COUNTERS];
            for (i, cell) in r.counters.iter().enumerate() {
                c[i] = cell.get().wrapping_sub(open.counters[i]);
            }
            (t, c)
        });
        let row = ItemTiming {
            kind: open.kind,
            module: open.module,
            item: open.item,
            total_ns,
            kernel_ns: timers[Timer::KernelGate as usize],
            timers,
            counters,
            kernel: kstats::snapshot().since(&open.kernel),
            value_metrics: current_value_metrics()
                .zip(open.value_metrics)
                .map(|(after, before)| after.saturating_sub(before)),
        };
        REG.with(|r| {
            let push = |buf: &RefCell<Vec<ItemTiming>>, row| {
                let mut buf = buf.borrow_mut();
                if buf.len() < ROW_CAP {
                    buf.push(row);
                }
            };
            match (open.explicit, open.ambient) {
                (true, true) => {
                    push(&r.ambient, row.clone());
                    push(&r.rows, row);
                }
                (false, true) => push(&r.ambient, row),
                _ => push(&r.rows, row),
            }
        });
    }
}

thread_local! {
    /// The collector a scope should read, lent by the elaborator that owns it.
    /// `None` when no elaborator on this thread is collecting; the columns are
    /// meaningful only under the `value-metrics` feature, which is what makes
    /// the collector count anything.
    static METRICS: RefCell<Option<ValueMetrics>> = const { RefCell::new(None) };
}

fn current_value_metrics() -> Option<ValueMetricsSnapshot> {
    METRICS.with(|m| m.borrow().as_ref().map(|v| v.snapshot()))
}

/// Lend the registry the value-machine collector, so that scope rows can carry
/// its columns. Installed by `Elaborator::enable_value_metrics`.
pub(crate) fn set_value_metrics_source(source: Option<ValueMetrics>) {
    METRICS.with(|m| *m.borrow_mut() = source);
}

/// Open a scope. Free (one branch, no clock, no allocation) when collection is
/// off, so an item bracket is paid only by a run that asked for one.
pub fn scope(kind: ScopeKind, module: &str, item: &str) -> ScopeGuard {
    let (explicit, ambient) = REG.with(|r| (r.collecting.get(), r.dump_to.is_some()));
    if !explicit && !ambient {
        return ScopeGuard { open: None };
    }
    let (timers, counters) = REG.with(|r| {
        let mut t = [0u64; TIMERS];
        for (i, cell) in r.timers.iter().enumerate() {
            t[i] = cell.get();
        }
        let mut c = [0u64; COUNTERS];
        for (i, cell) in r.counters.iter().enumerate() {
            c[i] = cell.get();
        }
        (t, c)
    });
    if kind == ScopeKind::Item {
        ITEMS.with(|s| s.borrow_mut().push((module.to_string(), item.to_string())));
    }
    ScopeGuard {
        open: Some(Open {
            explicit,
            ambient,
            kind,
            module: module.to_string(),
            item: item.to_string(),
            started: Instant::now(),
            timers,
            counters,
            kernel: kstats::snapshot(),
            value_metrics: current_value_metrics(),
        }),
    }
}

/// Begin collecting scope rows on this thread.
pub fn enable() {
    REG.with(|r| r.collecting.set(true));
}

/// Stop collecting scope rows on this thread. Open scopes still push.
pub fn disable() {
    REG.with(|r| r.collecting.set(false));
}

/// Whether scope rows are being collected on this thread.
pub fn collecting() -> bool {
    REG.with(|r| r.collecting.get())
}

/// Drain the collected rows without disabling collection.
pub fn take_rows() -> Vec<ItemTiming> {
    REG.with(|r| r.rows.borrow_mut().drain(..).collect())
}

/// How many rows have been collected on this thread, in both buffers.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RowsMark {
    rows: usize,
    ambient: usize,
}

pub(crate) fn rows_mark() -> RowsMark {
    REG.with(|r| RowsMark { rows: r.rows.borrow().len(), ambient: r.ambient.borrow().len() })
}

/// Drop every row collected since [`rows_mark`]. The one caller is the
/// deferred gate's serial fallback (`docs/parallel-kernel-gate-design.md`
/// §5.1): a discarded pass leaves no declaration rows behind, so `--timings`
/// has one row per declaration at every width rather than two for a module
/// that had to be re-checked. The *cells* are deliberately not rolled back —
/// the abandoned pass really did spend that wall, and the enclosing module
/// row is the honest place for it.
pub(crate) fn truncate_rows(mark: RowsMark) {
    REG.with(|r| {
        r.rows.borrow_mut().truncate(mark.rows);
        r.ambient.borrow_mut().truncate(mark.ambient);
    });
}

// ---------------------------------------------------------------------------
// The dump
// ---------------------------------------------------------------------------

/// Where a dump goes: a file, or the standard error stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Dest {
    Stderr,
    File(std::path::PathBuf),
}

impl Dest {
    /// `-` means stderr; anything else is a path. This is what
    /// `HEATHER_TIMINGS` and `--timings` both parse.
    pub fn parse(spec: &str) -> Dest {
        if spec == "-" { Dest::Stderr } else { Dest::File(std::path::PathBuf::from(spec)) }
    }

    /// The destination `HEATHER_TIMINGS` names, if it names one.
    pub fn from_env() -> Option<Dest> {
        std::env::var("HEATHER_TIMINGS").ok().map(|spec| Dest::parse(&spec))
    }
}

/// The TSV header: the stable column order every dump writes.
pub fn header() -> String {
    let mut out = String::from("scope\tmodule\titem\ttotal_ns\tother_ns");
    for name in Timer::NAMES {
        out.push('\t');
        out.push_str(name);
    }
    for name in Counter::NAMES {
        out.push('\t');
        out.push_str(name);
    }
    for name in kstats::Snapshot::NAMES {
        out.push('\t');
        out.push_str(name);
    }
    out.push_str("\tterm_cache_lookups\tterm_cache_hits\ttype_cache_lookups\ttype_cache_hits");
    out.push('\n');
    out
}

fn row_line(row: &ItemTiming, out: &mut String) {
    use std::fmt::Write;
    let _ = write!(
        out,
        "{}\t{}\t{}\t{}\t{}",
        row.kind.as_str(),
        row.module,
        row.item,
        row.total_ns,
        row.other_ns()
    );
    for ns in &row.timers {
        let _ = write!(out, "\t{ns}");
    }
    for n in &row.counters {
        let _ = write!(out, "\t{n}");
    }
    for n in row.kernel.values() {
        let _ = write!(out, "\t{n}");
    }
    match row.value_metrics {
        Some(m) => {
            let _ = write!(
                out,
                "\t{}\t{}\t{}\t{}",
                m.term_cache_lookups, m.term_cache_hits, m.type_cache_lookups, m.type_cache_hits
            );
        }
        None => out.push_str("\t\t\t\t"),
    }
    out.push('\n');
}

/// Render rows as the TSV of `docs/instrumentation-design.md` §4.
pub fn render(rows: &[ItemTiming]) -> String {
    let mut out = header();
    for row in rows {
        row_line(row, &mut out);
    }
    out
}

/// Write the rows to `dest`. The one dump: `heather check --timings`,
/// `--item-timings` on the native commands, and every test that used to print
/// its own roll-up go through here, so there is one format to learn.
pub fn dump(dest: &Dest, rows: &[ItemTiming]) -> std::io::Result<()> {
    let text = render(rows);
    match dest {
        Dest::Stderr => {
            eprint!("{text}");
            Ok(())
        }
        Dest::File(path) => {
            std::fs::write(path, text)?;
            eprintln!("timings: {} rows in {}", rows.len(), path.display());
            // The copy-on-write sites behind the `cow_*` columns, beside it.
            let sites = take_cow_sites();
            if !sites.is_empty() {
                let beside = path.with_extension("cow-sites.txt");
                std::fs::write(&beside, format!("copies\tms\ttype\tsite\n{sites}"))?;
            }
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// The decline listing
// ---------------------------------------------------------------------------

// `HEATHER_GENDEF_DECLINES=1`: one line per *decline* of the generated-
// definition devices — the per-instantiation type code
// (`docs/per-instantiation-type-codes-design.md` §4.1) and the record
// projections over it (§13) — naming the site, the declaration and the
// reason.
//
// It exists because a decline is **silent**: a device that never registered
// and a device that registered and lost look exactly alike from outside, and
// §13.7 asked for this listing twice and got a throwaway both times. So it is
// permanent, and it takes the sampler's rule: behind `value-metrics`, inert
// unless the environment asks, and compiled out of the build that ships.
//
// A decline is far more frequent than a conversion miss — every type the
// emission walk passes asks — so the environment is read once per thread and
// the reason's formatting happens only inside the switch.

#[cfg(feature = "value-metrics")]
thread_local! {
    static DECLINES: Cell<Option<bool>> = const { Cell::new(None) };
}

/// Whether `HEATHER_GENDEF_DECLINES` asked for the listing (cached per thread).
#[cfg(feature = "value-metrics")]
pub fn declines_wanted() -> bool {
    DECLINES.with(|d| match d.get() {
        Some(v) => v,
        None => {
            let v = std::env::var_os("HEATHER_GENDEF_DECLINES")
                .is_some_and(|v| !v.is_empty() && v != "0");
            d.set(Some(v));
            v
        }
    })
}

/// One decline: the site that declined, the declaration it declined for, the
/// reason, and the declaration scope it happened in. Tab-separated so a run is
/// grouped with `cut`/`sort`.
#[cfg(feature = "value-metrics")]
pub fn note_decline(site: &str, decl: &str, reason: std::fmt::Arguments<'_>) {
    let item = current_item().map_or_else(|| "-".to_string(), |(m, i)| format!("{m}::{i}"));
    eprintln!("gendef-decline\t{site}\t{decl}\t{reason}\t{item}");
}

/// Record one decline (see above). Nothing is formatted, and none of the
/// arguments are evaluated, unless the listing is on; without the
/// `value-metrics` feature nothing is compiled at all.
macro_rules! decline {
    ($site:literal, $decl:expr, $($reason:tt)*) => {{
        #[cfg(feature = "value-metrics")]
        if $crate::stats::declines_wanted() {
            $crate::stats::note_decline($site, $decl, format_args!($($reason)*));
        }
    }};
}
pub(crate) use decline;

/// Collect (if `HEATHER_TIMINGS` asks) around `f`, then dump. What a test
/// binary calls instead of hand-rolling a roll-up printer.
pub fn with_env_timings<T>(label: &str, f: impl FnOnce() -> T) -> T {
    let Some(dest) = Dest::from_env() else { return f() };
    enable();
    let out = {
        let _run = scope(ScopeKind::Run, label, "");
        f()
    };
    let rows = take_rows();
    let _ = dump(&dest, &rows);
    disable();
    out
}

#[cfg(test)]
mod tests {
    use std::sync::Arc as Rc;

    use super::*;

    #[test]
    fn only_a_write_that_copies_is_counted_and_named() {
        take_cow_sites();
        let mut alone = Rc::new(vec![1u32]);
        make_mut(&mut alone).push(2);
        assert_eq!(take_cow_sites(), "", "an unshared write copies nothing");

        let mut shared = Rc::new(vec![1u32]);
        let held = Rc::clone(&shared);
        make_mut(&mut shared).push(2);
        assert_eq!((held.len(), shared.len()), (1, 2), "make_mut semantics are unchanged");
        let sites = take_cow_sites();
        assert!(sites.starts_with("1\t") && sites.contains(file!()), "the copy names this file: {sites:?}");
        assert!(sites.contains("\tVec<u32>\t"), "and the type it copied: {sites:?}");
    }
}
