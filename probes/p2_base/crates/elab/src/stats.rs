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

use std::cell::{Cell, RefCell};
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
    }
    counters {
        DeclsGated = "decls_gated",
        GendefsPushed = "gendefs_pushed",
        ResolveGoals = "resolve_goals",
        UnifyCalls = "unify_calls",
        CacheHashes = "cache_hashes",
        DiagNotes = "diag_notes",
        DiagCandidates = "diag_candidates",
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
}

impl Default for Registry {
    fn default() -> Self {
        Registry {
            timers: [const { Cell::new(0) }; TIMERS],
            counters: [const { Cell::new(0) }; COUNTERS],
            nested: Cell::new(0),
            collecting: Cell::new(false),
            rows: RefCell::new(Vec::new()),
        }
    }
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
            let mut rows = r.rows.borrow_mut();
            if rows.len() < ROW_CAP {
                rows.push(row);
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
    if !REG.with(|r| r.collecting.get()) {
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

/// How many rows have been collected on this thread.
pub(crate) fn rows_mark() -> usize {
    REG.with(|r| r.rows.borrow().len())
}

/// Drop every row collected since [`rows_mark`]. The one caller is the
/// deferred gate's serial fallback (`docs/parallel-kernel-gate-design.md`
/// §5.1): a discarded pass leaves no declaration rows behind, so `--timings`
/// has one row per declaration at every width rather than two for a module
/// that had to be re-checked. The *cells* are deliberately not rolled back —
/// the abandoned pass really did spend that wall, and the enclosing module
/// row is the honest place for it.
pub(crate) fn truncate_rows(mark: usize) {
    REG.with(|r| {
        let mut rows = r.rows.borrow_mut();
        if rows.len() > mark {
            rows.truncate(mark);
        }
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
            Ok(())
        }
    }
}

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
