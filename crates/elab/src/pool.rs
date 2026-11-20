//! The deferred kernel gate: a pool of kernel worker threads
//! (`docs/kernel/parallel-kernel-gate-design.md`, `issues/parallel-kernel-gate.md`).
//!
//! The elaborator checks a declaration's *statement* synchronously — dependents
//! need it — commits the binding to Ψ, and queues the proof/body's
//! `typing::check_term` here with the Ψ prefix it must be checked against. The
//! module joins every outstanding check before it is accepted, published, or
//! emitted; any failure fails the module, reported in declaration order.
//!
//! Nothing is shared with a worker but the frozen prefix and the item, both
//! immutable and both behind `Arc`. Every piece of checker state — `Tc`, its
//! conversion memo, the value arena, `GlobalCache`, the bounds memo, the budget
//! cells, both stats registries — is per-thread by construction, because it is
//! either created inside `check_term` or declared `thread_local!`.
//!
//! A pass the join refuses is discarded and replayed serially, and its
//! *verdicts* travel with it: [`Replay`] lets the replay reuse a kernel answer
//! wherever its own inputs are structurally the ones a worker was handed, so
//! the dev loop's commonest module — a probe of one or two declarations, one
//! of them meant to be refused — pays for one kernel pass and not two
//! (`docs/kernel/parallel-kernel-gate-design.md` §5.2).
//!
//! `workers == 1` spawns nothing: the gate sites run the code they always ran,
//! in the order they always ran it, and the pool exists in that configuration
//! only to answer `is_inline()`. It is what a clone gets, and what the serial
//! fallback (`docs/kernel/parallel-kernel-gate-design.md` §5.1) re-runs a failed
//! module at — a module's answer never depends on the width.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::stats as kstats;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::{self, TypeError};
use heather_syntax::Span;

use heather_kernel::rc::Rc;

/// The `Arc`-by-alias premise, as a compile error rather than a mystery: a
/// kernel type that grows a non-`Send` field breaks the build here and not in
/// the middle of the pool.
const _: fn() = || {
    fn assert<T: Send + Sync + 'static>() {}
    assert::<Term>();
    assert::<Type>();
    assert::<Level>();
    assert::<LocalCtx>();
    assert::<GlobalCtx>();
    assert::<TypeError>();
};

/// One queued proof obligation: exactly the arguments `typing::check_term`
/// takes, plus what the join needs to rebuild a [`crate::gate::GateItem`] and
/// to report a failure where the declaration is.
pub(crate) struct Deferred {
    pub(crate) name: String,
    pub(crate) span: Span,
    /// The frozen prefix. O(1) to snapshot: `GlobalBindings` is persistent
    /// (sealed chunks plus a bounded tail), so this is one refcount bump.
    pub(crate) psi: Rc<GlobalCtx>,
    pub(crate) ctx: LocalCtx,
    pub(crate) ty: Type,
    pub(crate) level: Level,
    pub(crate) body: Term,
    pub(crate) opaque: bool,
    pub(crate) layer: Layer,
    pub(crate) lands_in_psi: bool,
    pub(crate) fuel: u64,
    /// The sealed proofs the statement's check opened, on the queuing
    /// thread, before the body was queued (`heather_kernel::unseal`): the
    /// verdict depends on them as much as on the body's own.
    pub(crate) unsealed: Vec<usize>,
    /// The declaration scope open when this was queued — the row its timings
    /// fold back into (`docs/kernel/parallel-kernel-gate-design.md` §7). `None` when
    /// nothing is collecting.
    pub(crate) row: Option<(String, String)>,
}

impl Deferred {
    fn check(&self) -> Result<(), TypeError> {
        typing::check_term(
            &self.psi,
            0,
            self.layer,
            &self.ctx,
            &self.body,
            &self.ty,
            &self.level,
            self.fuel,
        )
    }
}

/// How one queued check ended, and what it cost.
pub(crate) struct Outcome {
    pub(crate) index: usize,
    pub(crate) item: Rc<Deferred>,
    /// `Err(None)` is a worker panic: a module failure naming the item, never
    /// a hang.
    pub(crate) verdict: Result<(), Option<TypeError>>,
    pub(crate) ns: u64,
    pub(crate) kernel: kstats::Snapshot,
    /// Absolute Ψ indices of the sealed proofs the check opened, the
    /// statement's included: what `KernelGate::accepted` must be told, and
    /// what the module's slices charge to the item that queued this.
    pub(crate) unsealed: Vec<usize>,
}

fn run(index: usize, item: Rc<Deferred>) -> Outcome {
    let peaks = kstats::peak_scope_open();
    let before = kstats::snapshot();
    let started = std::time::Instant::now();
    // A panic in a worker must not poison the queue or wedge the join. It is
    // reported as this item failing, which is what a panic on the elaborator's
    // own thread would have amounted to.
    let checked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        heather_kernel::unseal::record(|| item.check())
    }));
    let mut unsealed = item.unsealed.clone();
    let verdict = match checked {
        Ok((Ok(()), opened)) => {
            unsealed.extend(opened);
            Ok(())
        }
        Ok((Err(e), _)) => Err(Some(e)),
        Err(_) => Err(None),
    };
    unsealed.sort_unstable();
    unsealed.dedup();
    let ns = started.elapsed().as_nanos() as u64;
    let kernel = kstats::snapshot().since(&before);
    kstats::peak_scope_close(peaks);
    Outcome { index, item, verdict, ns, kernel, unsealed }
}

// ---------------------------------------------------------------------------
// Verdict reuse across the discard (`docs/kernel/parallel-kernel-gate-design.md` §5.2)
// ---------------------------------------------------------------------------

/// One verdict a discarded parallel pass already earned, and exactly the
/// inputs it was earned for.
///
/// Copied out of the [`Deferred`] rather than holding it: what has to survive
/// the discard is the binding (an `Arc` bump per component — the term graph is
/// shared, not copied) and the Ψ prefix's *length*, not the prefix itself, and
/// not the span or the timing row. A replayed module holds one of these per
/// obligation while its own pass rebuilds the same terms from source, so what
/// this struct does not carry is memory the two passes do not overlap on.
struct Recorded {
    psi_len: usize,
    name: String,
    ctx: LocalCtx,
    ty: Type,
    level: Level,
    body: Term,
    opaque: bool,
    layer: Layer,
    lands_in_psi: bool,
    fuel: u64,
    /// A worker *panic* is not a verdict and is never recorded, so this is the
    /// kernel's own answer and nothing else.
    verdict: Result<(), TypeError>,
    ns: u64,
    kernel: kstats::Snapshot,
    unsealed: Vec<usize>,
}

/// What a discarded pass leaves the serial replay: its verdicts, in submission
/// order, reusable exactly as far as the replay's inputs are identical.
///
/// **Why this is not a second trust seam.** A verdict is reused only for a
/// kernel call whose inputs — the binding (context, statement, level, body,
/// opacity, layer, fuel) and the length of the Ψ prefix it is checked against
/// — are structurally identical to a call the same kernel already answered in
/// this process. Elaboration is deterministic, so replaying the same source in
/// the same order reproduces the same bindings up to and including the first
/// failure: if every obligation before index *j* matched, the replay's Ψ
/// prefix at *j* is the prefix the worker saw, entry for entry, and the
/// kernel is a function of (Ψ, binding). One mismatch is therefore fatal to
/// the whole tail — [`Replay::live`] goes false and stays false — because
/// after it the prefixes may have diverged and Ψ's *length* alone no longer
/// witnesses its contents. The first reused rejection diverges by
/// construction (the serial pass does not commit the declaration it refuses),
/// which is what turns reuse off for everything after it.
///
/// Nothing crosses a process boundary and nothing is stored: this list dies
/// with the replay that consumes it. `KernelGate::accepted` is still recorded
/// only by the serial pass, verdict reused or not.
pub(crate) struct Replay {
    /// Each entry is **taken** the moment it is compared, and the whole list is
    /// dropped at the first mismatch: the replay is re-elaborating the same
    /// declarations, so a recorded binding and its replacement are alive at the
    /// same time only across the comparison that retires it.
    entries: Vec<Option<Recorded>>,
    /// How far the replay has got, while `live`.
    at: usize,
    /// Whether the inputs have matched at every index so far.
    live: bool,
    /// Set while the serial pass is the one running. A recorded-but-unarmed
    /// replay answers nothing.
    armed: bool,
    /// Worker clocks owed to item rows that have not closed yet. Charged at
    /// [`Replay::finish`], because a row is patched in place and only exists
    /// once its scope has closed. Empty unless `--timings` is collecting.
    folds: Vec<(String, String, u64, kstats::Snapshot)>,
}

impl Replay {
    /// The verdicts of a pass that is about to be discarded. `None` when there
    /// is nothing to reuse.
    ///
    /// The outcomes are the whole of one pass, from its first submission: the
    /// only join that can reach this is the pass's last, because the two
    /// mid-pass joins (`elab_module_pass`'s failed-item branch) return from
    /// the pass immediately after. Recording stops at the first gap or panic
    /// rather than guessing which index a later outcome belongs to.
    pub(crate) fn record(outcomes: &[Outcome]) -> Option<Replay> {
        let mut entries = Vec::new();
        for (at, outcome) in outcomes.iter().enumerate() {
            if outcome.index != at {
                break;
            }
            let verdict = match &outcome.verdict {
                Ok(()) => Ok(()),
                Err(Some(err)) => Err(*err),
                // A panic says nothing about the declaration; the replay
                // checks it, and everything after it, itself.
                Err(None) => break,
            };
            let item = outcome.item.as_ref();
            entries.push(Some(Recorded {
                psi_len: item.psi.bindings.len(),
                name: item.name.clone(),
                ctx: item.ctx.clone(),
                ty: item.ty.clone(),
                level: item.level.clone(),
                body: item.body.clone(),
                opaque: item.opaque,
                layer: item.layer,
                lands_in_psi: item.lands_in_psi,
                fuel: item.fuel,
                verdict,
                ns: outcome.ns,
                kernel: outcome.kernel,
                unsealed: outcome.unsealed.clone(),
            }));
        }
        (!entries.is_empty()).then_some(Replay {
            entries,
            at: 0,
            live: true,
            armed: false,
            folds: Vec::new(),
        })
    }

    fn arm(&mut self) {
        self.armed = true;
    }

    /// The verdict already earned for this obligation, if its inputs are the
    /// ones the worker was handed. `None` means "ask the kernel", which is
    /// always allowed and is what a single mismatch condemns the rest of the
    /// replay to.
    fn reuse(
        &mut self,
        psi_len: usize,
        fuel: u64,
        item: &crate::gate::GateItem<'_>,
    ) -> Option<Result<(), TypeError>> {
        if !self.armed || !self.live {
            return None;
        }
        let Some(entry) = self.entries.get(self.at).and_then(|e| e.as_ref()) else {
            self.stop();
            return None;
        };
        let same = entry.psi_len == psi_len
            && entry.fuel == fuel
            && entry.name == item.name
            && entry.opaque == item.opaque
            && entry.layer == item.layer
            && entry.lands_in_psi == item.lands_in_psi
            && &entry.ctx == item.ctx
            && &entry.ty == item.ty
            && &entry.level == item.level
            && &entry.body == item.body;
        if !same {
            self.stop();
            return None;
        }
        // Retire the entry here: its terms have served their one purpose, and
        // the replay is about to go on building the module's second copy of
        // everything after it.
        let entry = self.entries[self.at].take().expect("just matched");
        self.at += 1;
        // The kernel gate ran for this declaration — on a worker, in the pass
        // this one replaces — so the counter column says so at either width.
        crate::stats::count(crate::stats::Counter::DeclsGated);
        if let Some((module, item)) = crate::stats::current_item() {
            self.folds.push((module, item, entry.ns, entry.kernel));
        }
        // The worker's unsealings belong to this check as if it had just run
        // here, for whoever is recording on this thread.
        heather_kernel::unseal::observe(&entry.unsealed);
        Some(entry.verdict)
    }

    /// Reuse is over for this replay: nothing after a mismatch is answerable,
    /// so the rest of the list is dead weight and goes now.
    fn stop(&mut self) {
        self.live = false;
        self.entries = Vec::new();
    }

    /// Charge the reused verdicts' worker clocks to the rows they belong to
    /// and drop the list.
    ///
    /// The kernel *counters* are deliberately not merged again: the discarded
    /// pass's own join already merged every worker's delta into this thread
    /// (`stats::fold_deferred_kernel`), and the enclosing module and run rows
    /// were never rolled back. What is missing after the replay is only the
    /// per-declaration row, which `stats::truncate_rows` threw away with the
    /// pass and the replay has just re-created empty.
    fn finish(&mut self) {
        for (module, item, ns, kernel) in std::mem::take(&mut self.folds) {
            crate::stats::fold_reused_kernel(&(module, item), ns, &kernel);
        }
    }
}

/// The elaborator's slot for a [`Replay`]: interior-mutable, because the gate
/// sites consult it while holding a borrow of Ψ, and **never inherited**, for
/// the same reason a clone gets a fresh pool (a clone is a different module's
/// work, and a verdict is about one pass of one module).
#[derive(Default)]
pub(crate) struct ReplaySlot(std::cell::RefCell<Option<Replay>>);

impl ReplaySlot {
    /// Keep a discarded pass's verdicts for the replay that follows.
    pub(crate) fn record(&self, replay: Option<Replay>) {
        *self.0.borrow_mut() = replay;
    }

    /// Forget whatever is held, charging nothing.
    pub(crate) fn clear(&self) {
        *self.0.borrow_mut() = None;
    }

    /// The serial pass is starting: the recorded verdicts become answerable.
    pub(crate) fn arm(&self) {
        if let Some(replay) = self.0.borrow_mut().as_mut() {
            replay.arm();
        }
    }

    /// The serial pass is over: fold the attribution back and drop the list.
    pub(crate) fn finish(&self) {
        if let Some(mut replay) = self.0.borrow_mut().take() {
            replay.finish();
        }
    }

    /// [`Replay::reuse`], or `None` when nothing is armed.
    pub(crate) fn reuse(
        &self,
        psi_len: usize,
        fuel: u64,
        item: &crate::gate::GateItem<'_>,
    ) -> Option<Result<(), TypeError>> {
        self.0.borrow_mut().as_mut()?.reuse(psi_len, fuel, item)
    }
}

struct State {
    jobs: VecDeque<(usize, Rc<Deferred>)>,
    outcomes: Vec<Outcome>,
    outstanding: usize,
    shutdown: bool,
}

struct Shared {
    state: Mutex<State>,
    work: Condvar,
    done: Condvar,
    /// Set by whichever worker first records a rejection or a panic, and read
    /// without the lock by [`KernelPool::poll_failed`] between declarations.
    /// That poll is the early abort: once a queued proof has failed the pass
    /// is going to be discarded and re-run serially, so elaborating the rest
    /// of the module is work nobody will look at
    /// (`docs/kernel/parallel-kernel-gate-design.md` §5.1).
    failed: AtomicBool,
}

impl Shared {
    fn worker(self: &Arc<Self>) {
        loop {
            let job = {
                let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
                loop {
                    if state.shutdown {
                        return;
                    }
                    if let Some(job) = state.jobs.pop_front() {
                        break job;
                    }
                    state = self.work.wait(state).unwrap_or_else(|e| e.into_inner());
                }
            };
            let outcome = run(job.0, job.1);
            if outcome.verdict.is_err() {
                self.failed.store(true, Ordering::Relaxed);
            }
            let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
            state.outcomes.push(outcome);
            state.outstanding -= 1;
            if state.outstanding == 0 {
                self.done.notify_all();
            }
        }
    }
}

/// The pool, as the elaborator holds it.
pub(crate) struct KernelPool {
    workers: usize,
    shared: Option<Arc<Shared>>,
    handles: Vec<JoinHandle<()>>,
    next: usize,
}

impl Default for KernelPool {
    /// A fresh elaborator runs as wide as `HEATHER_KERNEL_WORKERS` says, or
    /// [`crate::DEFAULT_KERNEL_WORKERS`] wide: the deferral pipelines the
    /// elaborator against the workers and total CPU is flat with width
    /// (`docs/kernel/parallel-kernel-gate-design.md`), so there is no serial mode
    /// to protect by default. `HEATHER_KERNEL_WORKERS=1` is the serial
    /// build, for timing an item in isolation.
    fn default() -> Self {
        KernelPool::with_workers(crate::kernel_workers_from_env().unwrap_or(crate::DEFAULT_KERNEL_WORKERS))
    }
}

impl KernelPool {
    fn with_workers(workers: usize) -> Self {
        KernelPool { workers: workers.max(1), shared: None, handles: Vec::new(), next: 0 }
    }

    /// An inline pool with nothing queued: what a clone of an elaborator gets
    /// (`ModulePass`'s `Clone`), never a second handle on the same queue.
    ///
    /// Cloning an elaborator shares its committed world and nothing
    /// transient, so outstanding proof obligations stay with the original —
    /// that much is forced. Resetting the width to 1 as well is a judgment: a
    /// cloned elaborator is speculative or nested work (`relational_context`'s
    /// candidate search calls `environment.clone().elab_module_source(..)`
    /// once per candidate), and spawning and tearing down a pool per
    /// candidate would cost more than the handful of declarations inside one
    /// could possibly save. A driver that wants a clone to run wide says so
    /// with `set_kernel_workers`. `KernelPool` is deliberately not `Clone`, so
    /// this is the only way to get a second one from a first.
    pub(crate) fn inline() -> Self {
        KernelPool::with_workers(1)
    }

    /// Set the worker count. 1 is exactly the serial behaviour: no thread, no
    /// queue, the gate sites inline — which is also what the serial fallback
    /// (`docs/kernel/parallel-kernel-gate-design.md` §5.1) sets it to for the replay.
    /// Changing it with checks outstanding is a caller error; the elaborator
    /// sets it up front or between passes, both of which are quiescent.
    pub(crate) fn set_workers(&mut self, workers: usize) {
        debug_assert!(self.shared.is_none() || self.next == 0);
        self.workers = workers.max(1);
    }

    pub(crate) fn workers(&self) -> usize {
        self.workers
    }

    /// Set the width for an **inline** stretch in the middle of a pass and
    /// return the old one, leaving anything already queued where it is. At
    /// width 1 the gate sites run the kernel themselves and never touch the
    /// queue, so a caller that needs one verdict now — the meaning check,
    /// whose statement is gated and rolled back (`meaning.rs`) — narrows to 1,
    /// gates, and restores. Unlike [`Self::set_workers`], this is not a
    /// quiescent-only operation, because nothing it runs is queued.
    pub(crate) fn swap_width(&mut self, workers: usize) -> usize {
        std::mem::replace(&mut self.workers, workers.max(1))
    }

    /// Whether a gate site should run the kernel itself rather than queue.
    pub(crate) fn is_inline(&self) -> bool {
        self.workers <= 1
    }

    /// Queue one proof obligation.
    ///
    /// The pool **grows one worker per submission**, up to the configured
    /// width, so a run that queues nothing spawns nothing and a module with
    /// one proof obligation pays for one thread rather than for eight. A
    /// thread is not free — it carries the kernel's whole native stack,
    /// and the dev loop is full of one- and two-declaration probe modules —
    /// while a module wide enough to use eight workers reaches eight by its
    /// eighth declaration, before any of them could have been the bottleneck.
    pub(crate) fn submit(&mut self, item: Deferred) {
        let shared = match &self.shared {
            Some(shared) => Arc::clone(shared),
            None => {
                let shared = Arc::new(Shared {
                    state: Mutex::new(State {
                        jobs: VecDeque::new(),
                        outcomes: Vec::new(),
                        outstanding: 0,
                        shutdown: false,
                    }),
                    work: Condvar::new(),
                    done: Condvar::new(),
                    failed: AtomicBool::new(false),
                });
                self.shared = Some(Arc::clone(&shared));
                shared
            }
        };
        if self.handles.len() < self.workers {
            let n = self.handles.len();
            let mine = Arc::clone(&shared);
            // A thread the OS will not give us is not a reason to fail a
            // check: the workers already running (or, with none, this thread)
            // do the work. The stack is the one the kernel's depth budget was
            // sized for, not the 2 MiB default a spawned thread gets.
            if let Ok(handle) = std::thread::Builder::new()
                .name(format!("heather-kernel-{n}"))
                .stack_size(heather_kernel::reduce::NATIVE_STACK_BYTES)
                .spawn(move || mine.worker())
            {
                self.handles.push(handle);
            }
        }
        let index = self.next;
        self.next += 1;
        let item = Rc::new(item);
        if self.handles.is_empty() {
            let outcome = run(index, item);
            if outcome.verdict.is_err() {
                shared.failed.store(true, Ordering::Relaxed);
            }
            let mut state = shared.state.lock().unwrap_or_else(|e| e.into_inner());
            state.outcomes.push(outcome);
            return;
        }
        let mut state = shared.state.lock().unwrap_or_else(|e| e.into_inner());
        state.jobs.push_back((index, item));
        state.outstanding += 1;
        drop(state);
        shared.work.notify_one();
    }

    /// Whether some *already finished* check has failed. Non-blocking: one
    /// relaxed load, asked between declarations, and the only thing it is
    /// allowed to decide is whether to stop elaborating early — the verdict
    /// itself still comes from [`Self::join`].
    pub(crate) fn poll_failed(&self) -> bool {
        self.shared.as_ref().is_some_and(|s| s.failed.load(Ordering::Relaxed))
    }

    /// Wait for every outstanding check and take the outcomes, in submission
    /// order — which is declaration order, which is the order failures are
    /// reported in.
    pub(crate) fn join(&mut self) -> Vec<Outcome> {
        self.next = 0;
        let Some(shared) = &self.shared else { return Vec::new() };
        let mut state = shared.state.lock().unwrap_or_else(|e| e.into_inner());
        while state.outstanding > 0 {
            state = shared.done.wait(state).unwrap_or_else(|e| e.into_inner());
        }
        let mut outcomes = std::mem::take(&mut state.outcomes);
        drop(state);
        // Nothing is outstanding and the outcomes have left: the next pass
        // starts from no known failure.
        shared.failed.store(false, Ordering::Relaxed);
        outcomes.sort_by_key(|o| o.index);
        outcomes
    }
}

impl Drop for KernelPool {
    fn drop(&mut self) {
        let Some(shared) = self.shared.take() else { return };
        // A pool is quiescent and drained when it dies: every module path
        // joins before it returns, and the join takes the outcomes. Dropping
        // one that still holds a verdict means some caller replaced a *live*
        // pool, and the verdicts in it are the ones a module was about to be
        // judged by — silently discarded, gate silently inline afterwards.
        // That was a real defect (`restore_from_clone`), and it was invisible
        // except under load, so the next one gets caught here instead.
        #[cfg(debug_assertions)]
        if !std::thread::panicking() {
            let state = shared.state.lock().unwrap_or_else(|e| e.into_inner());
            debug_assert!(
                state.outstanding == 0 && state.outcomes.is_empty(),
                "kernel pool dropped with {} check(s) outstanding and {} verdict(s) unread",
                state.outstanding,
                state.outcomes.len(),
            );
        }
        {
            let mut state = shared.state.lock().unwrap_or_else(|e| e.into_inner());
            state.shutdown = true;
        }
        shared.work.notify_all();
        for handle in self.handles.drain(..) {
            let _ = handle.join();
        }
    }
}
