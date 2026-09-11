//! The deferred kernel gate: a pool of kernel worker threads
//! (`docs/parallel-kernel-gate-design.md`, `issues/parallel-kernel-gate.md`).
//!
//! The elaborator checks a declaration's *statement* synchronously — dependents
//! need it — commits the binding to Ψ, and queues the proof/body's
//! `typing::check_term` here with the Ψ prefix it must be checked against. The
//! module joins every outstanding check before it is accepted, published, or
//! emitted; any failure fails the module, reported in declaration order.
//!
//! Nothing is shared with a worker but the frozen prefix and the item, both
//! immutable and both behind `Arc`. Every piece of checker state — `Tc`, its
//! conversion memo, the value arena, `BodyCache`, the bounds memo, the budget
//! cells, both stats registries — is per-thread by construction, because it is
//! either created inside `check_term` or declared `thread_local!`.
//!
//! `workers == 1` is the default and spawns nothing: the gate sites run the
//! code they always ran, in the order they always ran it. The pool exists in
//! that configuration only to answer `is_inline()`.

use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::stats as kstats;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::typing::{self, TypeError};
use heather_syntax::Span;

use std::sync::Arc as Rc;

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
    /// The declaration scope open when this was queued — the row its timings
    /// fold back into (`docs/parallel-kernel-gate-design.md` §7). `None` when
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
}

fn run(index: usize, item: Rc<Deferred>) -> Outcome {
    let before = kstats::snapshot();
    let started = std::time::Instant::now();
    // A panic in a worker must not poison the queue or wedge the join. It is
    // reported as this item failing, which is what a panic on the elaborator's
    // own thread would have amounted to.
    let verdict = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| item.check())) {
        Ok(Ok(())) => Ok(()),
        Ok(Err(e)) => Err(Some(e)),
        Err(_) => Err(None),
    };
    let ns = started.elapsed().as_nanos() as u64;
    Outcome { index, item, verdict, ns, kernel: kstats::snapshot().since(&before) }
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
    fn default() -> Self {
        KernelPool { workers: 1, shared: None, handles: Vec::new(), next: 0 }
    }
}

/// A clone is an **inline** pool, never a second handle on the same queue.
///
/// Cloning an elaborator shares its committed world and nothing transient, so
/// outstanding proof obligations stay with the original — that much is forced.
/// Resetting the width to 1 as well is a judgment: a cloned elaborator is
/// speculative or nested work (`relational_context`'s candidate search calls
/// `environment.clone().elab_module_source(..)` once per candidate), and
/// spawning and tearing down a pool per candidate would cost more than the
/// handful of declarations inside one could possibly save. A driver that wants
/// a clone to run wide says so with `set_kernel_workers`.
impl Clone for KernelPool {
    fn clone(&self) -> Self {
        KernelPool::default()
    }
}

impl KernelPool {
    /// Set the worker count. 1 (the default) is exactly today's serial
    /// behaviour: no thread, no queue, the gate sites inline. Changing it with
    /// checks outstanding is a caller error; the elaborator only sets it up
    /// front.
    pub(crate) fn set_workers(&mut self, workers: usize) {
        debug_assert!(self.shared.is_none() || self.next == 0);
        self.workers = workers.max(1);
    }

    pub(crate) fn workers(&self) -> usize {
        self.workers
    }

    /// Whether a gate site should run the kernel itself rather than queue.
    pub(crate) fn is_inline(&self) -> bool {
        self.workers <= 1
    }

    /// Queue one proof obligation. Threads are spawned on the first
    /// submission, so a run that queues nothing spawns nothing.
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
                });
                for n in 0..self.workers {
                    let mine = Arc::clone(&shared);
                    let handle = std::thread::Builder::new()
                        .name(format!("heather-kernel-{n}"))
                        .spawn(move || mine.worker());
                    match handle {
                        Ok(handle) => self.handles.push(handle),
                        // A thread the OS will not give us is not a reason to
                        // fail a check: the remaining workers (or, with none,
                        // the join's own thread) do the work.
                        Err(_) => break,
                    }
                }
                self.shared = Some(Arc::clone(&shared));
                shared
            }
        };
        let index = self.next;
        self.next += 1;
        let item = Rc::new(item);
        if self.handles.is_empty() {
            let mut state = shared.state.lock().unwrap_or_else(|e| e.into_inner());
            state.outcomes.push(run(index, item));
            return;
        }
        let mut state = shared.state.lock().unwrap_or_else(|e| e.into_inner());
        state.jobs.push_back((index, item));
        state.outstanding += 1;
        drop(state);
        shared.work.notify_one();
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
        outcomes.sort_by_key(|o| o.index);
        outcomes
    }
}

impl Drop for KernelPool {
    fn drop(&mut self) {
        let Some(shared) = self.shared.take() else { return };
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
