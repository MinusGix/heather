# The deferred kernel gate

Check independent declarations' proofs on a pool of kernel worker threads
while the elaborator continues serially, behind the existing `KernelGate`
seam (`crates/elab/src/gate.rs`), over `Arc` kernel terms.
Issue: `issues/parallel-kernel-gate.md`.

The workload this exists for is the native certificate: 3 474 generated
theorems, none over a second, all successful, 86 s of kernel in a 128 s build
(`issues/function-ir-x86-proof-scaling.md`, 2026-09-11). The dependency graph
is wide and shallow, and nothing in the kernel could check two of them at
once, because every `Term` child was an `Rc`.

## 1. `Arc` by alias

Every workspace file that said `use std::rc::Rc;` now says
`use std::sync::Arc as Rc;`, and the handful of inline `std::rc::Rc`
spellings became `std::sync::Arc`. No other change: `Arc` has `ptr_eq`,
`make_mut`, `get_mut`, `try_unwrap` and `strong_count` with the same
signatures, so the 2 800-odd kernel sites and the elaborator's ~63 files
compile unchanged.

The serial tax was measured first, as the control
(`issues/kernel-arena-terms-frozen-prefix.md`, 2026-09-11): 1.04x median over
87 bench cases, +2% at module scale, with the refcount-dense nat micro-steps
paying 1.20–1.28x. That is what buys the right to a worker pool now, rather
than waiting on the arena representation.

Renaming the alias to `Arc` throughout is a mechanical follow-up and is
deliberately not in this round: it would bury the diff.

## 2. The seam

The gate is already a single narrow surface. `gate.rs` documents exactly three
sites where a finished declaration faces `typing::check_type` +
`typing::check_term`:

| site | what it is | deferred? |
| --- | --- | --- |
| `Elaborator::elab_decl_inner` (lib.rs) | a user `fn`/`theorem`, pushed to Ψ | **yes** |
| `gendefs::push_gen_def` | a generated definition, pushed to Ψ | **yes** |
| `quote.rs::elab_meta_decl_inner` | a `meta fn`, registered in the meta-def table | no |

A `meta fn` stays synchronous on purpose: its body is *executed* by the
metaprogram interpreter later in the same module, and running a term that has
not yet been type-checked is a different risk from merely committing it to Ψ.
The certificate workload has no `meta fn` in its hot path.

At a deferred site the split is:

- `KernelGate::admits` is consulted **synchronously**, against the Ψ the item
  would be checked in. A hit skips everything, exactly as today.
- On a miss, `check_type` on the statement runs **synchronously**, on the
  elaborator's thread, inside the existing `stats::time_kernel` bracket.
  Dependents need the statement, and it is the cheap half.
- `check_term` on the proof/body is **queued**, together with everything it
  needs, and the binding is committed to Ψ immediately.
- `KernelGate::accepted` is deferred with it: a cache must not record a
  verdict for a proof that has not been checked yet.

## 3. The queued item

```rust
struct Deferred {
    name: String, span: Span,          // for the error, in declaration order
    psi: Rc<GlobalCtx>,                // the frozen prefix, O(1) snapshot
    ctx: LocalCtx, ty: Type, level: Level, body: Term,
    opaque: bool, layer: Layer, lands_in_psi: bool,   // to rebuild GateItem
    fuel: u64,
    row: Option<(String, String)>,     // the item scope to fold timings into
}
```

The Ψ snapshot is the whole point of the design being cheap. `GlobalBindings`
is already persistent — `Rc<Vec<GlobalChunk>>` plus a bounded `Rc<Vec<_>>`
tail plus an identity token (`crates/kernel/src/term.rs`) — so
`Rc<GlobalCtx>::clone` is one refcount bump and the snapshot is O(1), not a
copy of the bindings. The elaborator's next `push` pays at most one
copy-on-write of the ≤64-binding tail, which it already pays whenever a
semantic image holds a snapshot.

`Deferred` is moved into an `Arc<Deferred>` so that the worker can read it and
the main thread can still rebuild a borrowed `GateItem` from it at join time,
to hand to `KernelGate::accepted`. The gate itself never leaves the
elaborator's thread: it is an `Rc<dyn KernelGate>` and stays one.

## 4. Worker lifecycle

`--kernel-workers N` on `heather check`, `build-x86` and `compile-x86`, and
`HEATHER_KERNEL_WORKERS` in the environment; the flag wins.

**N = 1 is the default and spawns no thread.** The pool reports itself
inline, the gate sites run exactly the code they ran before, in the same
order, with the same error timing and the same `stats::time_kernel` bracket.
The test suite and its 4 GiB per-process rail are therefore unchanged until
someone moves the default. Two other conditions also force inline: the
`value-metrics` collector being enabled (its `ValueMetrics` is an `Rc` the
elaborator owns and the profiled checker entry points want), and a `meta fn`
gate.

A **cloned** elaborator gets an inline pool, not a second handle on the
original's queue and not a pool of its own. Outstanding obligations belonging
to the module the original is elaborating is forced; resetting the width is a
judgment, and the reason is `relational_context`'s candidate search, which
calls `environment.clone().elab_module_source(..)` once per candidate —
spawning and tearing down a pool per candidate would cost more than the
handful of declarations inside one could save. A driver that wants a clone to
run wide says so.

For N > 1 the pool is `std::thread` plus one `Mutex`/`Condvar` pair (the
kernel keeps zero dependencies, and the elaborator gains none): a job deque,
an outcome vector, an outstanding count. A worker loops — wait for work, pop,
check, push an outcome, notify — and exits on a shutdown flag set when the
`Elaborator` is dropped. Threads are spawned lazily on the first submission,
so a run that queues nothing spawns nothing.

Per-worker checker state is per-worker by construction: `Tc`, its `RefCell`
conversion memo, the `ValueArena`, `BodyCache` and the diagnostic stacks are
all created *inside* `typing::check_term` and die with the call. The
thread-locals — the bounds memo (`bounds.rs`), the budget cells (`fmt.rs`),
the `checks.rs` sampling counter, and both stats registries — are per-thread
by definition. Nothing is shared but the frozen prefix and the item, both
behind `Arc`, both read-only.

## 5. The join, and every point it must precede

`Elaborator::join_kernel_gate()` drains the pool and returns the first
failure in declaration order. It is called at the end of **both** module
paths, before either returns:

- `elab_module_source` — the `?`-returning path used by `elab_source`,
  `with_prelude`, the generated-source entry points, and `build-x86` /
  `compile-x86` for the certificate module;
- `check_module_source_inner` — the error-collecting path, which is what
  `check_module_delta` runs inside and therefore what the semantic session,
  the module image and the declaration cache sit behind.

Putting the join at the end of the two module bodies, rather than at each
consumer, is what makes the "could the join be missed?" question answerable
by reading two functions. Everything downstream is strictly after:

| consumer | why it is covered |
| --- | --- |
| `SemanticSession::check` publishing an image | runs `check_module_delta` → `check_module_source_inner`; the extension is read from Ψ *after* the join, and an error short-circuits before publication |
| `Cache::accepted` recording a verdict | `accepted` is itself deferred and replayed at the join, in declaration order, only for items before the first failure |
| `build-x86` / `compile-x86` writing the ELF, the `.s` and the `.certificate.hthr` | every `write_new` is after `elab.elab_module_source(...)` has returned `Ok` |
| `heather check` reporting a module accepted | the errors vector it reads is the one the join appended to |
| `replay_module_delta` | replays a *stored* delta; it queues nothing |

The failure rule: any queued check failing fails the module. Outcomes are
sorted by submission index, which is declaration order, and the first failing
one is reported. A worker panic is caught (`catch_unwind`) and becomes an
ordinary module failure naming the item — never a hang, never a poisoned
mutex taking the process with it.

What a committed-but-unchecked binding can do to the *rest* of the module,
between its commit and the join, is bounded but not nothing: a `fn`'s body is
visible to dependents, so conversion can δ-unfold a term the kernel has not
yet accepted. It cannot produce a wrong verdict — the module fails either way
— but it can make a later check spend its fuel on nonsense. Fuel is what
bounds it; the module's answer is unchanged; and a `theorem`, which is the
whole of the certificate workload, is pushed opaque and so is invisible to
every dependent in the first place.

Two things about the **declaration cache** as a consumer of the seam
(`crates/cache/src/lib.rs`), both consequences of the deferral rather than
choices:

- *The prefix rule is a soundness rule, not a tidiness one.* The serial gate
  never pushes a failed declaration to Ψ, so nothing is ever proved against a
  bogus binding. The deferred gate does push it — that is the deferral — so a
  later declaration in the same module may have been checked against an
  unverified body. Vouching for it would record a cache entry that the kernel
  did not earn. Hence: verdicts for the prefix before the first failure,
  nothing after it. A failing module therefore records *fewer* entries under
  N > 1 than under N = 1, which is the conservative direction.
- *The verdict is replayed against the item's own Ψ snapshot*, in declaration
  order, which is what `Inner::sync` needs to extend its Merkle prefix
  incrementally. The one cost is that the first replayed verdict of a module
  arrives with a Ψ *shorter* than the prefix the intervening `admits` calls
  grew, and `sync` answers a shrinking Ψ by clearing and rehashing — so
  `--cache` together with `--kernel-workers N > 1` pays one full prefix
  rehash per module. Correct, and measurable, and not a combination anything
  runs today (the default is 1, and the native commands do not install a
  declaration gate at all). The proper fix is a third seam method that
  computes an item's identity synchronously at submission and commits the
  verdict at the join; that is its own round.

One behavioural difference under N > 1, recorded deliberately: a deferred
failure loses the `kernel_error` notes (`refused_decide`, the pending
mismatch and refl notes), because those are per-declaration elaborator state
that has moved on by join time. The error, its item and its span are exact;
the hint is not reconstructed. Under the default N = 1 nothing changes.

## 6. What had to be `Send`

`Term`, `Type`, `Level`, `LocalCtx`, `GlobalCtx`, `GlobalBinding` and
`TypeError` are plain trees of `Rc` and `String` with no interior mutability
— `crates/kernel/src/term.rs` has no `Cell` or `RefCell` at all — so the
alias alone makes them `Send + Sync`. `crates/elab/src/pool.rs` asserts this
statically, so a future field that breaks it is a compile error and not a
mystery.

What is *not* `Send`, and therefore stays on the elaborator's thread: the
`Rc<dyn KernelGate>`, the `ValueMetrics` collector, and the `Elaborator`
itself. The pool holds none of them.

## 7. Attribution fold-back

The stats registry (`crates/elab/src/stats.rs`) and the kernel's counters
(`crates/kernel/src/stats.rs`) are thread-local, and that stays true: a
worker measures itself. The worker records the elapsed nanoseconds of its
`check_term` and the delta of `heather_kernel::stats::snapshot()` across it,
and returns both with the outcome. At join time, on the elaborator's thread:

1. `kstats::merge` adds the worker's counter delta to the main thread's
   counters, so every *still-open* enclosing scope — the module row, the run
   row — picks it up the way it always did;
2. `stats::add_deferred_kernel` adds the nanoseconds to the `KernelGate`
   timer cell (without touching the exclusive-nesting accumulator, which
   belongs to whatever bracket is open) for the same reason; and
3. the already-closed **item** row named by `Deferred::row` is patched in
   place: `kernel_gate_ns`, `kernel_ns`, `total_ns` and the kernel counter
   columns all gain the worker's numbers.

`Deferred::row` is the innermost `ScopeKind::Item` scope open at submission
time, tracked by a thread-local stack that `stats::scope` maintains only when
collection is on. That is what charges a generated definition to the
declaration that minted it, which is where the exclusive-timer rule charged
it before.

`decls_gated` is counted at submission, on the elaborator's thread, so the
counter column is unchanged. The net effect: `--timings` has the same shape
as today — `kernel_gate_ns` per item — and the per-module and per-run totals
still sum. The one honest difference is that under N > 1 a module row's
`kernel_gate_ns` can exceed its `total_ns` wall, because it is CPU across
workers; that is the speedup, visible.

## 8. Trusted base

The kernel gains no new judgement and no new rule. `check_term` is the same
function, called with the same arguments, on a different thread, against a Ψ
that is immutable for the duration of the call. What the trusted-base
argument now additionally rests on is that `Term` and `GlobalCtx` are
immutable once built and reachable only behind `Arc`, so two threads reading
the same subtree observe the same tree; the only mutation of Ψ is an append
on the elaborator's thread to a *copy* the worker does not share.

Two counters and one merge were added to `crates/kernel/src/stats.rs`
(`Snapshot::plus`, `merge`), which remain inert by the module's own rule:
nothing in the kernel reads them.

`crates/kernel/DESIGN.md` carries this paragraph.

## 9. Measurement protocol

Release binary, warm image cache, one furnace instance, nothing else running:

```
cargo build --release --bin heather                    # outside any ulimit
for W in 1 2 4 8; do
  ( ulimit -v 16777216 -t 900
    /usr/bin/time -f "W=$W wall=%es rss=%MKB user=%Us" \
      target/release/heather build-x86 \
        examples/x86-native/reused_callee.hthr caller --callee leaf \
        --arg 21 --arg 1 -o /tmp/pk$W.elf \
        --cache-dir target/native-test-images \
        --kernel-workers $W --timings /tmp/pk$W.tsv )
done
```

Reported per W: wall, user CPU, peak RSS, and the summed `kernel_gate_ns`
over the `*_native_certificate` item rows. The **first** run after a new
binary rebuilds the 28 library images from source (~94 s), because the image
cache keys on the compiler binary; W = 1 is therefore run twice and the first
discarded, so every reported number is warm.

Linear to 8 means contention is a non-issue. Flat past 2 means the
frozen-prefix borrow discipline, or the arena representation
(`issues/kernel-arena-terms-frozen-prefix.md`), comes first.

**What it found** (numbers in the issue's log, not here): contention is a
non-issue — total CPU and summed `kernel_gate` are flat across every width,
so the atomics cost nothing beyond the serial tax the control already
measured. What the curve flattens against instead is Amdahl's other half:
the certificate's wall falls steeply from one worker to two, gains a little
at four, and stops, because by then the **elaborator's own serial time** —
the unattributed `other` bucket that
`issues/perf-instrumentation-consolidation.md` owes timers for — is the
whole of the remaining wall. Peak RSS grows roughly with the width, one
value arena per worker in flight. The next lever on this workload is
naming and shrinking the serial elaborator, or
`issues/parallel-checking-and-caching.md`'s cross-process split; it is not
more kernel workers.

One trap the first measurement fell into, now impossible: `--timings` also
turned on the value-machine collector, which pins the gate to the
elaborator's thread — so every width produced *identical* numbers, the
serial gate wearing the parallel flag. The commands now say which of the two
won rather than silently honouring neither.

`scripts/bench --check` against a same-box `Rc` baseline confirms the serial
tax stayed where the control put it; the four nat families
(`nat/step-once`, `nat/step-into-closed-body`, `nat/add-normalize`,
`nat/mul-normalize`) are reported explicitly, because they are what the
clone/drop audit is supposed to move.
