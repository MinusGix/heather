# Implicit state machines in the kernel — second pass

Review of 2026-11-08 over master `5df757c`, kernel crate only
(`crates/kernel/src`). The first survey (`docs/implicit-state-machines-survey.md`,
2026-11-02) covered the kernel and the elaborator together and found three
kernel items (§3 the Ψ-bound `GlobalCache`, §6 the checker's mode, §9's
latches). This pass reads the kernel alone, at the depth the first one gave
the elaborator. It asks the same question: where is a phase, a mode or a
validity condition carried by flags, `Option`s, counters, the order of calls
or a doc comment, where a type could carry it instead?

The kernel is the trusted base, so the bar differs from the elaborator's. An
implicit invariant there whose breach makes the kernel *accept* more is a
soundness risk and ranks above everything else. One whose breach makes it
*refuse* a convertible pair, or answer differently depending on what it was
asked before, is a completeness or determinism risk. Breaches that only cost
time come last.

## Ranking

| # | Finding | Where | Evidence it bites | Breach costs | Make explicit? | Issue |
|---|---------|-------|-------------------|--------------|----------------|-------|
| 1 | The value memo does not record the mode a value was forced in | `value.rs` `ValueArena`, `eval.rs` `Eval::transparent` | **a real defect** (#459: a convertible interval verdict refused) | completeness, history dependence | the #459 path fixed (§1: withheld-call closedness); (a) still worth doing | [[value-memo-evaluation-mode]] |
| 2 | Deferred-premise queues: two hand-kept copies of one discipline | `conv.rs` `Conv` (8 fields), `typing.rs` `Tc` (4 fields) | **two defects while it was built** (deep-term-walks §3.3, §3.4) | soundness (a provisional memo entry kept) | **done** (§2, `premises.rs`) | [[kernel-premise-queue-type]] |
| 3 | Typing memo keys copy `Env`'s fields by hand | `typing.rs` `Scope`, `TyScope`, `SigScope` | none found | soundness (a stale memo hit) | **done** (§3, `Ambient`) | [[typing-memo-scope-key]] |
| 4 | Ψ-bound `GlobalCache`, plus `Defs`' layer condition | `reduce.rs` `Defs`, `GlobalCache` | none found | soundness | yes (already filed) | [[kernel-psi-bound-cache]] |
| 5 | The checker's mode | `typing.rs` `Tc` | none found | wrong mode's shortcut | yes, modest (already filed) | [[kernel-checker-mode-enum]] |
| 6 | Observation recordings: one guarded, one not | `unseal.rs`, `withheld.rs` | none yet (the second has no reader) | stale incremental cache | **done** (§6, `recording.rs`) | [[kernel-observation-recording-guard]] |
| 7 | `Debug`'s budget state in three thread-locals | `fmt.rs` `REMAINING`/`DEPTH`/`EXACT` | **a latent panic, reproduced** (§7) | the `{:?}`-is-safe rail | **done** (§7, `FmtState`) | [[fmt-budget-state-nesting]] |
| 8 | Seven hand-paired native-depth counters | see §8 | none | time only | no | — |
| 9 | Smaller ones | see §9 | none | — | no | — |
| 10 | Already explicit | see §10 | — | — | — | — |

Ranking weighs: a defect already happened > soundness > completeness and
determinism > number of hand-kept sites > size of the change. Every proposal
below is a kernel change on a hot path, so each issue asks for
`scripts/bench --check` and, where it moves a counter, `scripts/perf ab`.

## 1. The value memo does not record the mode a value was forced in

**Where.** `ValueArena` (`value.rs` ~295) memoizes forced closures by address
(`term_cache`), closed closures by body identity (`closed_values`,
`ValueArena::memo_closed`), and several per-closure classifications
(`fold_classes`, `transducers`, `bit_types`). `Eval` (`eval.rs` ~255) carries
the mode the forcing happens in: `transparent: bool` (~279), set by
`delta_whnf`, `delta_whnf_ty` and `delta_step_transparent` (~664–780) for the
duration of a δ-transparent request, plus the `Defs` it was built with.

**The state.** Under `transparent`, an eliminator stuck on a glued scrutinee
unfolds the scrutinee and retries (`eval.rs` ~2143). Without it, the
eliminator stays stuck. A thunk's weak-head value therefore depends on the
mode it was first forced in. The memo is keyed by the closure alone, so the
first force decides what every later reader sees, whatever *its* mode. The
validity condition, "this memo entry was made in a mode at least as
transparent as the reader's", lives nowhere.

**What went wrong.** #459 (`a9cb55b`, "Kernel meet: look ahead on a copy,
transparently"). `meet_on_the_way` stepped a side opaquely, which forced
memoized glued unfoldings to opaque results. The transparent run that
followed read them, could not step the stuck eliminator inside, and
conversion answered `NotConvertible` on a convertible interval verdict. The
fix added `Eval::delta_step_transparent` for that one look-ahead. Its doc
comment states the rule: a step whose result a transparent run will read
must itself be transparent. The other opaque δ-steps (`Dom::delta_tm` and
`delta_ty` at `conv/dom/values.rs` ~727, ~750, used at `conv.rs` ~1237 and
~1730–1793) are safe today only because no transparent run reads their
thunks first. Nothing checks that.

**The same shape for `Defs`.** The arena's classifications are documented
as depending "on nothing but the closure and the definitions, both fixed for
one arena" (`value.rs` ~300, ~316). `Eval::new(fuel, defs, base, &arena)`
takes the two separately. Conversion builds a fresh `Eval` per step over one
arena (`conv/dom/values.rs` `run`, ~523), and the elaborator builds several
(`crates/elab/src/host.rs` ~112, `sealing.rs` ~159). The real invariant is
weaker than "fixed": Ψ only *extends* within one arena (a telescope push),
and a closure only reads globals of the Ψ it was built in. That holds
because every caller follows it, not because the types say so.

**Why it ranks first.** It is the only finding here with a defect on master
in the last week. The breach is completeness rather than soundness: a value
forced transparently is δ-equal to the opaque one, so a mismatch in the
other direction only does extra work. But a verdict that depends on the
order of earlier queries is also a determinism hole, and the verdict caches
assume determinism (`issues/elaboration-determinism.md`).

**Make explicit?** Yes. Three options, cheapest first:

- (a) **Bind the arena to its Defs.** `ValueArena::new(defs)` and `Eval::new(fuel,
  base, &arena)`, so a mismatched pair cannot be built. The extension case
  becomes an `arena.extend(defs')` that asserts the new Ψ extends the old.
  Mechanical, and it fixes only the `Defs` half.
- (b) **Record the mode per memo entry.** Store a mode bit beside each
  `term_cache`/`closed_values` value. A transparent reader treats an opaque
  entry as a miss (or resumes it with one transparent step). It costs one
  bit per entry and a branch per hit, on the kernel's hottest lookup.
- (c) **Make forcing an unfolding mode-independent.** Always force `n.unfold`
  thunks transparently, so the memoized value of a glued unfolding is the
  same whoever asks first. This removes the condition instead of tracking it.
  It changes what the δ-lazy stage sees, so it needs the conversion
  benchmarks and the library gate. That stage's opaque spines are what make
  the rendezvous cheap (`eval.rs` `step_elim` notes).

(a) is worth doing anyway. Between (b) and (c), measure (c) first: it
deletes the hazard, where (b) only manages it.

**First attempt (2026-11-08): not landed.** The patches are kept in
`/mnt/project-files/value-memo-unfolding/`.

- **Reproduced.** Reverting #459's transparent look-ahead
  (`delta_tm_ahead` back to `delta_step`) makes five theorems of
  `lib/_tests/std/tactic/interval_tactic_tests.hthr` refuse with
  `NotConvertible`.
- **(b) as rejection.** `Eval` carries `Unfolding { Opaque, Lazy, Transparent }`
  in place of its bool, and the force, closed-value and type memos keep it
  beside each value; a reader takes only values forced at its level or
  above. This fixes those five under the lazy look-ahead, and costs under
  1% of evaluation steps on `calc_parser`, provided the shared-application
  memo is left untagged (tagged, it cost +68% steps and +88% memory).
  Keying strictly by mode cost +18% steps.
- **But the library gate refuses two modules with `OutOfFuel`**
  (`creal_tests::half_terms`, `rt_lower_tests::spread_agrees`). A
  transparent reader that re-evaluates a lazily forced closure builds fresh
  closures for everything below it, so the sharing the lazy run built is
  lost and fuel runs out.
- **(b) as resumption.** A transparent reader takes a lazy value unless it
  is a glued neutral with a non-application elimination in its spine, and
  resumes that one from its own unfolding. This keeps both modules passing,
  but does *not* fix the five refusals.
- **Why not.** Instrumenting the rejecting variant shows the differing
  values are exactly such stuck spines, so the gap is in values that reach
  a transparent run without passing through the memo. A value the
  evaluator wraps as `TmClo::Val` (`Eval::vclo`, 58 sites, many of them in
  conversion) carries no level. Conversion itself hands lazily forced `wa`
  and `wb` to its transparent stage. So "the mode a value was forced at" is
  a property of values, not of memo entries.

**Second attempt (2026-11-08): the exact path, fixed narrowly.** A
differential run found it: each transparent `delta_whnf` was re-run with
lazily forced memo entries refused, and the first result that changed was
logged. The value in both runs was a call of a **withheld** (`interface fn`)
global left unglued (`u ·app ·app ·app ·case …`), so the transparent run had
nothing to unfold.

- **The state.** A withheld call is glued once its arguments are closed
  (`eval/withheld.rs`), and closedness is decided by *forcing* each
  argument and walking its parts. A δ-lazy force of a closed argument such
  as `pred(two)` stops at an eliminator stuck on a glued scrutinee, a
  neutral the walk does not open. So it answers "open", and the call stays
  withheld. That verdict is not a memo entry the reader could check: it
  is built into the call's value (glued or unglued), and the memo hands
  that value to every later reader. A transparent run that reads it has no
  unfolding to take.
- **The fix** (`Eval::closed`). The walk forces δ-transparently whatever
  the run's mode. It also goes into the unfolding of a glued neutral whose
  spine has a non-application eliminator, because the memo can still hand
  it a value a lazy run forced first. Each half is needed: the regression
  test `a_withheld_call_at_a_lazily_stuck_closed_argument_is_glued`
  (`crates/kernel/tests/eval_differential.rs`) fails without either. With
  both, the five interval verdicts pass even under the lazy look-ahead.
- **#459's transparent look-ahead stays.** With the fix and the lazy
  look-ahead, `rt_lower_tests::spread_agrees` runs out of fuel. That is a
  cost, not a refusal: the look-ahead and the run that follows then force
  the same unfoldings twice. `delta_step_transparent`'s comment now gives
  that reason, not correctness.

What remains: the memo is still mode-blind in general (a lazily forced
value read by a transparent run is resumed by the spine replay, which is
correct but repeats work), and option (a), binding the arena to its `Defs`,
is still worth doing. Neither is a known defect now. Giving values a level
byte (`Val`/`TmClo::Val`) would close the general case and is the route if
another mode-dependent verdict turns up.

## 2. Deferred-premise queues: two hand-kept copies of one discipline

**Where.** `Conv` (`conv.rs` ~840–910) and `Tc` (`typing.rs` ~1118–1137),
implementing `docs/deep-term-walks-design.md` §3.3–3.4: a premise met
`SPINE_ITERATE_AT` frames deep is queued, not descended into, and is judged
before any verdict leaves.

**The state in `Conv`.** Eight fields cooperate: `depth`, `deferred`,
`deferred_pushed` (an epoch counter), `provisional` (a log of memo keys),
`attempts_open`, `defer_base`, `draining_at_top`, `defer_floor`, and they
are read together with `memo`. The phases the code walks are:

```
Walking ─(depth ≥ base+128, or queue past floor)─► Queuing (every later premise in this context queued)
Queuing ─(back at depth 0, Ok)─► DrainingAtTop ─(each popped item: floor := len)─► … ─► Settled
         ─(back at depth 0, Err)─► Dropped (queue cleared, all provisional memo entries taken back)
Any ─delta_lazy─► Attempt{mark, provisional mark, floor := mark} ─(Ok: drain to mark at own base)─►
         ─(Err: truncate to mark, take back provisional since mark)─►
```

And the memo itself has three states per key, `Final(true)`, `Final(false)`
and `Provisional(true)`, held as a `bool` in `memo` plus membership in
`provisional`.

**The state in `Tc`.** A simpler copy: `check_depth`, `deferred`,
`deferred_pushed`, `defer_floor`. There are no δ-attempts, so there is no
provisional log. Instead, a refused root that queued anything clears all
three memos wholesale (`Tc::forget_after_refusal`, ~2717). The two copies
follow the same rules on order and settling, but take memo entries back
differently.

**Invariants.** No verdict leaves with a queued premise. A memo `true` made
while anything is queued is provisional until its queue settles. A failed
attempt's premises are never judged. Only one drain runs at depth zero.
The threshold counts from the depth the queue is drained at.

**What went wrong.** Both while it was built, both caught by the library gate
(`docs/deep-term-walks-design.md`). (1) Queuing only the deep premise and
going on with its siblings changed the *order* of a conjunction, which
turned an expected `NotConvertible` in `rt_loop_tests` into `OutOfFuel`.
`defer_floor` was the fix. (2) Counting the threshold from zero inside a
δ-attempt's drain queued every popped comparison straight back until the fuel
ran out (`x86_64_block`). `defer_base` was the fix. Each fix added a field,
and each new field is read at several sites (`tm`, `ty`, `tm_nat_tail`,
`settle_at_top`, `drain_deferred`, `delta_lazy`, `memo_true`).

**Why it is soundness-relevant.** If a provisional `true` survived its queue
being dropped, conversion would answer yes on a premise nobody judged. Today
that is prevented by `take_back_provisional` at two sites and the
`attempts_open == 0` test in `settle_at_top`. A third kind of speculation
added later must remember both.

**Make explicit?** Yes. One `PremiseQueue<Item, Key>` type owning the
queue, floor, base, epoch, provisional log and attempt count, with a small
API that makes the phases calls rather than field writes:
`should_defer(depth)`, `defer(item)`, `context(|q| …)` for a root or popped
item, `attempt(|q| …)` for speculation (mark, drain, truncate, take back),
and `settle(result)`. The memo's three states move into it (or into a
`MemoEntry` enum it owns), so "provisional" is a value, not a list
membership. `Tc` uses the same type. Whether `Tc` should take back
provisional entries rather than clear everything is then one decision in one
place. Risk: this is `Conv::tm`'s prologue and epilogue, the kernel's
hottest path. The type must compile down to today's field reads.
`scripts/perf ab` should show identical counters and no time delta beyond
noise.

**Done (2026-11-09).** `crates/kernel/src/premises.rs` holds the
discipline once: `PremiseQueue<I>` owns the queue, floor, base, push count
and the depth-zero drain flag, and its phases are calls (`should_defer`,
`past_floor`, `defer`, `begin_drain`/`pop`/`judged`/`end_drain`,
`open_attempt`/`close_attempt`). `VerdictMemo<K>` owns conversion's memo
with its provisional log and open-attempt count (`succeeded`, `refused`,
`open_attempt`/`close_attempt`, `settle_at_top`), so a provisional `true`
is taken back by the type, not by remembering two call sites. `Conv` keeps
`depth` and the two values; `Tc` keeps `check_depth` and a
`RefCell<PremiseQueue>`, and still forgets its memos wholesale after a
refusal (that choice is now visible in one place, the module docs). The
`Drain` and `Attempt` records are `#[must_use]`, so a phase opened and not
closed is a warning. `scripts/perf ab` on `calc_parser`: conversion and
checking counters identical (`local_subst_nodes` +0.1%).

## 3. Typing memo keys copy `Env`'s fields by hand

**Where.** `typing.rs` `Env` (~973) and the three memo keys built from it:
`Scope` (~1343), `TyScope` (~1379), `SigScope` (~1406). Each `*::of`
copies `psi` (as `bindings.identity_addr()`), `gamma_base`, `univs`,
`layer` and `under_box` out of the `Env`. `Scope` adds Γ's identity or a
strengthened telescope id.

**The invariant.** A memo hit is sound only if the key holds *every* part of
the scope a rule reads. Today the rules read `psi`, `gamma`, `layer`,
`univs` and `under_box`, and all three keys have them. The next mode bit
added to `Env` for a rule must be added to three key structs and three
constructors, or the memo answers across it. `under_box` shows the shape: a
side condition read by one rule (`checked_spelling_admitted`), and therefore
a key component in all three memos.

Ψ is keyed by `bindings` identity alone. `GlobalCtx` also carries `sealed`
and `withheld` (`term.rs` ~1836), which change what δ does. The keys are
sound because a `Tc` lives for one gate over one Ψ, so both are fixed for
the memo's lifetime. That is a second unstated invariant. The verdict cache
in `crates/cache` mixes `withheld` into its key explicitly. The in-gate memo
relies on the checker's lifetime instead.

**Make explicit?** Yes, cheaply. Split `Env` into the part a key must see,
a `Copy` `JudgmentScope { psi_id, gamma_id, gamma_base, univs, layer, under_box }`,
and the rest (`cache`, metrics). Build the three keys from that sub-struct, so
a field added to it is in every key by construction. Assert once, at `Tc`'s
entry points, that `sealed`/`withheld` match the gate's Ψ for every `Env` the
checker builds (a `debug_assert!` on identity). No behaviour change.

**Done (2026-11-09).** `typing.rs` `Ambient { psi, gamma_base, univs,
layer, under_box }` is the key part all three hold, built only by
`Env::ambient`, whose pattern names every `Env` field without `..`: a field
added to `Env` does not compile until it is keyed there or excused with a
reason (`cache` is, since it is fixed by Ψ). `Env` itself was not split,
which would have touched every scope constructor for the same guarantee.
The Ψ question was settled by reading, not by an assert: `withholding`
already gives the bindings a fresh identity, and `seal_kept` does not but
need not, because a sealed proof only adds δ-steps, so a judgment made
before it still holds after. `Ambient`'s doc states both. Conversion's two
verdict buckets (`ConvMemoBucket`, `ClosedConvBucket`) keep their own
fields: they key a conversion, which never reads `under_box`, the one
component `Ambient` has that they lack.

## 4. Ψ-bound `GlobalCache` (filed; unchanged) and `Defs`' layer condition

The first survey's §3 stands as written. Seventeen `GlobalCache::new()`
pairings in `typing.rs` and two in `conv.rs` still pair the cache with its Ψ
by hand. [[kernel-psi-bound-cache]] is open.

One addition. `Defs` has a second doc-comment invariant beside "the cache
must belong to this exact `psi`" (`reduce.rs` ~198): `Defs::transparent` is
"only sound at a computing layer" (~192). Conversion enforces it at one
place (`Conv::defs`, `conv.rs` ~945). The typing path calls
`transparent_cached` at `typeof(i)`, which is always computing. But both
constructors are `pub`, and the elaborator calls them. A `ScopedGlobals` as
the issue proposes could also be the only way to get a transparent `Defs`,
taking the layer: `scope.defs(layer)` returns opaque at layer c. Logged on
the issue.

## 5. The checker's mode (filed; unchanged)

[[kernel-checker-mode-enum]] stands. Line numbers moved (`Tc` is now at
~1080; the mode tests at ~2146–2176, ~2260, ~2408, ~2728–2777, ~3039–3062,
~3221–3446), but the four modes and the sixteen combinations are as surveyed.
One interaction worth naming in that enum: Locate (`refused: Some`) bypasses
the typing memo by routing every check through `tm_check_noting`. That is
one reason a Locate checker can share §2's queue without the memo
take-back question arising. With `TcMode`, that becomes `mode.memo_allowed()`
rather than a field test placed before the memo test.

## 6. Observation recordings: one guarded, one not

**Where.** `unseal.rs` and `withheld.rs`, two thread-local stacks of
index sets that record which sealed proofs, or which withheld definitions,
a judgment opened. Their purpose is a protocol with the caches: a caller
that reuses a judgment must key it on what the recording saw.

**The state.** `unseal` has a guard (`Recording`, ~37). Dropping it
unfinished, as a panic unwinding through the span does, closes its frame,
and `close` pops any frames left open inside it. `withheld::record` (~29) is
the same idea written as a bare push, call, pop. A panic inside `f` that
is caught further out leaves its frame on the stack. The outer recording
then pops the inner's frame as its own and loses what it saw. The elaborator
catches panics in exactly one place, the kernel pool's workers (`pool.rs`
~119), and wraps them in `unseal::record` only.

**Evidence.** None yet, because `withheld::record` has no caller: the gluing
is noted but nobody reads it. Its first reader is
[[interface-body-early-cutoff]], which will key early cutoff on it. Then a
lost frame means a client is replayed over a withheld body it did observe.

**Make explicit?** Yes, before that issue lands: one
`Observation { unsealed, glued }` frame type with `unseal`'s guard, or
`withheld` reusing `unseal`'s `Recording`/`close`. It is small, and it
removes the second copy before it gets a reader.

**Done (2026-11-09).** `crates/kernel/src/recording.rs` is the one
protocol: a `Recording` guard over a thread-local stack of frames, whose
drop closes its frame and any left open inside it, plus `note`. `unseal`
and `withheld` each keep their own stack and use it, so `withheld::record`
now closes its frame on a caught panic as `unseal::record` always did
(test `withheld::tests::a_caught_panic_inside_a_recording_does_not_strand_its_frame`).
The two stay separate recordings rather than one `Observation` frame,
because their callers ask different questions (a cache keyed on opened
proofs, early cutoff keyed on glued bodies).

## 7. `Debug`'s budget state in three thread-locals

**Where.** `fmt.rs` ~48–90: `REMAINING: Cell<isize>` (where −1 means no
format is in progress), `DEPTH: Cell<u32>`, and `EXACT: Cell<bool>`, read by
`node` and set by `write_exact` (~115).

**The state.** Three states, Idle, Bounded `{remaining, depth}` and Exact
`{depth}`, held in three cells with a sentinel. `node` decides "outermost"
from `REMAINING < 0`, and the module already names the hazard: "In exact
mode the counter must never reach 0, or a nested call would mistake `r < 0`
for outermost and re-arm."

**What it misses.** That guard covers exact mode entered from Idle, where
the counter starts at `isize::MAX`. It does not cover `write_exact` *nested
inside* a bounded `{:?}`. Then the counter continues from the bounded
budget, exact mode never elides, and the counter goes below zero. The next
node takes itself for outermost and resets `DEPTH` to 0. When the enclosing
frames unwind, `DEPTH - 1` underflows. Reproduced with a throwaway unit test
(a `Debug` impl that calls `write_exact` on a 600-deep `Succ` chain inside
`node`): in a debug build it panics with "attempt to subtract with overflow" at `fmt.rs:81` (`d.set(d.get() - 1)`); in release the depth wraps to `u32::MAX` and every later node of the outer format is elided. Nothing calls `write_exact` from inside a
`Debug` impl today. Its callers are the metrics sampler and the elaborator
tests' Ψ hash. So this is latent. But CLAUDE.md treats "an accidental
`{:?}` is safe" as a rail, and this is a way around it.

**Make explicit?** Yes, cheaply: one `Cell<FmtState>` with `enum FmtState
{ Idle, Bounded { remaining, depth }, Exact { depth } }`, where `write_exact`
saves the whole state and restores it in its guard, and `node`'s
outermost test matches `Idle`.

**Done (2026-11-09).** `fmt.rs` holds one `Cell<FmtState>` with `Idle`,
`Bounded { remaining, depth }` and `Exact`. `node` arms the budget when it
finds `Idle`, and `write_exact` replaces the whole state and restores it in
its guard. Exact mode no longer counts anything, so it cannot run a
budget below zero. An outermost node also resets the thread to `Idle`
in a drop guard, so a panic inside a `Debug` impl no longer leaves later
`{:?}`s continuing a spent budget. The reproduction is now the unit test
`fmt::tests::write_exact_inside_a_bounded_format_resumes_it`, which panics
on the old code ("attempt to subtract with overflow") and passes on the
new.

## 8. Seven native-depth counters, hand-paired — leave them

`Tc::check_depth` (a `Cell`), `Conv::depth` (a field, paired by hand for the
reason `conv.rs` ~928 gives), `Eval::depth` plus `reserve_depth`,
`reduce::Frames`, `subst.rs`'s `SUB_DEPTH` (thread-local), `bounds::Cache::depth`
(inside a thread-local), and `fmt::DEPTH`. Each is incremented and
decremented around one recursive call with no `?` in between. I checked
every site. The two thread-local ones (`SUB_DEPTH`, the bounds cache) are
not restored by a panic. A caught panic in a pool worker leaves them high,
and that thread's later walks switch to spine iteration earlier. That is
the same answer computed by a loop, so it costs time only. Not worth a type.
If a guard is ever added for §7's `FmtState`, the same `DepthGuard` could
serve the two thread-locals for free.

## 9. Smaller ones — leave them

- **`reduce::Frames`** (~431): `Option` means both "no rule applies" and
  "gave up at the depth limit", disambiguated by the `exhausted` latch
  that `answer` reads at the end. Conservative (any answer after exhaustion
  is discarded), so it costs only wasted work after the limit. A three-way
  `Step` result would let arms stop early. Not worth it alone.
- **`Conv::has_defs`** (~858): decided once from the root Ψ, on the stated
  invariant that a telescope push never introduces a definition. True by
  construction of the recursor telescopes.
- **Conversion's value memo key** (`conv/dom/values.rs` ~731): Ψ by length,
  on "within a run it only grows". Sound because the closure addresses in
  the key already separate two pushes to the same length.
- **`Eval::transparent`'s save/restore** (~665–777): local and correct. What
  is wrong is that the memo does not see it (§1), not the restore.
- **`Eval::frames`' floor convention** ("a stack of stacks", ~258):
  `drive_above` truncates to its floor on every exit, errors included.
- **Direction booleans** (`w_is_b`, `left`, `first` in `conv.rs` and
  `conv/dom*.rs`): parameters, not state. A `Side` enum would read better,
  but nothing is at stake.

## 10. Already explicit, and good precedents

- `unseal::Recording`: a guard whose drop closes its frame (§6 asks
  `withheld` to share it).
- `fmt::write_exact`'s `Guard`, which restores rather than resets (§7 asks
  it to restore the whole state).
- `Conv::delta_lazy`: speculation as a scoped call that owns its mark, its
  drain and its rollback. §2's `attempt` is this, made the only way in.
- `bounds.rs`' weak-keyed slots, sound by the argument at ~176 with no
  state to keep. The two-stage marker stays deliberately implicit (first
  survey §10).
- `ConvError::{NotConvertible, OutOfFuel}`: "no" and "gave up" are distinct
  values, which `reduce::Frames` (§9) is not.
