# A depth budget beside the fuel

Round of `issues/kernel-native-depth-budget.md` (2026-09-09), implementing the
resource-diagnostic clause of `issues/bitvec-closed-reduction-cost.md`. Fuel
makes the checker total on ill-typed input by bounding the *steps* a reduction
takes. It does not bound the *frames* a reduction stands on, and this round is
about the workloads where those two numbers come apart far enough that the
process dies instead of answering. The stack figures below are here rather
than in the issue log because they derive a constant in the source; the sweeps
they were read off live in the issue log.

## 1. Where the depth is

`Eval::drive` keeps the machine's **tail** positions off the native stack: a
reduction chain is a `while` loop over `Work`, so divergence returns
`OutOfFuel` rather than overflowing (measured 2026-07-31: Ω under a 500-step
budget overflowed 8 MiB). Its non-tail positions — a scrutinee, an
application's function, a type annotation — are ordinary Rust recursion, "where
the depth is the syntax's".

That last clause is the false premise. It holds of a *term*; it does not hold
of a *value*. `iterate_increment` builds `increment(n, ih)` with `ih` the
pending elimination of the previous increment, and `increment` matches on it,
so forcing the head bit of the old `bitvec::add(64, a, b)` re-enters `drive`
once per unit of `toNat(b)` from syntax that is a dozen nodes deep. Fuel is
spent on the way back out, so the machine goes deep *first*: at a count of
4096 it is 4096 frames down with its 2^20 fuel almost untouched.

Two sites carry native depth, and the round counts both:

- **`Eval::drive` re-entries.** This is where the live reproducer dies, and —
  measured below — where every workload that needs real depth spends it.
- **`Conv::tm` / `Conv::ty`.** Conversion recurses natively over the values it
  compares, and it calls the evaluator *from inside* that recursion
  (`conv/dom/values.rs::run`), so the two interleave on one stack. Neither is
  bounded by the other.

A drive re-enters only when the enclosing one is still in its loop, which is
what separates the two nestings. A *syntactic* chain of scrutinees does not
qualify: `step_eval` walks it to the bottom before the first `drive` starts, so
those machines run one after another and the depth is `step_eval`'s, not
`drive`'s. A chain in the *value* does: each scrutinee is a variable standing
for a thunk, and forcing it starts a machine inside the machine that asked.
`nested_scrutinee_value` in `eval_differential.rs` is that shape at its
smallest.

`Eval::force_ty`, `eval_ty` and `decode` recurse too, but every cycle among
them passes through `drive` — there is no native loop among *them* that the
counter misses. `step_eval`'s own syntactic recursion is not counted; see §6.
Nor is `typing.rs`'s walk: its depth is genuinely the syntax's, and it is
`issues/numeral-stack-depth.md`'s (a fat-frame problem, not an
unbounded-depth one).

### What was measured

Release and debug `heather check`, one furnace box, main-thread stack varied
with `ulimit -s`, on `toNat(64, bitvec::add(64, ofNat(64, 0), ofNat(64, N)))`:

| | largest N that answers at 8 MiB |
|---|---|
| release | 2048 (2560 aborts) |
| debug | 1920 (2048 aborts) |

and, with the budget in place and its bound varied, the largest bound that
answers instead of aborting:

| stack | release | debug |
|---|---|---|
| 4 MiB | 1024 (1280 aborts) | 1024 (1280 aborts) |
| 8 MiB | 2304 (2560 aborts) | 2048 (2304 aborts) |
| 16 MiB | ≥ 5120 | ≥ 5120 |

So a counted level costs ≈ 3.5 KB of stack in release and ≈ 4 KB in debug, and
the cost is linear in the stack as it must be. The near-absence of a
debug/release gap is worth naming, because it is the opposite of
`numeral-stack-depth`'s 18× : the frames here are `drive_from`'s own, whose
size is dominated by `Work` and `Elim` locals that optimization does not
shrink, not by the fat unoptimized frames of the checking walk.

## 2. What the first reproducer turned out to be

`theorem t(): nat::half(1048576) = 524288 { refl }` — the issue's
course-of-values reproducer — **no longer reproduces**. It checks in the module
baseline. Run-program arithmetic (`issues/nat-run-algebra-primitives.md`, landed
2026-09-09) classifies `half`'s step algebra and iterates it over the run
instead of descending it, so the depth is not spent at all. It is pinned as a
*success* control (`half_computes_at_a_large_closed_argument`, `nat_parity.rs`)
rather than the refusal control the issue's acceptance asked for: a computation
that answers is a better outcome than one that is refused politely, and the
control still fails loudly if the depth ever comes back.

The nested-scrutinee reproducer is untouched by that work and is the one the
budget is for.

## 3. The counter

One shared account, for the same reason fuel is one shared account: the frames
are one stack.

- `reduce::NATIVE_DEPTH_LIMIT` — the bound, beside `OutOfFuel` because it is
  the same totality argument.
- `Eval::depth` — live `drive` re-entries. `drive` refuses at the bound before
  incrementing, and decrements on the way out (including the error path, which
  is why the decrement precedes the `frames.truncate`).
- `Conv::depth` — live `Conv::tm`/`Conv::ty` nodes, taken by `Conv::descend`
  and given back by hand. The comparison nodes are the only callers and a guard
  type would have to borrow `self` across their bodies, so hand-pairing is the
  cheaper honesty here.
- `Eval::reserve_depth`, called by `conv/dom/values.rs::run`, tells the machine
  how many frames conversion is already standing on. Unlike fuel it is not
  handed back: the frames are gone when the run returns.

The policy is fuel's, exactly: **a machine that answers under the budget
answers what the deeper stack answers.** The bound decides *whether* there is a
verdict, never what it is. Nothing about the bound is a cost model, and no path
refunds it.

## 4. The bound

`NATIVE_DEPTH_LIMIT = 1024`.

The rail is 8 MiB — `RUST_MIN_STACK=8388608` in `scripts/test`, which is also a
main thread's default, so it is what a `heather check` gets too. That leaves
two numbers to sit between, and they are closer together than the issue
expected:

- **What the stack holds**: ≈ 2000 levels at 8 MiB, from §1's table.
- **What real work needs**: more than the 512 this round first tried. A bound
  of 512 broke two live workloads — the `conv/computed-numeral` bench family at
  n = 512, and the x86 native-certificate CLI tests — and 576 fixed both, with
  the conversion counter pinned high throughout. So the requirement is
  evaluator depth, at just over 512, and `heather check lib/std` (which needs
  64 and fails at 32) is nowhere near the interesting part of the range.

1024 is the midpoint on a log scale: ≈ 1.8× what the deepest known good
workload needs, ≈ 2× under what the stack physically holds, ≈ 4 MiB of the
8 MiB rail. Both margins are thin, and that thinness is a real finding rather
than a tuning failure: at ≈ 4 KB of stack per re-entry there is only about one
decade between "answers" and "aborts", and the way to widen it is to make the
frame smaller, not to move the bound. That is `issues/eval-native-frame-size.md`,
filed out of this round, and it is the same complaint
`issues/numeral-stack-depth.md` makes about a different walk.

Against the workloads at 1024: the reproducer is refused, `lib/std` checks, the
rail's own `bitvec::add` at count 8 still checks — which is the separation the
budget has to make — the suite is green, and `scripts/bench --check` reports
every scaling comparison within its threshold with `stack/check-numeral` at
its recorded depth.

## 5. Reporting

A depth refusal reports the existing `OutOfFuel` — no distinct reason text.

The issue preferred a distinct reason and allowed this fallback if threading
one rippled. It ripples: `OutOfFuel` is a unit struct with 42
construction-and-pattern sites across `heather-kernel`, `heather-elab` and a
dozen integration tests, plus the `ConvError::OutOfFuel` and
`TypeError::OutOfFuel` variants that lift it. The alternative fallback — a
kernel-side counter — was also declined, because the only place to increment it
is `drive`, which is the checker's hottest function, and this round is not a
perf round and should not be spending on diagnostics there.

What is lost is small and recoverable: depth exhaustion is exactly the case
that leaves fuel unspent, so the two are distinguishable by anyone with a
debugger or a smaller input, and the shapes that produce it are recorded here
and pinned as tests. If the diagnosis is wanted for its own sake, the honest
version is a `Reason` on `OutOfFuel` and its own round.

## 6. Deliberately not done

- **Moving scrutinee evaluation onto the trampoline** (a `Frame` for "an
  elimination waiting for its scrutinee's value") would remove this class
  rather than bound it. It also costs the machine its simplest invariant —
  that the heap stack carries only the two places a result flows *back* into
  something — and turns every non-tail position into a frame kind. Bounding
  first is the verdict-neutral step; that is a redesign.
- **A guard page or `stacker`-style stack growth** hides the abort without
  bounding anything: the computation that overflows 8 MiB overflows 8 GB a
  little later, and the checker would then be total only up to the machine's
  memory.
- **Bounding `step_eval`'s syntactic scrutinee chain, or `typing.rs`'s walk.**
  Both have a real bound already — the syntax's depth — and neither is what
  aborted. What they have is fat frames, which is
  `issues/numeral-stack-depth.md`'s complaint and needs the frames measured,
  not a counter added.
- **Making the bound configurable.** A knob on a totality invariant invites
  callers to trade the invariant for a workload, and there is no caller that
  needs to. The tests exercise a small effective budget through
  `Eval::reserve_depth`, which is the mechanism conversion already uses.

## 7. The small-step reducer

`reduce::step_term_delta` and `step_type_delta` walk syntax too, and §6's
argument for leaving such walks unbounded does not reach them. A step recurses
into the head or scrutinee it is blocked on, so its depth is the depth of the
term, and that term is one reduction built. δ-unfolding a closed
`pow(3, 5000)` nests a blocked `mul`/`add` per level of the exponent. The
first step of `x < pow(3, 5000)` stood on about 2,000 frames and aborted. The
oracle's step budget could not stop it (`SemanticOracle::whnf_type`, where
the value machine had answered "stuck" and the reducer was only asked to spell
it), because fuel counts steps and this was one step.

The reducer now keeps its own account against the same
`NATIVE_DEPTH_LIMIT`. It is private to `reduce.rs`: a `Frames` cell per public
step, taken on entry to each recursive step and given back on the way out.
Past the bound a step returns `None` upward, marks itself exhausted, and the
public entry points answer `Err(OutOfFuel)`. So every answer given past
exhaustion is discarded, including a later congruence that stepped something
else, and exhaustion never reads as "no rule applies". The public signatures
changed from `Option` to `Result<Option, OutOfFuel>` for exactly that reason.
Every caller either propagates the error (`whnf_*`, `eval`, the syntactic
conversion domain) or already treated "no answer" as best-effort (the
oracle's reduct iterator and diagnostics, `inductive`'s decoded view).

The account is per step and not shared with `Eval::depth`. The one place the
reducer runs inside the machine, `elim^Trm`'s Δ-scoped annotation, can in
principle stand on both budgets at once. That annotation is small syntax, the
same argument §6 makes, and it is not what aborted.
