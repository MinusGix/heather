---
title: Conversion cost is exponential in non-tail eval nesting: the working term itself grows ~2x per level
status: open
labels: [kernel,conversion,performance,ir]
created: 2026-07-31
updated: 2026-07-31
---

The deep IR path ([[simulate-conversion-cost]]'s ~24s `add(2,3)`-through-
`LetCall` figure) is **exponential**, and this issue owns the mechanism.
The exponent's axis is not fuel, not term breadth, and not value payload:
it is the **nesting depth of recursive `eval` calls in scrutinee (non-tail)
position** — `match ev(…) { Out(vs) => … }`. Each such level multiplies
work, peak memory, and the size of the largest single substitution by the
same factor. Everything that would indicate *re-computation* (reduction
steps, δ-unfolds) is **linear**.

The one-sentence mechanism: reduction is small-step rewriting on terms, so
an eliminator's β **materialises a physical copy of its branch bundle**, and
branch bundles nest — a depth-`d` nest is copied once per enclosing level.
Nothing shares the copies, so the term does not merely get re-walked, it
genuinely gets exponentially bigger.

**This path is memory-dangerous.** See the OOM incident below; every direct
`heather` run now goes under a `ulimit` wrapper.

## Measurements (release, 2026-07-31, 141ef76 + scratch counters)

`add(a, b)` through `add_prog`, `a` = loop iterations. Baseline (the file's
own declarations, no probe theorem) subtracted where marked.

| a | wall | peak RSS | subst node-visits | largest single subst | δ-unfolds | reduction steps |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 0.64s | 19 MB | 158 k | 7.4 k | 41 | 502 k |
| 1 | 1.24s | 84 MB | 3.24 M | 152 k | 75 | 509 k |
| 2 | 14.8s | 1016 MB | 75.9 M | 3.58 M | 107 | 515 k |
| 3 | — | **died at the 8 GB cap after 118s CPU** | — | — | — | — |

Through `LetCall` (the headline theorem, a = 2): 22.5s, 1508 MB, 134 M
subst node-visits, largest single substitution 5.52 M nodes.

**Growth law.** Time ×21/×20, RSS ×15/×15, substitution work ×20.5/×23.4,
largest single term ×20.7/×23.5 — **all four share one exponent, ≈22 per
loop iteration**. An add-loop iteration is ~6 executed fuel steps and ~32
δ-unfolds, so ≈1.65 per executed fuel step. Baseline file: 0.55s / 8.9 MB.

**Same exponent for time and memory is the discriminating fact**: the
working term is retained, not recomputed.

### The axis, isolated (four in-language probes)

| probe | shape | result |
| --- | --- | --- |
| `LetCon` chain, no args | N tail evals, no value consumed | **flat**: 0.59→0.68s, 9.4→10.2 MB over N=1..10 |
| `LetCon` chain consuming slot 0 | N tail evals, each consumes the previous computed value | **linear**: +1950 subst nodes/level, largest term pinned at ~500 nodes, N=1..8 |
| `LetMatch` chain in `rest` | N *sequential* matches (tail continuation) | **flat**: 0.61→0.75s, 10.0→10.9 MB, N=1..5 |
| `LetMatch` nested in the **arm** | N *nested* scrutinee-position evals | **exponential**: 10.7 k→117 k subst nodes, largest term 501→6207, ratio converging to ~1.85–2.3 per level, N=1..6 |

So: tail position is free, consuming a computed value in tail position is
linear, and only *nesting* multiplies. The add loop contributes ~4–5 nested
levels per iteration (`LoopIter`'s body eval, the `LetMatch` arm eval, the
`LetCon` inside it), which is exactly how ~2 per level becomes ~22 per
iteration.

**Payload size is irrelevant.** `add(a, b)` with `a` fixed and `b` = 1, 3, 5:
subst node-visits 3 241 443 / 3 241 794 / 3 241 054 at a=1 and
75 928 146 / 75 926 412 / 75 927 570 at a=2 — variation under 0.003%. The
values being carried are tiny; the *contexts* wrapped around them are not.

## Profile (a=2 direct probe, 14s, `perf -F 499 --call-graph dwarf`)

| self % | symbol |
| --- | --- |
| 16.7 | `Rc<Term>::drop_slow` |
| 11.8 | `subst::sub_tm::<SubstLocal>` |
| 9.7 | `bounds::Cache::term_use` |
| 7.2 | `subst::sub_tm::<ShiftLocal>` |
| 7.1 | TLS `with::<bounds::skip_term>` |
| 9.2 | libc malloc/free (three unresolved frames + `cfree`) |
| 3.6 | `drop_glue::<Level>` |
| 2.7 | TLS `with::<bounds::skip_type>` |
| 2.6 | `map_term::<SubstLocal>` |
| 2.5 | `ShiftGlobal::level` |
| 2.3 | `sub_ty::<SubstLocal>` |

Grouped: **substitution traversal ~26%, allocate/free/drop ~30%, the bounds
skip machinery ~21%, ShiftGlobal 2.5%.** Together, building and tearing down
terms is ~56% and there is no third thing.

**Contrast with the routine `lib/ir_v1.hthr` profile** (post the two
constant-shaving rounds): `Conv::ty` 6.6 → *does not appear at all* here;
`drop_slow` 6.9 → 16.7; the ShiftGlobal family 8.6 → 2.5; `Vec<CtxEntry>`
clone 4.3 → absent. The deep path is not the routine path scaled up; it is a
different workload, which is why the 1.56× the routine file gained bought it
nothing.

## Hypotheses that died

1. **Re-normalisation without memoisation** (the brief's leading candidate:
   δ-lazy conversion re-unfolding and re-reducing the same prefix). Dead.
   δ-unfolds go 41 → 75 → 107 (**+~32 per iteration, linear**) and
   `step_term_delta` entries go 502 k → 509 k → 515 k (**+~6 400 per
   iteration, linear**) while work grows ×22. The reduction *sequence* is
   linear; only what each step copies explodes. (`whnf_term_delta` is never
   called on this path at all — conversion drives `step_term_delta` itself.)
2. **`Defs::body`'s per-unfold `shift_global`.** Dead as the dominant cost:
   ShiftGlobal node-visits are linear (+~215 k per iteration) and 2.5% of
   the profile. [[outer-namespace-bounds]] is a real win on the *routine*
   file (8.6% there) and is **not** the deep-path lever. Worth recording so
   nobody sequences it expecting this.
3. **The term is a small DAG we re-traverse.** Dead, and this one was
   measured directly: a scratch pointer-keyed memo (`(Rc::as_ptr, Depths)`)
   inside each top-level `apply_local` hit **39 810 times out of 75.9 M
   visits — 0.05%** — and made a=2 *slower* (14.8s → 26.1s). The 3.58 M-node
   term is 3.58 M physically distinct nodes. Sharing is already gone by the
   time the substitution runs.
4. **Growing value payload.** Dead: `b` has no effect (above).

## The hypothesis that survived

Reduction rewrites terms. `beta_elim_tm` and friends build the branch
substitution and call `apply_local` on the branch, which walks and rebuilds
it. The branch of a non-tail `match ev(…) {…}` *contains the whole pending
continuation*, including the next nested eval. So level `d`'s β copies
everything level `d+1` will later copy again, and the bounds skip cannot
save it — those branches genuinely have free locals (bound by the
eliminator's own telescope), which is why the skip rate is only 70%
(52.9 M skips of 75.9 M entries) and why the 30% that is not skipped is
enough to be exponential.

Equivalently: the kernel has a *rewriter*, not an *evaluator*. There is no
representation in which a computed result is bound once and referred to.

## Candidate levers

1. **Sharing-preserving evaluation (NbE / closures).** Evaluate to a value
   domain with environments instead of substituting into branch bundles: a
   branch is never copied, it is closed over. This is the fix that changes
   the exponent rather than the constant — the other levers cannot. *Danger:*
   the largest kernel round on the board. It touches `reduce.rs` and
   `conv.rs` wholesale, must respect layer-indexed δ transparency
   ([[simulate-conversion-cost]]'s definitions design) and ch. 06's
   syntactic treatment of boxed code (reduction never enters a `box`; a
   value domain must preserve that), and has a ch. 07 bill of its own.
   Read `docs/delam/06` before costing it. Do **not** start it as a
   performance round; it is a design round.
2. **Sub-lever: stop materialising branch bundles.** If β could produce a
   *delayed* substitution node (an explicit-substitution / suspension form
   in `Term`) instead of walking the branch, the copy would happen at most
   once per node actually inspected. Smaller than (1) and reuses the bounds
   machinery. *Danger:* explicit substitutions are famous for breaking
   confluence/termination proofs and for making `conv.rs` compare terms that
   are equal only after forcing; the metatheory cost is not obviously less
   than (1)'s.
3. **Constant-factor only, and named as such:** the bounds skip machinery is
   **21%** of this profile at a 70% skip rate, paying a thread-local
   `RefCell` probe per node entry — logged as a deep-path datapoint on
   [[bounds-metadata-taxes-one-shot-checking]]. Allocation/drop is ~30% and
   an arena or a smaller `Term` node would shave it. Both are ~1.3–1.5×
   on a curve whose base is 22; they buy less than one loop iteration.
4. **Not levers here:** [[conv-pointer-equality-reflexivity]] (the two sides
   are never pointer-equal on this path — the whole cost is *producing* the
   normal form, before any comparison), [[context-representation-clones]]
   (the Γ half does not appear in this profile at all), and
   [[outer-namespace-bounds]] (2.5%).

## The OOM incident (2026-07-31)

An uncapped `heather check` on the a=3 probe reached **~22 GB RSS (~40% of
a 54 GB machine)** and OOM-pressured the host; the driving session was
killed. Under an 8 GB `RLIMIT_AS` the same probe aborts after 118s CPU, as
it should. Consequences:

- **Every direct `heather` invocation runs under a memory cap and a CPU
  timeout**, e.g. `(ulimit -v 8388608 -t 120; target/release/heather check
  <file>)`, the same discipline `scripts/test` and `scripts/bench` already
  enforce. Landed as its own commit (141ef76).
- **Three loop iterations is the cliff.** The headline
  `add(2,3)`-through-`LetCall` theorem (2 iterations) peaks at 1.5 GB, which
  is survivable; a=3 is not. Nobody should reconstruct a deeper probe
  without a cap.
- `lib/ir_v1.hthr`'s comments already explain why the loop and the call are
  certified separately; the reason is now stronger than "24s".

## Trigger / next step

Reopen for work when either (a) a `Compile` certificate needs more than ~2
nested non-tail eval levels — i.e. the first real
[[end-to-end-compile-instance]] — or (b) [[ir-simulate-design]]'s
`converges`/`refines` interface makes deep discharge routine rather than an
acceptance curiosity. Until then the discipline stands: **write certificates
with shallow non-tail nesting**; tail chains are free and linear, and that
is a fact about the interpreter's *shape*, not just its cost.

Acceptance for a fix: the arm-nested `LetMatch` probe (N=1..8) linear in N,
recorded as a kernel bench fixture alongside `conv/simulate-depth` and
`conv/simulate-payload` — those two are linear/flat precisely because
neither varies nesting, which is why this defect was invisible to them.
That gap is itself the lesson: `docs/testing-generated-terms.md`'s axes
should gain *nesting depth of non-tail recursive calls*.

## Log

- 2026-07-31: Filed out of the deep-path investigation round. Reproduced 22.5s / 1.5 GB for the `add(2,3)`-through-`LetCall` theorem, established the growth law on four independent quantities with one exponent (~22 per loop iteration, ~2 per nested level), isolated the axis with four in-language probes, profiled it, killed four hypotheses including the brief's leading one, and sized the only lever that changes the exponent. Scratch instrumentation (counters in `reduce.rs`/`subst.rs`, a pointer-keyed memo experiment) lived in a throwaway worktree and is gone; nothing landed on master but this issue and the log entries it points at.
