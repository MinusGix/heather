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

**Read the two sections together.** The paragraph above is the axis as first
measured, and it is right about the recursive interpreter. A later round
(§"The route that does not work") found the axis is *broader*: a
scrutinee-position recursive call is one way to carry a term forward as an
unforced redex, and an ordinary data field of a step machine — or a
semantically invisible identity wrapper — is another, with the same ~×2 per
level. The title's "non-tail eval nesting" is the instance, not the class.

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

**Refined 2026-07-31 by the stage-0 instrument, and this narrows the axis
by one turn.** Three arm-nested variants were built at CLI level, differing
only in what the arm and its continuation return, and only one is
exponential (peak RSS at N = 12):

| arm-nested variant | N=12 peak RSS |
| --- | --- |
| nesting only — every `Ret` is `Ret(RNil)`, nothing consumes anything | 13 MB |
| nesting + a scrutinee value that deepens one constructor per level | 13 MB |
| nesting + each continuation rebinding the nested eval's `Out` payload | **511 MB** |

So *nesting is necessary and not sufficient* (which is
`docs/nbe-conversion-design.md` §12's secondary finding, now reproduced in
the language rather than in hand-built kernel terms), and a growing
scrutinee payload is not the axis either. What multiplies is a nested eval
whose **result is consumed by the pending continuation** — the continuation
is the thing copied per level, which is §"The hypothesis that survived"
stated as a property of the probe. The first variant is the instrument's
negative control (`--family flat`) precisely because it holds nesting fixed
against the one thing that turned out to matter.

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
   the exponent rather than the constant — the other levers cannot.
   **Designed 2026-07-31: `docs/nbe-conversion-design.md`**, with the staged
   plan, the acceptance gates and the kill criteria. Headline decisions: the
   declarative system does not change (no rule, no former, no ch. 07 bill);
   `reduce.rs` survives as ch. 06's relation, as `typing.rs`'s whnf and as
   the differential oracle; **there is no readback**, which is what keeps
   the TYPES 2024 irrelevant-domain problem away from the landed SProp
   formers; the one new obligation is machine adequacy (`eval` ≡ ch. 06
   `⇝*`, both directions). Sized at ~5 definitions-rounds. Do **not** start
   it as a performance round; the design round is done, the *instrument*
   round (stage 0) is next.
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

## The route that does not work: defunctionalize the interpreter (2026-07-31)

The obvious in-language fix — rewrite `simulate` as a defunctionalized step
machine (`Config` = environment × instruction × continuation-frame chain,
`step : Config -> Config`, `run` iterating it on fuel in tail position) so
that no `eval` ever appears in scrutinee position — was implemented and
**measured strictly worse than the recursive interpreter it replaced**. It
is written down here so nobody spends the day on it twice.

The machine was faithful to every discipline this file and
[[ir-simulate-design]] record: recursion on fuel alone, one syntactic ih
occurrence, ih applied in tail position to the previous configuration,
`run` stopping at halted configurations (unused fuel stayed free —
verified: fuel 20 vs 400 identical). Frames: arm-return and call-return
unified as one "rebind and continue" frame, plus a loop-iteration frame.

| probe | recursive (master) | step machine |
| --- | --- | --- |
| declarations only | 0.55s / 8 MB | 4.9s / 10 MB |
| `LetCon` chain, N=8 | 0.6s / 10 MB | 5.4s / 13 MB (flat) |
| sequential `LetMatch` chain, N=4 | 0.73s / 10 MB | 5.9s / 81 MB |
| sequential `LetMatch` chain, N=8 | 0.86s / 11 MB | **died at the 8 GB cap** |
| `LetCall` chain, N=8 | 0.76s / 10 MB | **died at the 8 GB cap** |
| `LetCall` chain, N=16 | 0.89s / 13 MB | **died at the 8 GB cap** |
| `add(a,1)`, a=1 | 1.24s / 84 MB | 13.7s / 606 MB |
| `add(a,1)`, a=2 | 14.8s / 1016 MB | **died at the 8 GB cap** |

So the machine is exponential in the number of **sub-region returns** —
frame pushes and pops — which the recursive interpreter does in *flat*
time and memory. It bought nothing on the axis it targeted and lost a loop
iteration overall.

### What the isolation experiments say (machine, `LetCall` chain, N=4→8)

| the frame-return does | N=4 | N=8 |
| --- | --- | --- |
| `CEval(append(vals, env), rest, next)` | 55 MB | died |
| `CEval(env, rest, next)` (drop the rebinding) | 12 MB | 13 MB |
| `CEval(id_val(env), rest, next)` — a semantic **identity** | 19 MB | 307 MB |
| push one slot per machine step, carrying `vals` | died at N=3 | died |
| the same, with a literal `VNil` in the pending field | 15 MB | 17 MB |

The third row is the finding. `id_val` is `match v { VNil => VNil,
VCons(h,t) => VCons(h,t), VCon(a,b) => VCon(a,b) }`: same values, same
step count, same everything — one wrapper — and flat becomes ~×2 per
level. Payload size stays irrelevant on the machine too (a 6-deep match
chain: 7542 MB at payload 0 vs 7551 MB at payload 12).

**The conclusion is stronger than the original diagnosis, and it revises
it.** The axis is not "recursive eval in scrutinee position": it is
whether a term the interpreter carries forward is *stored as a redex*. A
recursive `eval` in scrutinee position is one way to store a redex; a
configuration field is another; a semantically-invisible identity wrapper
is a third. Each level's forcing re-forces the levels beneath it and
nothing shares the result — which is §"The hypothesis that survived",
restated without reference to branch bundles. **No restructuring of the
interpreter can fix this, because the language has no way to force a
value.** The lever list below is unchanged and lever 1 (evaluate to a
value domain — NbE) is the only one that applies.

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

The trigger deliberately does **not** say "when someone restructures the
interpreter": that route is spent (see the section above), and the known
consumer stays the recursive interpreter on master. What would change the
picture is a kernel that shares a forced result — lever 1.

**Trigger amendment 2026-07-31.** Lever 1 now has a design and a staged
plan (`docs/nbe-conversion-design.md` §13), so the trigger gains a second,
independent arm: **the plan is startable now, beginning at stage 0** (build
and validate the acceptance instrument, ~0.3 of a definitions round), and
stage 0 is worth doing ahead of any decision to fund the rest — it is cheap,
it is the round's kill criterion, and without it no later stage can be
gated. Stages 1 (value domain + evaluator, unwired, differential-tested)
and 2a (make the comparison arms shape-agnostic — a no-op refactor) are
likewise independently landable and independently valuable. Stage 2b, the
switch of `conv.rs` to values, is the irreducible risk and should not be
started until stage 0 has produced a validated curve.

**The instrument now exists: `scripts/probe-whnf-sharing`** (stage 0, landed
2026-07-31). Its docstring holds the shape, the master curve and the gate;
`--expect linear` is what a fix has to make pass. It sweeps N = 1..15 rather
than 1..8 because below N ≈ 9 the 0.57 s declarations baseline dominates the
wall clock — peak RSS is already doubling per level from N = 5, and it is the
quantity to read at small N.

Acceptance for a fix: the arm-nested `LetMatch` probe (N=1..8) linear in N.
`conv/simulate-depth` and `conv/simulate-payload` are linear/flat precisely
because neither varies nesting, which is why this defect was invisible to
them. That gap is itself the lesson: `docs/testing-generated-terms.md`'s
axes should gain *nesting depth of non-tail recursive calls*.

**Amended 2026-07-31 (design round, and this is a plan change).** The probe
is **not** a kernel bench fixture: the bench suite is zero-dependency and
cannot call the elaborator, and three hand-built kernel-term reconstructions
of the shape — branch-nested, interpreter-shaped, and interpreter-shaped
with a duplicated induction hypothesis — all measured **linear** (per-level
ratio 0.8–1.5 over d/F = 1..14; spike in `docs/nbe-conversion-design.md`
§12). Nesting is *necessary* for the exponent and not *sufficient*: in small
hand-built terms `subst.rs`'s depth-zero fast path shares the duplicated
payload as one `Rc`, whereas in the elaborated interpreter shifting under
binders destroys that sharing — which is dead hypothesis 3's 0.05% measured
from the other side. So the gate is the **elaborated `.hthr` probe driven at
CLI level** under `(ulimit -v 8388608 -t 120; …)`, and it must be
**validated on master first** (ratio ≥ 1.8 per level over ≥ 4 consecutive
levels) before it gates anything — a family that is linear on master proves
nothing when it is linear after. That validation is stage 0 of the plan and
carries the round's kill criterion.

## Log

- 2026-07-31: Filed out of the deep-path investigation round. Reproduced 22.5s / 1.5 GB for the `add(2,3)`-through-`LetCall` theorem, established the growth law on four independent quantities with one exponent (~22 per loop iteration, ~2 per nested level), isolated the axis with four in-language probes, profiled it, killed four hypotheses including the brief's leading one, and sized the only lever that changes the exponent. Scratch instrumentation (counters in `reduce.rs`/`subst.rs`, a pointer-keyed memo experiment) lived in a throwaway worktree and is gone; nothing landed on master but this issue and the log entries it points at.
- 2026-07-31: Primary consumer NOT restructured: the defunctionalized step-machine route was implemented against lib/ir_v1.hthr and measured strictly worse than the recursive interpreter -- flat cases stayed flat, but every sub-region return became exponential (8-deep LetCall chain: 0.76s / 10 MB recursive, dead at the 8 GB cap on the machine; add(a,1) died at a=2 rather than a=3). Recorded as its own section above with the probe table and five isolation experiments. The kernel defect is UNCHANGED and this issue stays open with its existing trigger; what changed is the diagnosis, which is now broader and stated without reference to branch bundles: the axis is a carried term stored as an UNFORCED REDEX, of which a scrutinee-position recursive call is only one instance -- a configuration field does it, and so does a semantically invisible identity wrapper (id_val(env): same values, same steps, flat becomes ~x2 per level). Since the language cannot force a value, no in-language restructuring reaches it, so the trigger now says explicitly that the interpreter-restructuring route is spent and only lever 1 (a kernel that shares a forced result) applies. docs/testing-generated-terms.md gains nesting depth as axis 5.
- 2026-07-31: Design round done, no kernel code: docs/nbe-conversion-design.md costs out lever 1 (sharing-preserving evaluation) with decided answers, rejected alternatives and a staged plan (~5 definitions-rounds). Headline decisions: scope is a shared-value whnf for CONVERSION only, not full NbE — reduce.rs survives verbatim as ch. 06's relation, as typing.rs's whnf (9 sites, all on types, all cold — the deep-path profile shows no typing symbols) and as the differential oracle, and beta_elim_* is shared rather than transcribed a sixth time; the value domain makes invariants unrepresentable rather than merely unviolated (El and canonical-length Vec/Fin cannot BE values, box values carry raw syntax with no environment so reduction structurally cannot enter one), locals are the only environment-based namespace while levels/globals stay syntactic, and variables need a two-part identity (level into the concrete entries, depth into the abstract CtxBase::Var prefix) because textbook de Bruijn levels break on context variables; the subtlest correctness point is that a global's local substitution must store its terms as VALUES, else u^delta reintroduces the defect class verbatim. Evaluation exists at p/m only and carries no layer index (Defs already encodes the one bit). delta becomes glued neutrals with memoized unfold thunks — the delta-lazy order and the has_defs gate survive and improve (O(1) head test, second visit free, and the rescoped body cached per GlobalVar since shift_global depends only on the index). Fuel: one unit per step ch. 06 would have counted, forcing is FALLIBLE everywhere (no infallible force, no Deref — a single one silently converts exhaustion into a verdict), no thunk memoizes a failure, and the invariant that comparison never inspects an unforced value is what keeps laziness from changing the relation; fuel accounting becomes sharing-dependent, so fuel-sensitive tests keep their property (insufficient budget dies OutOfFuel, never a verdict) and lose their numbers. THERE IS NO READBACK — every customer was checked and none needs syntax back, which is the design's largest simplification and the reason the TYPES 2024 irrelevant-domain negative result does not bite the landed sEq/sEmpty formers. Bounds metadata: conversion stops being its customer entirely (the 21% leaves rather than shrinks); re-measure at cleanup, honest prediction is deletion. The strict-let/force alternative is priced and rejected on four grounds, chief among them that head-only forcing cannot reach an identity WRAPPER and no data-directed deep force reaches a pending continuation. Metatheory: declarative system untouched, the one obligation is machine adequacy (both directions, against the unbounded relations, with fuel's property stated separately), DESIGN.md's 'ch. 06 verbatim' moves from the algorithm to the specification, and it is recorded in the design doc + ch05-06-lemma-audit rather than as a Part V of metatheory-ch07-extensions (which extends the declarative system; this does not).
- 2026-07-31: Stage 0 of [[nbe-conversion-round]] landed the acceptance instrument, `scripts/probe-whnf-sharing`, and VALIDATED IT ON MASTER (4300b31) — the round's kill criterion did not fire. The probe is the arm-nested `LetMatch` shape generated on top of `lib/ir_v1.hthr`'s declarations (no import system, so it generates rather than commits a copy), driven through the release CLI under the ulimit rail, N = 1..15. Baseline-subtracted master curve: wall 0.06s -> 33.77s, peak RSS 0.0 MB -> 4544 MB; RSS ratio >= 1.8 across five consecutive levels (N = 11..15, tail geometric mean 2.12), wall across three (N = 10..12, tail geometric mean 1.91, per-level ratios +-30% noisy across repeat sweeps). The negative control -- the same nesting with nothing consuming the nested eval's payload -- never reaches 1.8 and is ~0.4 MB per level. The sweep also refined the axis: nesting alone is not sufficient (13 MB at N=12) and neither is a deepening scrutinee value (13 MB); the exponent needs the continuation to REBIND the nested eval's Out payload (511 MB), which is the surviving hypothesis isolated in-language. The optional kernel-bench variant was attempted once more, informed by subst.rs's own 'a payload inserted under k>0 binders still costs a full copy', and measured linear (slope 1.44 over twelve levels); recorded as family D in design doc section 12, so four hand-built kernel families have now failed where the elaborated probe succeeds. This issue closes when `scripts/probe-whnf-sharing --expect linear` passes.
- 2026-07-31: The instrument went linear. [[nbe-conversion-round]] stage 2b switched conversion to the value machine, and `scripts/probe-whnf-sharing --max 15 --family both --expect linear` now exits zero on the same machine that recorded the master curve: the nest family's N = 15 goes from 33.77 s / 4544 MB to **1.87 s / 21.5 MB**, its tail geometric means from 1.91 wall / 2.12 RSS to **1.09 / 1.18**, and it has collapsed onto the flat control (0.81 s / 11.3 MB against 0.80 s / 8.5 MB, baseline-subtracted). The in-language witness: the combined `add(2,3)`-through-LetCall theorem this issue diagnosed as ~×22 per loop iteration is **20.88 s → 1.21 s** (both measured here, the first against a release build of the pre-stage commit), and `add(3,4)` — the shape lib/ir_v1.hthr's comment says reaches ~22 GB and takes the machine down — checks in 1.25 s under an 8 GB cap. The lever was lever 1 as costed: an eliminator's β extends an environment instead of copying a branch. **Closing is stage 4's call, not this entry's** — the round's own tracker sequences it, and stage 3 (δ glueing) and stage 4 (the rewriter path, bounds.rs re-measured) are still open. Recorded here so the close condition is visibly met.
