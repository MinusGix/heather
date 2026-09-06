---
title: Emitted annotations no registered code can name: fn-typed-parameter Apps, monomorphized and quoted Wf copies
status: open
labels: [elaboration,performance]
created: 2026-08-13
updated: 2026-09-06
---

The emitted-mass residual of [[wf-shape-annotation-slots]]'s round (docs/wf-shape-code-design.md §7), promoted out of that closing issue's log so it keeps a live home. Two families of emitted `Type::Wf` occurrences survive both spelling rounds because no registered definition names them:

1. **An `App`'s `dom`/`cod` at a function-typed parameter** (`ev: Val -> Ir -> Res`): the annotation is copied from the binder's type during elaboration, not from a callee's Psi statement, so the statement-respell cascade cannot reach it. A handful of occurrences per declaration — small, but named and measured.
2. **`Type::Wf` occurrences that are not any declaration's registered lowering**: monomorphized instantiations (the `Box<T>`-style per-instantiation copies — registration is closed-only by design, [[wf-field-conversion-cost]]) and copies quoted inside a code literal (`⌜⟦D⟧⌝`), where a reference cannot stand because the quote is syntax. This includes open instantiations of a parameterized or value-indexed record: there is a declaration to name, but today's `TyCode` registration cannot abstract over the instance telescope.

Fix shapes, if a round takes one: (1) is a use-site respell at the App-annotation emission (the machinery exists: `respell_ty_deep`); (2) is harder — per-instantiation registration keyed by the monomorphized type, or accepting it as the boundary of the scheme.

## When

Triggered: the next time emitted node mass matters on a workload where the per-slot counters attribute the residual to these families — one deliberate round, per the accumulator discipline. Re-run the counters first; both families were a minority of mass when filed (2026-08-13).

## Log

- 2026-08-13: A NEGATIVE FOR THIS ISSUE'S TRIGGER, from the certgen family's post-evaluation attribution round ([[certgen-harness-cost]] owns the round and its numbers). The trigger says "the next time emitted node mass matters on a workload where the per-slot counters attribute the residual to these families" -- so, recorded: on today's certgen workload, **emitted node mass does not matter**, and family (1) in particular is not what is being paid.

The measurement (rendered-Psi bytes added per declaration, against that declaration's wall, 2026-08-13): `ta_inr` in lib/certgen_code.hthr adds **289 kB** of Psi and checks in **117 ms**; `ta_app` adds 246 kB and checks in 96 ms; `k_bind_mono` in lib/ir_v1.hthr adds **129 kB** and checks in **2,430 ms**. That is a ~150x spread in time-per-emitted-byte between a `refl` pin and a transport lemma, in the direction opposite to mass.

`k_bind_mono` is the interesting case for this issue specifically, because it is exactly family (1)'s shape -- three function-typed parameters (`ev1`, `ev2`, `hyp: (e, i, w) -> ev1(e,i) = Out(w) -> ...`), so its `App` `dom`/`cod` annotations are the unnameable copies this issue owns, and 129 kB for thirteen lines is presumably largely them. At `ta_inr`'s rate that mass would cost ~50 ms; it costs 2.43 s, of which `conv_type` is 2.05 s in a long tail of individually expensive comparisons ([[conversion-cost-at-large-values]], logged today). So the mass is real and this issue's family (1) is confirmed present at a named declaration -- it is simply not the cost there, and a use-site respell at the App-annotation emission would not move that workload. Re-run the counters before spending a round, as this issue already says; this entry is the denominator for the next person who does.

- 2026-08-25: **Trigger fired for family (2)** in
  [[ir-pass-probe-elaboration-cost]]. `IrPassLawsProbe<M>(R, alg)` is a
  parameterized and value-indexed proof record instantiated openly at
  `M = Ir`; its exact rendered type is about 1.00 MB, and record/law bodies
  carrying its construction and projections render at 9.92--32.28 MB each.
  Dependent matches directly on `Ir` contribute another 21.71--31.45 MB per
  declaration. Per-gate conversion, typing, and evaluator counts track those
  sizes linearly, and the standalone target spends about 36 seconds checking
  them.

  This is the positive counterpart to the 2026-08-13 certgen negative: emitted
  annotation mass is the wall here. Local `let`, theorem opacity, proof
  splitting, and an evaluator zero-step shortcut were all measured and
  rejected; none names the open instantiated type. The next design should
  weigh a telescope-abstracted `D#tycode` (including value parameters) or an
  equivalent local/open type-sharing representation, then respell the record
  literal/projection and Wf-match annotation sites. It must retain inline
  copies at structural readers and the wrong-global/look-alike negatives of
  the closed-family code-definition rounds.

- 2026-08-25: **The direct telescope-abstracted `TyCode` experiment is a
  negative, and narrows the design.** The kernel already admits the proposed
  definition without a new rule: `D#tycode : Trm_c(Delta |- Ty l)`, referenced
  by a checked `LocalSubst` carrying the type and value arguments. The
  prototype retained each lowering's originating substitution for the
  emission pass (rather than unsoundly trying to invert a monomorphized
  structural type), extended `unspell` at structural/inference boundaries,
  and passed the focused closed/parameterized code tests.

  It did not pass the workload criterion. With the contextual whole-record
  code alone, `ir_fold_same_probe` reached its gate in about **8.2 s** rather
  than the old target's roughly 36 s, but exhausted the ordinary 2^20
  conversion budget. Abstracting the parameterized record's generated
  projection/tail definitions as well still exhausted that budget (about
  14.8 s to refusal). A diagnostic 4x-fuel run passed, but the whole target
  took **129.2 s**. A 2x-fuel run was still running past a minute and was
  stopped. All prototype code and the diagnostic fuel change were reverted.

  Cause: this representation hides the useful outer structural head behind
  `El (D#tycode[delta])`. Type-directed conversion must delta-unfold it to
  learn that a value is a Sigma/record, and mixed compact/structural
  annotations make that happen repeatedly. The syntax is dramatically
  smaller while normalization work becomes dramatically larger. Raising fuel
  is therefore not a fix.

  The next experiment should preserve the outer structural head and share
  only the large dependent tails, or add memoized contextual unfolding whose
  cache survives the many conversion queries in one kernel gate. In concrete
  terms, prefer a contextual/open analogue of the existing `RecFam` tail
  device (with a compact structural spine at use sites) over a whole-record
  `El(GlobalTm)`; alternatively make normalized contextual global instances a
  gate-local shared object. Acceptance remains: the default fuel test passes,
  exact core mass falls, and standalone wall improves—not merely one of the
  three.

- 2026-08-25: **The structural-head-preserving contextual projection
  experiment is also a measured negative.** This follow-up left the record's
  outer Sigma spine inline and generalized only `RecFam`/`RecTail`/`RecProj`.
  The useful refinement over the first prototype was to use contextual
  globals natively rather than Π-encoding their receiver:

  `D#proj_j : Trm_c(Delta, v : D |- Field_j(v))`.

  Thus a use was one `GlobalTm` with the checked substitution `[type
  arguments, value indices, receiver]`: no `App`, no expanded domain
  annotation, and no whole-record `El` hiding the structural head. A focused
  value-indexed-record regression proved that this path was selected (the
  earlier Π-shaped attempt had silently fallen back after a generated
  projection failed its gate). Closed records stayed on their existing,
  separately tested path.

  The default-fuel IR probe passed, but took **52.67 s** versus the roughly
  **36 s** baseline. Here the cost moved from type-code unfolding to term
  unfolding: every projected field now reaches a contextual global body by
  delta, and those forced results are not shared across the many conversion
  queries in one declaration gate. The generated-definition family therefore
  cannot by itself provide the desired abstraction. This prototype was also
  reverted.

  The evidence now points at the normalization boundary: either cache forced
  contextual global instances across a whole kernel gate, keyed by the
  global and its local substitution in a scope-safe way, or introduce a local
  core sharing form whose normalization result is memoized. Repeating the
  experiment with another global-definition shape is not warranted until one
  of those exists.

- 2026-08-25: **Gate-local contextual-global caching does not rescue that
  representation.** A scope-safe prototype shared glued global values across
  all conversion premises of one public kernel check, keyed by the ambient
  context base, persistent environment identity, global, and local
  substitution. It preserved the differential conversion suite. The IR probe
  nevertheless remained at **51.32 s** (and **48.74--51.07 s** under two
  lookup refinements), essentially the contextual-projection experiment's
  52.67 s rather than the 36 s baseline.

  Instrumentation explains why. Individual gates accumulated as many as
  **41,647 distinct instances** (with 21,720 hits), and several others held
  6,000--14,000. Restricting entries to unfoldable definitions did not change
  that shape; bucketing by global removed unrelated structural comparisons
  but did not move wall time. The workload is not repeatedly asking one
  normalization question: it builds many genuinely different substitutions.
  The cache prototype was therefore removed rather than making kernel fuel
  accounting and memory retention more complicated for no measured gain.

- 2026-08-25: **Naming only contextual tails is also a negative.** A hybrid
  kept native `fst`/`snd` projection terms but used the registered contextual
  `RecFam` definitions only in their dependent `snd_ty` annotations. It
  compiled and passed the earlier focused path checks, but the unchanged IR
  test ran beyond two minutes and was stopped. Mixed compact/structural types
  still force every named tail to expose its next Sigma head during
  conversion, recreating the suffix normalization that the spelling was
  meant to avoid.

  These three negatives identify the useful granularity more tightly: keep
  the *entire* Sigma spine structural and native, and consider naming only
  individual field types. A contextual `D#field_j` can abstract over the
  declaration parameters and preceding field values; its occurrence is an
  `El(GlobalTm)` in the `fst` slot, while the surrounding Sigma tail remains
  visible. That should avoid both structural-head loss and delta-based term
  projection, and is the next warranted experiment.

- 2026-08-25: **Contextual field-type codes preserve the right heads but are
  still a negative.** The prototype registered
  `D#field_j : Trm_c(Delta, tag, f0, ..., f_{j-1} |- Ty l_j)` and rebuilt an
  instantiated record as the same fully visible Sigma spine with only each
  payload `fst` type replaced by `El(D#field_j[...])`. Native `fst`/`snd`
  remained native. The value-parameter suite's 14 tests, including its
  propositional capture observers, passed after correcting a source-context
  depth bug.

  The IR target nevertheless exceeded its **4 GiB** test-process limit after
  23--27 seconds. Two suspected interface copies were removed without
  changing that verdict: later generated-definition contexts used the earlier
  compact field types, and closed type arguments reused their existing
  `TyCode` term rather than re-quoting (notably `M = Ir`). The residual is
  inherent to the explicit telescope spelling. A later field reference's
  substitution contains all preceding field variables; dependent Sigma
  projection eagerly substitutes growing `fst(snd^i r)` terms for those
  variables in every later reference, copying the projection annotations into
  the substitutions themselves. This is the original growth mechanism moved
  one node inward, not removed. The prototype was removed.

  The next representation-level candidate is consequently an **explicit
  local-substitution suspension** (or an equivalent locally shared type
  thunk): retain `S[delta]` as a compact core node and have NBE compose its
  environment lazily, instead of `Type::apply_local` materializing `delta`
  through the entire annotation. Unlike a global code, the suspension exposes
  the structural `S` when demanded without delta-unfolding a definition, and
  unlike a field-code telescope it does not copy `delta` into every nested
  global reference. This changes core syntax and substitution metatheory, so
  it should receive a design pass before a kernel prototype.

- 2026-08-25: **The first explicit local-substitution suspension prototype is
  inconclusive: its final representation was a genuine DAG, but the syntactic
  reducer still had an eager escape hatch.** The prototype added an
  administrative core type `S[delta]`
  with a checked target context, value-evaluator interpretation by environment
  composition, one-layer structural Sigma exposure in the syntactic oracle,
  eager erasure at staging boundaries, and distinct cache syntax. The record
  projection fallback walked the original telescope and retained the growing
  substitution in each native `fst`/`snd` annotation.

  A flat `LocalSubst` payload first exhausted the test process's **4 GiB**
  limit in 49--90 seconds even when all kernel gates were bypassed. Boxing the
  suspension payload did not help: the substitution's term `Vec` was still
  cloned into every telescope prefix. A persistent snoc spine likewise
  exhausted 4 GiB after **81 seconds**, because each dependent annotation
  still eagerly shifted the retained prefix. The final representation made
  `Concrete`, `Extend`, and `Shift` persistent expression nodes, so cloning,
  extension, and dependent lift were all O(1). A diagnostic that panicked on
  the first materialization proved no suspension was forced until **80.27
  seconds** into probe elaboration; the first force was `step_type` exposing a
  terminal field for application elaboration. Without the diagnostic, the
  construction-only run still exhausted 4 GiB after **120 seconds**.

  The backtrace changes the interpretation of that last failure. `step_type`
  forced the suspension through its generic non-Sigma fallback, which called
  eager `apply_local`; the projected field was function-typed (the call came
  from applying a projected law), while the prototype only preserved
  suspension through a Sigma head. Materializing the accumulated `Shift` DAG
  recursively shifts projection terms whose annotations contain older
  suspensions, collapsing the shared graph back into duplicated syntax. The
  4 GiB result therefore measures that eager fallback, not an inherent cost of
  carrying the final DAG. The kernel prototype and diagnostic changes were
  removed, but it is not evidence that explicit suspension itself fails.

  A conclusive retry must have no such escape hatch on the elaborator's WHNF
  path: at minimum push suspension structurally through Pi as well as Sigma,
  retain local composition/lift as DAG nodes when an application substitutes
  into the codomain, and let NBE evaluate the substitution expression directly
  rather than first materializing syntax. Other type heads should either get
  analogous one-layer rules or a deliberately bounded force whose cost is
  measured. Only after that version reaches the gate can it be compared with
  the 36-second baseline. A compact record-projection/core-let remains the
  next alternative if a fully lazy suspension still retains too much mass.
- 2026-09-06: Family (2), measured on the five-node FunctionIR/x86 module by [[inductive-spelling-codes-nonrecursive]]'s round (dev profile, furnace): after that round, what remains of the module's typing-seam conversion misses is this family — a value-indexed record instance (`BitVec(64)`, 450 queries / 0.66 s), a record's function-typed field (`Gprs.at : Gpr → BitVec(64)`, 150 / 0.40 s), a 54 K-char monomorphized sum copy (312 / 0.13 s) and the 216 K-char `MachineState<M>` instance against its boxed code literal (154 / 0.15 s) — about 1.3 s of 2.86 s kernel. Two facts for the design here: (a) the round's parameterized slice showed that a *consistent* spelling with no new definitions (respelling the arity's Case annotations with the shape in `respell_ty_deep`'s Wf arm) removed 3 s on its own, so half of what per-instantiation codes would buy is available by spelling monomorphized copies alike at every emission site first; (b) per-instantiation codes minted at a use site are unsound as a Ψ push mid-declaration (GlobalVars number from the end of Ψ), so the telescope-abstracted or pre-pass shape logged above is the only form they can take.
- 2026-09-06: The cheap half is split out to [[emission-site-respell-audit]]; this issue keeps the per-instantiation-code design question.
