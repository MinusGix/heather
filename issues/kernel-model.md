---
title: A model of the kernel's reduction in Heather, for proving its accelerations
status: open
labels: [kernel,semantics,proofs,design,metatheory]
area: heather-in-heather
milestone: [hih-kernel-model,hih-km-runs]
created: 2026-10-24
updated: 2026-10-24
---

Model the kernel's reduction in Heather and prove, against the model, the
facts the kernel's accelerations rely on, so that an optimisation that today
is argued in a comment and checked by the differential suites (and, for the
caches, by the nightly sentinel) can be promoted to proven. Design and
ladder: `docs/kernel-model-design.md`.

## Acceptance (this issue closes with `hih-km-runs`)

- `hih-km-probe`: the fold classifier's probe argument
  (`crates/kernel/src/eval/probe.rs`) is a theorem over ch. 06's weak-head
  reduction: done, `lib/kernel_model/kernel_reduction.hthr`.
- `hih-km-runs`: iterating an affine or synchronous class over a run is the
  unary fold, with Σ and projections in the model and runs as a value
  representation.
- Both export to Lean with no refusals and pass `scripts/export-recheck`'s
  kernel route.

## Open questions

- How far the model should follow the kernel's actual machine (closures,
  glued neutrals, memoized thunks) before the native compiler can take it
  over as the evaluator (rung 5 of the ladder).
- Whether `Lc` and `Ground` should become `Bool`s with reflection lemmas
  once the fragment grows (proof terms for `Lc` of a literal grow with the
  term).

## Log

- 2026-10-24: Filed with the first round. The probe lemma holds in two
  forms: for values at every unblocked run (`Tm::whnf_inst`), and for any
  closed instantiation (the kernel's `ih` is a thunk) at settled runs
  (`Tm::whnf_inst_settled`). Both keep the fuel, which proves `probe.rs`'s
  second claim, that a probe never manufactures a verdict fuel would have
  refused. Instantiation by a value is needed only where a run ends at a
  bare atom. Controls in the tests show each hypothesis is necessary.
