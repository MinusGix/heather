---
title: A model of the kernel's reduction in Heather, for proving its accelerations
status: open
labels: [kernel,semantics,proofs,design,metatheory]
area: heather-in-heather
milestone: [hih-kernel-model]
created: 2026-10-24
updated: 2026-10-25
---

Model the kernel's reduction in Heather and prove, against the model, the
facts the kernel's accelerations rely on, so that an optimisation that today
is argued in a comment and checked by the differential suites (and, for the
caches, by the nightly sentinel) can be promoted to proven. Design and
ladder: `docs/kernel-model-design.md`.

## Acceptance (closes once the Lean recheck of both modules has run)

- `hih-km-probe`: the fold classifier's probe argument
  (`crates/kernel/src/eval/probe.rs`) is a theorem over ch. 06's weak-head
  reduction: done, `lib/kernel_model/kernel_reduction.hthr`.
- `hih-km-runs`: iterating an affine or synchronous class over a run is the
  unary fold, with Σ and projections in the model and runs as a value
  representation: done, `lib/kernel_model/kernel_runs.hthr`
  (`Tm::fold_affine`, `Tm::fold_affine_peeled`, `Tm::fold_sync`).
- Both export to Lean with no refusals (done, `kernel_model_exports`) and
  pass `scripts/export-recheck`'s kernel route (round 1's module did; round
  2's is not yet run: the cloud box has no Lean and cannot fetch one).

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
- 2026-10-24: `hih-km-runs`, the second round (design §7). The fragment
  gained pairs, projections and runs (`NRun(c, t)`, unpacking one successor
  at a time), and the probe lemma was re-proved over it. Run folds are
  stated with reduction as a relation, closed under instantiation with no
  unblocked hypothesis, and the evaluator is sound for it. The probe's tree
  and synchronous readings are modelled after `read_affine` and
  `probe_sync` and proved sound, and so are `at` and `compose`. The three
  theorems: a uniform affine fold over `NRun(c, x)` joins the kernel's
  built tree at the fold over `x`; peeled, the same over the rest of the
  run after the innermost step; a synchronous fold applied to a run
  cancels the common prefix under `q` successors per pair. Open: the Lean
  recheck of the new module, and (design §7.4) programs and binary
  powering against unary iteration, and the `WfIh`/`WIh` synchronous heads.
- 2026-10-25: From `docs/definitional-inversion-survey.md` §3: injectivity
  of formers and subject reduction are provable without normalisation
  (arXiv:2607.13662), so they are not behind the Gödel limit. If the
  inversions are all that heather-coq's `AlgSound.v` takes from the
  relation, rung 4's strategy changes can be proved sound against the
  declarative rules inside Heather. Owned by
  `definitional-inversion-domain-model`.
- 2026-11-05: gardener: cites a file it shares with [[bitvec-width-generic-decision]] (`docs/kernel-model-design.md`); [[definitional-inversion-domain-model]] (`docs/definitional-inversion-survey.md`); [[generator-ctors-open-types]] (`lib/kernel_model/kernel_reduction.hthr`).
