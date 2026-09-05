---
title: Elaborator whnf probes run the small-step reducer on computing types
status: open
labels: [elaboration,performance,kernel,conversion]
created: 2026-09-05
updated: 2026-09-05
---



`Elaborator::whnf` is `reduce::whnf_type_delta`: the kernel's
substitution-based small-step reducer with every definition transparent. It
is the right tool for the questions the elaborator asks -- "is this a Π", "is
this a universe", "which inductive is this" -- as long as the answer is a few
steps away. On a type that *computes*, it is not: reducing
`El^0(Le(x, dot(row, atoms)))` unfolds `Le` at `Int` to a match on
`dot(row, atoms)`, and reaching a constructor there means evaluating the dot
product -- `dot`, `scale`, `combo`, `basis`, `zeros`, `add`, `mul` -- by
`apply_local`, each step copying the row and atom lists and recomputing their
free-variable bounds (`bounds::Cache::compute_term`, half the samples). One
such whnf cost 1-7 s on the 7-atom certificate of
[[omega-per-goal-elaboration-cost]], and the answer was always "stuck".

Two probes did this on every argument of a generated certificate and were
made cheap in that round (2026-09-05): the universe probe in the checking
fallback now skips an `El` at level 0 (no `El^0` reduces to a `Ty`), and
`ctor_here_expected` stands down on a qualified name whose qualifier names no
inductive. That removes the two paths a certificate takes; the mechanism
remains. Any remaining `self.whnf(cx, expected, …)` probe -- the `Var` arm's
erased-universe check, the expected-type harvest, `anonymous_ctor_expected`,
an *unqualified* name reaching the constructor route -- pays the full
computation whenever a proposition's head is a `fn … → Type` over a computing
argument. `Le`/`Lt` at `Int` and at `Nat` are exactly that.

## Levers, when a workload shows one of the remaining probes

- **Value-domain whnf.** The conversion checker already evaluates in the value
  domain and is not pathological on these types (the kernel gate on the same
  certificate is ~0). A `whnf` that evaluates to a value and reads back only
  the head would make every probe cheap at once. Cost: the elaborator anchors
  on *spellings* in places (`unspell_here`, `wf-shape-code-design` §3.3), so
  a readback that respells has to be audited site by site.
- **Head-shape pre-tests.** The level-0 test is one instance: decide from the
  unreduced type what the reduct *cannot* be, and skip. `expected_ind` on a
  `Type::Pi`-free `El` whose code is a `GlobalTm` application of a `fn`
  (not a lowering) is another candidate.
- **Memoize per attempt.** The same `Rc<Type>` (a lemma binder's substituted
  domain) is probed two or three times along one checking path; a pointer-keyed
  memo on `SemanticOracle::whnf_type` would bound repeats, not the first hit.

## What it assumes from elsewhere

- **[[omega-per-goal-elaboration-cost]]** owns the certificate workload that
  found this and the two probe fixes; assumed here only that its reproducer
  (`cutsat_left_cut`) exercises `Le` at `Int` over a computing row.
- **[[bounds-metadata-taxes-one-shot-checking]]** owns the bounds memo's cost
  model; assumed here only that a miss recomputes bounds over the whole fresh
  subtree, which is what makes a substitution step O(term) here.
- **[[conversion-cost-at-large-values]]** owns the value domain's constant;
  assumed here only that conversion, not reduction, is what it measures.

## Log

- 2026-09-05: Precedent for the value-domain lever: [[whnf-sharing-term-growth]] closed by moving conversion to the value machine, and its 2026-08-13 entry records a second consumer -- certgen's analyzer readback moved from reduce::whnf_term_delta to eval::Eval::force. A head-only whnf for the elaborator's probes would be the third.
