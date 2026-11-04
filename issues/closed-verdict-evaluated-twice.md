---
title: trivial and decide at a closed IsTrue(b) evaluate b twice; refl at b = True evaluates it once
status: closed
labels: [tactics,performance,elaboration]
area: tactics
created: 2026-10-29
updated: 2026-11-02
---

A closed `Bool` verdict proved as `b.IsTrue()` by `trivial` or `decide`
costs about twice the same verdict proved as `b = True` by `refl`, because
the elaborator evaluates `b` before the kernel evaluates it again. At native
scale the difference is not a constant: on cat FILE's certificate (PR #247)
`trivial` against `IsTrue(…)` passed 12 GiB where `x = True { refl }` cost
about 0.6M steps, and the interval tactic's `IsTrue` verdicts ran out of
*elaborator* fuel (PR #208). Every round since PR #21 has had to learn
"closed facts by `Bool = True` refl" by hitting it.

Probe on master 4f0ac27 ([[proof-patterns-audit-2026-10]]), one cold item
each, width 1:

```
fn heavy(k: Nat) → Bool { List::range(k).map(λ i => i * i).len().leb(k) }
theorem t1(): heavy(300).IsTrue() { trivial }   // 587 ms total, 303 ms gate, 527K steps
theorem t2(): heavy(300) = True { refl }        // 263 ms total, 263 ms gate, 231K steps
theorem t3(): heavy(300).IsTrue() { decide }    // 521 ms total, 226 ms gate, 527K steps
```

`trivial` goes through `check_unit_form`, which reads the expected type in
the elaborator (`read_expected_type`, so a whnf of `IsTrue(heavy(300))`).
`decide` is `decide_yes(refl)` but resolves the `Decide` instance and
spells its `refl` against the evaluated goal first.

## Wanted

The elaborator records and the gate decides, as `refl` already does: at an
expected type that is a closed `IsTrue(b)` (or another `Decide`-instance
goal), `trivial`/`decide` should emit the proof without evaluating `b`
themselves, leaving one evaluation to the kernel. A refused verdict still
needs its located message, so the failing path may evaluate (the
REFL_NOTE_FUEL probe is the model).

## Acceptance

- `t1` and `t3` cost what `t2` costs in kernel steps and within noise in
  total time, measured with `scripts/perf ab`.
- A false closed verdict proved by `trivial` and by `decide` still reports
  at the call, pinned in lib/_tests.
- docs/proof-patterns.md's "closed facts" entry is relaxed to say any of the
  three spellings is fine.

## Log

- 2026-11-02: Fixed (branch claude/project-thread-kmbaz4). Two elaborator reads were running the verdict:

  - `trivial` (`ExprElab::check_unit_form`) read its expected type with the full fuel. It now reads it within `diagnostics::VERDICT_READ_STEPS` (4,096 steps, `UnitCheckingElab::read_expected_type_within`). Past that budget it emits `⟨⟩` at the expected type's own level, unread, and records a `TrivialUse`. When the gate refuses with `NotConvertible`, `Elaborator::refused_trivial` reduces the recorded type under the gate's budget and reports at the `trivial`, which is how `refused_decide` already worked.
  - `decide` was not slow inside `decide` itself. The cost was the general harvest in `solve_from_expected`: `decide_yes(refl)`'s result `P` was solved by the syntactic unification, and the harvest then whnf'd the expected type anyway. That read is now skipped once the result type mentions no unsolved meta (`zonked(result_ty)`). Unification records only into the pattern's metas, so at that point the read could learn nothing.

  `scripts/perf ab --file` over the issue's probe, 5 cold samples at width 1: t1 went from 461,796 to 234,996 eval steps, t3 from 461,878 to 230,982, and t2 stayed at 230,921. Across the file, `eval_steps` fell 36%, and total time was −13.5% with the samples separate. In `docs/showcase/calc_parser.hthr` (the quick corpus), `unify_calls` fell 29.5% (the harvest's skipped reads), `syntax_eq_nodes` rose 1.3% (the `zonked` test), and seconds did not change.

  `decide` now matches `refl` within noise. `trivial`'s kernel check still costs about a fifth more gate time than the `refl` at the same steps. That is a kernel cost of converting `⟨⟩` against a computed type, filed as [[kernel-unit-against-computed-type-cost]].

  The probes and the false-verdict controls are in `lib/_tests/std/core/closed_verdict_tests.hthr`. A false verdict past the budget is reported at the `trivial` ("`trivial` proves `True`, but `IsTrue(heavy_false(300))` is expected here, which reduces to `False`") and at the `decide` (with its instance named). Below the budget, `trivial` keeps its elaborator message. `docs/proof-patterns.md` §1 now says any of the three spellings is fine.

  One place could not leave the verdict to the gate: a literal's embedding is reduced before it is emitted (`reduced_embedding`), and `HexLiteral`'s `ofHex` never reads its `trivial`, so the reduct drops the `⟨⟩`, and an unrepresentable hex float would have been accepted with nothing checking it. Literal elaboration now decides every `trivial` it deferred, before reducing (`settle_deferred_units`). `literal_tests`' `hex_too_precise` is the pin: it caught the gap on the first suite run. Any other elaborator route that emits a reduct of a written term in place of the term itself would need the same treatment.

  A change in what gets reported: a verdict too expensive for the gate's fuel is now the kernel's `OutOfFuel` at the declaration, as a `refl` at `b = True` already was. Before, it was the elaborator's "out of fuel reducing a type" at the call.
