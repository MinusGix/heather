---
title: trivial and decide at a closed IsTrue(b) evaluate b twice; refl at b = True evaluates it once
status: open
labels: [tactics,performance,elaboration]
area: tactics
created: 2026-10-29
updated: 2026-10-29
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
