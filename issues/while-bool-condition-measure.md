---
title: A Bool while condition's measure obligation is not read by omega
status: closed
labels: [language,tactics,omega]
area: language
milestone: [lang-sequencing]
created: 2026-11-02
updated: 2026-11-06
---

A `while` over a Bool condition elaborates since [[bool-conditions-and-literals]], but its measure obligation is not discharged automatically when the measure's decrease depends on the condition. Found 2026-11-02:

```
fn drain_bool(n: Nat) → Nat {
    let mut k = n;
    let mut steps = 0;
    while !k.same(0) decreases k { k := k - 1; steps := steps + 1 }
    steps
}
```

is refused: `k - 1 < k` is not proved, and the locals show `__while_h: not(same(k, 0)) = True`. The loop's equation binder is the Bool equation `b = True` (the `match h: decide_bit<c>()` the loop lowers to, with `decide_bit<c>()` read as the Bool `c`), and omega's guard round reads `b.IsTrue()` guards ([[omega-reads-bool-guards]]), not `b = True` ones; nor does it read `Nat::same` as `=`.

Either omega reads an equation `b = True` / `b = False` in scope as the guard `b.IsTrue()` / its negation (which would serve every `match h:` on a Bool, not only loops), or the loop's binder for a Bool condition is `c.IsTrue()` (the `decide<c.IsTrue()>()` evidence an `if h: c` already gets). The first is the general fix.

Done when the probe above passes without an `on ?dec := …` clause, as a probe in `lib/_tests/std/core/imperative_statements_tests.hthr`.

## Log

- 2026-11-06: Done 2026-11-06. The loop binder `!k.same(0) = True` was already read as a guard (`guard_eq_true`, the general fix the issue asks for, landed with decreases-measure-record-field-unspelled); what was missing was `Nat::same`, read as the atom `bit(same(k, 0))`. The guard round now reads `n.same(m)` as `n = m` and `!n.same(m)` as `n ≠ m` (`omega::guard_same`/`guard_not_same`, `GuardShape::Same`). Probes: `drain_bool`, `climb` and a non-decreasing control in imperative_statements_tests, `guard_same`/`guard_not_same`/`guard_eq_same` and a stuck control in omega_tests.
