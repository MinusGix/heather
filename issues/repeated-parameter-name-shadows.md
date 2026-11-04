---
title: A repeated parameter name in a signature silently shadows the earlier one
status: open
labels: [frontend,elaboration,bug]
area: language
created: 2026-10-29
updated: 2026-10-29
---

A declaration may name the same value parameter twice, and the later one
silently shadows the earlier:

```
fn dup(x: Nat, x: Nat) → Nat { x }   // accepted
```

Probe on master 4f0ac27 ([[proof-patterns-audit-2026-10]]). The sections
round found it and refused it only inside a section splice
([[section-spliced-heads]], 2026-10-26); the ordinary signature still
accepts it. A caller sees a two-argument function whose first argument is
dead, and an `x := …` named argument is ambiguous.

## Acceptance

- A repeated parameter name in one signature (value, implicit, or `self`)
  is refused at the second binder, naming the first.
- `heather check lib` stays green (nothing in the library repeats one
  today, which the change will confirm).
