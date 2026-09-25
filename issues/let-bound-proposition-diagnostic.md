---
title: A let bound to a conjunction type reports an arity error on And
status: open
labels: [frontend,elaboration,diagnostics]
created: 2026-09-24
updated: 2026-09-24
---

## Scope

A `let` whose value is a type-level conjunction is refused with a diagnostic
that doesn't say what went wrong:

```text
let result = FetchedSteps(fetch, data, before, after) ∧ after.rip = next_rip(…);
error: `And` takes 2 argument(s), found 0
```

The same proposition written inline in a `match … as` motive elaborates. Found
building `lib/std/arch/x86_64/fetched_code.hthr` (2026-09-24), and worked around
by inlining.

Decide whether a type-valued `let` is meant to work (it would read better in
long proofs that restate one proposition several times). If it isn't, the
diagnostic should say so rather than report an arity mismatch on `And`.
