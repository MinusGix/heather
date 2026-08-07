---
title: Multi-binder function types: (x: A, y: A) -> B, and a shared-annotation form
status: open
labels: [frontend,syntax,elaboration,ergonomics]
created: 2026-08-07
updated: 2026-08-07
---

Probed 2026-08-07: `fn f(g: (x: Nat, y: Nat) -> Nat)` fails to parse at the comma — a surface function TYPE takes exactly one binder per arrow, so class fields and higher-order parameters write `(x: A) -> (y: A) -> (z: A) -> …` (see lib/std/algebra.hthr's law fields). Application is already fine: `op(op(x, y), z)` and `le(x, x)` both check against curried types.

Two additions, one decision:

1. **`(x: A, y: B) -> C`** — comma-separated binders in one arrow group, desugaring to the curried Π chain. Pure parser sugar; later binders' types may mention earlier ones (it is a telescope).
2. **Shared annotation** for same-typed runs. Candidates: Lean's juxtaposition `(x y z: A)` — works only because parameter modifiers (`self`) are keywords, so it is fragile against new modifiers and reads as application in other positions; or the comma form `(x, y, z: A)` — names separated by commas, one trailing annotation, consistent with the language being comma-separated everywhere else and unambiguous against modifiers (a modifier still prefixes a single name: `(self x: A, y: A)`). Leaning comma form (user + assistant agreement 2026-08-07); the same sugar should apply in fn/theorem parameter lists, not only in types.

Cleanup rider when this lands: normalize algebra.hthr's law spellings (also switch the one curried `le(x)(x)` to `le(x, x)` now — supported today).
