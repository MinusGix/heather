---
title: Add concise term introduction syntax for conjunction
status: closed
labels: [surface,syntax,logic,ergonomics]
created: 2026-08-30
updated: 2026-08-30
---

Heather has the obvious proposition spelling `P ∧ Q`, but constructing its
proof still requires the record constructor `And(p, q)`. Nested structural
certificates therefore contain terms such as:

```text
And(And(p, trivial), And(trivial, trivial))
```

even when their type is written with ordinary conjunction syntax. The first
hybrid FunctionIR validity certificate made this asymmetry conspicuous.

Design concise introduction syntax that remains visibly a term, composes for
nested conjunctions, and does not conflict with Boolean `&&` or proposition
type parsing. Pattern/elimination spelling should be considered at the same
time so introduction does not become a one-off special case.

Acceptance should include the `add64_valid` input-uniqueness proof in
`lib/native/function_ir/function_ir.hthr`, a nested three-or-more-field conjunction, and parser
controls distinguishing term introduction from `P ∧ Q` and Boolean `a && b`.

## Resolution

Resolved 2026-08-30 with expected-type-directed anonymous constructor syntax.
`⟨p, q⟩` selects the sole constructor, so it covers `And`, `Exists`, and
ordinary records; `⟨p |⟩` / `⟨| q⟩` select the first / second
constructor of an exactly binary sum, covering `Or` and other two-constructor
types. The same forms work as match patterns. They lower through the existing
constructor and pattern machinery and add no kernel form. The complete syntax
and shape restrictions are recorded in `docs/logic-connectives-design.md`
§4.1.
