---
title: "Dependent decidable if should convert through a definition using the same decision"
status: open
labels: [frontend,elaboration,conversion,stdlib,ergonomics]
area: language
created: 2026-08-20
updated: 2026-08-20
---

`std/int` defines `max(a, b)` as `if a <= b { b } else { a }`. Its direct
bound proof ought to use the evidence-binding form of that same conditional:

```heather
theorem le_max_l(a, b: Int): a <= max(a, b) {
    if h : a <= b { h } else { le_refl(a) }
}
```

The elaborator accepts the branches, but the kernel rejects the declaration as
`NotConvertible`. The explicit convoy over the underlying decision checks:

```heather
match le_dec(a, b) as λ d => a <= or_pick(d, a, b) { ... }
```

The same cleanup probe found an uneven boundary: evidence-binding `if` checks
for `min_le_l`, `min_le_r`, and `max_le`, but fails for `le_max_l`,
`le_max_r`, and `le_min`. This issue owns determining whether the elaborated
conditional is choosing a distinct decision term, synthesizing an insufficient
dependent motive, or failing to unfold the named branch definition during
conversion.

## Acceptance

- The three direct proofs above check with proposition-directed `if` and no
  explicit `le_dec`, `or_pick`, or written match motive.
- Both evidence-binding and evidence-free forms retain their current behavior.
- A negative control using a genuinely different decision dictionary does not
  become convertible accidentally.

## Log

- 2026-08-20: Filed from the standard-library style pass; all six candidate
  rewrites were checked against the kernel, and only the three listed forms
  failed.
