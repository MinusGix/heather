---
title: omega reads f(x).field as an atom when f(x) unfolds to a constructor
status: open
labels: [omega,proofs,ergonomics]
area: tactics
milestone: [none]
created: 2026-11-09
updated: 2026-11-09
---

`omega` reads `f(x).field` as an opaque atom when `f(x)` is a call whose
definition is a record constructor, though it reads `Ctor(a, b).field`
(a constructed record) as its component:

```text
// lib/std/data/set/span_set.hthr
fn Span::take(self s: Span, k: Nat) → Span { Span(s.base, s.len.min(k)) }
theorem ctor_field(a, b, x: Nat, h: x < Span(a, b).base): x < a { omega(h) }        -- ok
theorem call_field(s: Span, k, x: Nat, h: x < s.take(k).base): x < s.base { omega(h) } -- stuck, atom take(s, k).base
```

Found building [[address-interval-sets]]: every Boolean identity about a
span built from others (`Span::meet`, the pieces of `Span::cut`, `take`,
`drop`) had to be stated over `Span::covers(base, len, x)` at the spelled
endpoints and left to the kernel to convert to `built.has(x)`; and a
footprint lemma over a computed `SpanSet` meets the same wall one level up.

Shape of a fix: when a projection's receiver is a call that δ-unfolds (one
reduct at a time, as §17 unfolds a Bool guard head,
docs/omega-measure-reduction-design.md) to a constructor, read the
component; keep the atom when it does not.

## Done when

`call_field` closes, and `Span::meet_has`/`split_has` state their
`Bool::eq_of_is_true_iff` over `has` of the built span.
