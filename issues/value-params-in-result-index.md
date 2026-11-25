---
title: A constructor's result index cannot read the declaration's value parameters
status: open
labels: [elaboration,inductives,indexed-families]
area: language
milestone: [none]
created: 2026-11-25
updated: 2026-11-25
---

Found by [[reflected-languages-typed-by-construction]] (2026-11-25). A constructor's result index cannot read the declaration's value parameters:

```heather
inductive TStep<Q, P>(elem: Q → P, fst: Q → Q → P) : (st: P) → Type {
    TElem(t: Q, i: Nat) : TStep<Q, P>(elem, fst)(elem(t)),
    TFst(a: Q, b: Q) : TStep<Q, P>(elem, fst)(fst(a, b)),
}
```

is refused with "unbound name `elem`" at `elem(t)`. The value parameters are in scope in the fields' types, the children's family and the index type ([[indexed-families-at-any-index-type]]), not in a result index. With them in scope, a family over an open index type could compute its result indices from parameters, which is how a family indexed by an open type (`P := Pair<Type, Type>`) could be written; the investigation used a declared index type of type pairs instead (`lib/_tests/lang/ownership/typed_steps_tests.hthr`, `TyIx`), so nothing waits on this.

## Done when

A result index reads the declaration's value parameters, on the routes that admit value parameters, with a probe at an open index type; or the refusal names the reason.
