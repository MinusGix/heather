---
title: ring and linarith refuse an atom that mentions the class carrier's own constants
status: closed
labels: [tactics,proofs,ergonomics]
area: tactics
milestone: [tac-arith]
created: 2026-10-31
updated: 2026-11-01
---

At a section's class carrier (`section<K: OrderedField(≈, <, <=, +, *)>`),
`ring` (and `linarith` when it calls `ring` for its certificate) refuses
with "`ring` wrote an atom list that does not parse: unexpected character
'#'" when an atom's term mentions the dictionary itself. The atom is
spelled with the elaborator's placeholder (`#constraint0`, `#op*@0_4`), and
the atom list is re-read as text:

```heather
// lib/std/analysis/real_fn.hthr defines OrderedField::half(e) = e * recip(1 + 1, …)
section<K: OrderedField(≈, <, <=, +, *)> {
theorem t(d: K, s: OrderedField::half(K.multiplicative.unit) + OrderedField::half(K.multiplicative.unit) ≈ K.multiplicative.unit):
    OrderedField::half(K.multiplicative.unit) * d + OrderedField::half(K.multiplicative.unit) * d ≈ d
{ ring(s) }   // atom list: list::Cons(real_fn::OrderedField::half(#constraint0.multiplicative.unit), …)
}
```

Three shapes met in the real-functions round:

- an atom applied to a class constant, as above (`half(K.multiplicative.unit)`);
- the witness of an `∃` whose producer takes class constants
  (`hd(OrderedField::half(K.multiplicative.unit), …).witness`);
- a range product `∏ j < n, x` at `K`: its operation argument is spelled
  `#op*@0_4`.

The workaround is to generalize the atom away: name it as a lemma
parameter (`t: K` with `t + t ≈ 1`), or wrap the product in a named
function (`OrderedField::npow`). Both are in
`lib/std/analysis/real_fn.hthr` and its tests.

Shape of a fix: [[ring-field-read-atom-spelling]] already names atoms that
do not spell by an alias bound to the term (`__ring_a{i}`); the class
placeholder spelling should take the same route instead of reaching the
text.

A second reading gap of the same family: `linarith` reads `A.inv(e)` inside
a predicate defined in a parent class's section (`AbsLe`, from
`OrderedAddGroup`) as an opaque atom (`…`), because the negation is reached
through the parent dictionary's projection path rather than `K.inv`. The
workaround is to restate the hypothesis with a `let l: (K.inv(e) <= z) =
h.left;` ascription.

## Log

- 2026-11-01: The three `ring` shapes already checked on master: the
  difference-calculus round (PR #332) names an atom whose spelling does not
  parse by an alias, the route this issue proposed. The `linarith` gap is
  fixed here: ring's reifier compares a dictionary operation through a
  parent class's record (`same_dictionary_read`, docs/casting-design.md
  §16), so `AbsLe(z, e).left` reads as `-e <= z`. The `let l: (K.inv(e) <=
  z) = h.left` ascriptions in `real_fn.hthr` and the named half in
  `real_fn_tests.hthr` are gone; probes in `real_fn_tests.hthr`
  (`class_constant_…`, `class_range_product`) and `linarith_tests.hthr`
  (`class_parent_…`).
