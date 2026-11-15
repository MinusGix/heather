---
title: Make a weaker-class evidence rule's projections convert cheaply at a stronger section
status: open
labels: [traits,performance]
area: language
milestone: [math-classes]
created: 2026-11-07
updated: 2026-11-07
---

Since issues/sign-rules-at-weakest-class.md the sign rules sit at their
weakest class (lib/std/algebra/ordered_sign.hthr). At an `OrderedField`
section the search is the same as when they were stated at the field
(resolve goals equal), but the probes cost about 35% more and
`conv_shortcut_hits` doubles (`scripts/perf ab --base 56a39db --whole-tree`
over `field_division_tests`'s items, 2026-11-07). The extra queries are all
in items whose proofs go through a weaker-class rule: `div_square_plus_one`
goes from 186 to 1,741, `div_product` from 104 to 967.

The likely shape: a rule's premise and conclusion speak of `A.unit`, `+`
and `*` through the upcast dictionary (`#open:…OrderedAddMonoid` applied to
the section's prefix, docs/language/classes/traits-layer2-design.md §8.1), and every
comparison with the section's own `K.unit` or a local `K.unit < b` is a
conversion that unfolds the open derivation and walks the projection path.
Confirm with `HEATHER_CONV_MISS_TRACE` or the per-item counters before
choosing a fix.

Possible fixes, cheapest first:

- Recognise an open derivation applied to the prefix, projected, as the
  stronger dictionary's own projection by path (the upcast is a record of
  the parent's fields, each a projection of the child), so the comparison
  is syntactic.
- Mint each projection of an open derivation once, as the open derivation
  is minted, so later items compare globals.

Acceptance: the field probes back within noise of a field-level statement
of the rules, by `scripts/perf ab`, with `conv_shortcut_hits` named in the
result.
