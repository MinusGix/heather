---
title: Decide span footprints by sets and search endpoint relations
status: closed
labels: [sets,memory,tactics,native]
area: tactics
milestone: [hih-memory-model]
created: 2026-11-09
updated: 2026-11-10
---

Address footprints are values since [[address-interval-sets]]
(`lib/std/data/set/span_set.hthr`): `Span`, `SpanSet` with union,
intersection and difference proved against membership, and verdicts
`within`/`disjoint`/`apart` that are sound and complete. Two pieces of
automation would let a client stop citing lemma names for them.

1. **The `sets` tactic over span footprints.** `sets`
   ([[finite-set-membership-solver]]) decides membership goals over lists
   read as sets, by a truth table over atoms. A span set's membership is a
   Boolean (`a.has(x)`), and its operations already have Boolean laws
   (`SpanSet::union_has`, `inter_has`, `minus_has`), which is the shape of
   a `SetBitEntry`/`SetOpEntry` registration
   (`lib/std/data/set/set_ops.hthr`). Registering `SpanSet::has` as a
   membership spelling and `union`/`inter`/`minus` as operations, and
   `within`/`disjoint` as `SetRelEntry`s (their `_sound`/`_complete` laws
   are the elim/intro pair), lets `by sets()` close a footprint goal
   mixing named footprints, while a closed one is still `refl`. Open
   question: `sets` reads membership in a *list*; a span-set membership is
   about a number, so the registry entry needs an element type of `Nat`
   with the set an arbitrary `SpanSet`, not a `List<Nat>`.
2. **Endpoint relations as searched facts.** `Span::Disjoint(s, t)` and
   `Within` with open endpoints are `apart_sound(omega(...))`, every time.
   As an evidence rule ([[facts-on-demand]]) or a `by spans()` that
   reduces to the verdict and runs `omega` on it, a premise
   `buffer_span(b).Disjoint(buffer_span(c))` would be found, not cited.
   The same holds for `Space::Apart`/`Distinct` in a numbered space
   (`Numbering::spans_apart` at the numbers' verdict).

## Done when

A probe in `lib/_tests/std/data/set/span_set_tests.hthr` proves a footprint
inclusion over atoms (`a.union(b).Within(a.union(b).union(c))`) with `by
sets()`, and an open `Span::Disjoint` premise with endpoints in scope is
found without naming `apart_sound`.

## Log

- 2026-11-09: part 1 done by [[sets-any-carrier]]. `sets` reads any carrier
  with a `DecSet` instance; `Span` and `SpanSet` declare theirs
  (`span_set.hthr`), and `span_set_rels.hthr` registers `within`,
  `apart` and `disjoint` as relations. `a.union(b).Within(a.union(b).union(c))`
  is `within_sound(…, by sets())` in
  `lib/_tests/std/tactic/set_tactic_tests.hthr` (`span_footprint_within`).
  Part 2 (endpoint relations as searched facts) stays open.
- 2026-11-10: part 2 done; closed. Search rules (`h: … := omega`,
  docs/facts-on-demand-design.md §3) produce the endpoint relations:
  `Span::disjoint_by_ends`/`within_by_ends` (span_set.hthr) answer a
  `s.Disjoint(t) := infer`/`s.Within(t) := infer` premise by the verdict and
  `omega` over the asker's hypotheses; `BitVec::space_distinct_by_ends`,
  `space_apart_by_ends` and `Nat::space_apart_by_ends` (memory.hthr) answer
  `Distinct`/`Apart` in the two numbered spaces by the numbers' verdict and
  the fits below the top, and `Nat::space_distinct_always` is a plain rule.
  Probes (closed, open at constructed spans and at span variables, a literal
  width, negative controls for an overlap, an unknown order and a missing
  fit) in `lib/_tests/std/data/set/span_set_tests.hthr` and
  `lib/_tests/std/machine/memory_tests.hthr`. Not done: a generic rule over
  any `Numbering` (the numbering is not in the goal, so a rule cannot find
  it); spans whose endpoints are a call's fields
  (`layout.buffer_span(b, cap)`) still need hypotheses spelled at those
  atoms until [[omega-field-of-record-valued-call]].
