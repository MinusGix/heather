---
title: Let a generated declaration cite an earlier member of its group
status: open
labels: [metaprogramming,elaboration]
area: tactics
created: 2026-10-28
updated: 2026-11-12
---

A `generate` publishes its declarations only after the generator's run ends
(docs/host-elaboration-interface-design.md §19), so no member can cite an
earlier member of the same group: `Lookup` does not find a name that is not
published yet, and there is no `Expr` for "the declaration this run will
publish as `T::cong_App`". A group whose later lemmas use earlier ones (a
lemma and its corollary, an equation lemma and the congruence built on it)
has to be split over several `generate`s today, which loses the
all-or-nothing publication.

## Acceptance

- A member can refer to an earlier member of its own group by a typed
  reference the run issues (not by name), checked against that member's
  statement.
- The group still publishes all or nothing; a refused earlier member is
  reported as the cause, not the later member that cited it.
- A probe in `lib/_tests/std/tactic` where the second member's body cites the
  first, and a negative control citing a member that is refused.

## Log

- 2026-10-31: `tac-host-interface` is marked done in docs/roadmap.md (its "done when" is met), so this issue no longer serves it; it stays open in area `tactics` with no milestone.
- 2026-11-01: A customer (2026-11-01): `regex def is_hex` (lib/std/text/regex/regex.hthr) inlines its term in both `is_hex` and `is_hex::term` because `is_hex` cannot be defined as `is_hex::term.accepts` within one group ([[regex-dfa-compiler]]).
- 2026-11-12: One more cost of this (2026-11-12): a `runtime fn`'s group now publishes `f::sourced`, the proof that every function of its program evaluates to its source (`docs/native-library-exports-design.md` §6.3). `f::agrees` is that proof read at the last function, and since it cannot cite `f::sourced` it carries the proof again, so the kernel checks the linking proof twice for every `runtime fn`. With references inside a group, `f::agrees` would be one application of `f::sourced`.
- 2026-11-12: A fourth customer (2026-11-12, PR #551): `generate laid(T, [codec, …]);` (`lib/std/machine/laid.hthr`, `docs/layout-design.md` §6.2) publishes `T::stored()` and one `T::f_part()` per field, and a part's type is `Part<T, B>(T::stored())`. A member cannot cite `T::stored`, so each part's type and body carry the record's codec written out again, which makes the group's text quadratic in the number of fields and prints the whole codec in a diagnostic. This customer needs more than a typed reference: the part's body has type `Part<T, B>(fields.record(…))`, which is the statement only if the reference **unfolds** to the earlier member's body during the run's check. A reference that is opaque in the run (enough for a theorem citing a theorem, as `f::agrees` citing `f::sourced`) would refuse it.
- 2026-11-12: A second place the missing reference costs: the generator of a function of a laid record publishes `T::m::bytes`, its instance, its program and three theorems, and every one after the first names the written function and the instance in full, as holes. In the kernel each declaration then carries its own copy, and two copies compared are walked ([[conversion-proof-compared-at-computed-type]]). With a member citable by name, each mention would be a name and the comparison one step. `HWorld::written` (rt_held.hthr) exists only to give the kernel a name to meet at in its place.
