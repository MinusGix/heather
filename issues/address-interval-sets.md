---
title: Address intervals and interval sets, with a packing lemma
status: closed
labels: [memory,native,order]
area: mathematics
milestone: [hih-memory-model]
created: 2026-11-09
updated: 2026-11-09
---

`lib/std/machine/memory.hthr` states span facts pointwise (`Space::Distinct`,
`Space::Apart` quantify over offsets), and each region kind re-proves that an
offset below the top is addition and that two spans are apart:
`BitVec::space_apart`/`_above`, `DataRegion::toNat_at`/`perm_from`/`allows`,
`Layout::buffer_apart` with `List::total_take_nth`/`total_take_apart`
(prefix sums by hand), `scratch_below_stack`, `Homes::Apart`,
`arena_cells_within`. About 140 citations.
`docs/native-mathematics-survey.md` §4; survey rank 4.

## Scope

- Half-open intervals `[a, a + k)` in a `Space` with a no-wrap condition:
  containment, disjointness, adjacency, split and concatenation, decided by
  endpoint comparison; `Apart`/`Distinct` as corollaries.
- Finite unions of intervals as values (sorted, disjoint) with computed
  union, intersection and difference, proved: a footprint is data.
- A packing lemma: sizes laid out consecutively from a base give pairwise
  disjoint intervals at the prefix sums (`Layout`, frames, scratch, arena).

## Done when

`Layout::buffer_apart` and `BitVec::space_apart` are instances of the
packing and disjointness lemmas, and [[wp-view-separating-product]] states
its footprints with them.

## What it assumes from elsewhere

- **[[wp-view-separating-product]]** owns the product of views. Assumed
  here: only that it needs footprints and their disjointness.
- **[[state-location-and-frame-kit]]** owns point-update laws of stores.
  Assumed here: nothing.
- **[[finite-set-membership-solver]]** closes the membership goals left
  after endpoints are compared.

## Log

- 2026-11-09: Built. `lib/std/data/set/span_set.hthr`:
    - `Span(base, len)` = `[base, base + len)`, membership the Boolean `has`
      (so closed facts are `refl`, open ones `omega` guards). `Within` and
      `Disjoint` are pointwise; `within`/`apart` decide them by endpoints,
      sound and complete (`_sound`, `_complete`), plus the client shapes
      (`disjoint_of_before`/`_after`/`_ordered`, `ordered_of_disjoint`,
      `within_of_ends`), adjacency and split (`concat_has`, `split_has`,
      `adjacent_disjoint`), `meet`, `cut`.
    - `SpanSet` = a list of spans with **no invariant**: union is `++`,
      intersection meets every pair, difference cuts by each span in turn;
      each is a Boolean identity against membership (`union_has`,
      `inter_has`, `minus_has`), so `within` (empty difference) and
      `disjoint` (empty meet) are sound and complete verdicts. Decision:
      sorted/merged normal form is not needed for any proof, so it is not
      built; it would only shrink values (nothing asks for that yet).
    - Packing: `Span::pack`, `Span::packed(base, sizes, b, size)`,
      `packed_within`, `packed_before`, `packed_disjoint`, `pack_nth`,
      `pack_has` (the union is the span of the total). `List::total` and the
      prefix-sum lemmas `total_take_nth`/`total_take_apart` moved here from
      native_compile/native_compile_facts.
  - `lib/std/machine/memory.hthr`: `Numbering<A>(space, top)` — a number per
    address that tells addresses apart and adds under offsets below `top`.
    `spans_distinct`, `spans_apart` (from a `Span::Disjoint` of the numbers),
    `outside` (an address whose number is outside a stored span is none of
    its addresses: what `wp-view-separating-product`'s locality needs).
    Instances `BitVec::numbering(n)`, `Nat::numbering(top)`.
    `BitVec::space_distinct`/`space_apart`/`space_apart_above` and the Nat ones
    are now one-line instances (new: `BitVec::space_apart_of`,
    `Nat::space_apart_of` taking any span disjointness).
  - `Layout::buffer_apart` is `Span::packed_before`; new
    `Layout::buffer_span` and `Layout::buffers_disjoint` (`packed_disjoint`).
  - Probes: `lib/_tests/std/data/set/span_set_tests.hthr` (closed verdicts,
    a footprint as a value, the packing at a literal layout, `¬` controls).
  - Survey count correction: `Homes::Apart` is register apartness and
    `arena_cells_within` a list-walk bound, not address intervals; neither is
    a client.
  - Not ported, left as they are (they work, and porting is churn without a
    new client): `DataRegion::apart`'s ordered disjunction (could take a
    `Span::Disjoint` via `space_apart_of`) and the `away` disjunction in
    `Layout::Keeps` after a store (`native_compile_region`, is
    `buffers_disjoint` pointwise).

  Automation and theory notes from the round:
    - [[omega-applied-field-atom]]: `omega` cannot spell `nb.number(a)` (an
      applied function field), so four Nat-only helpers carry the
      `Numbering` proofs.
    - [[omega-field-of-record-valued-call]]: `omega` reads `s.take(k).base`
      as an atom though `Span(a, b).base` is read; lemmas about built spans
      are stated over `Span::covers` at spelled endpoints.
    - `omega` reads every guard in scope and the branch budget is shared:
      `Span::cut_has` needed its two pieces as separate lemmas (`cut_low`,
      `cut_high`) because the hypothesis `h` (four min/max/sub splits) was in
      scope of each branch. A `clear`/focus on omega's fact set would help;
      noted, not filed (one occurrence).
    - Boolean identities over atoms are `Bool::eq_of_is_true_iff(a, b,
      λ h => omega(h), λ h => omega(h))` (new in bool.hthr, with
      `Bool::or_cong`, `and_false_r`): `omega`'s guard rounds are a truth
      table over `bit(r)` atoms. A `bool_eq` front end would drop the
      boilerplate.
    - [[span-footprint-automation]]: register span sets with `sets`, and
      find endpoint relations (`Disjoint`, `Apart`) as searched facts.

  Done-when: `Layout::buffer_apart` and `BitVec::space_apart` are instances
  (above). The footprint half belongs to [[wp-view-separating-product]],
  whose assumptions now name this library (`Numbering::outside`,
  `SpanSet::Disjoint`); nothing else is residue.
