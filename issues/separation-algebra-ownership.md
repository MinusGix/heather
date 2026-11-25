---
title: Separation algebras (PCMs) for exclusive ownership
status: open
labels: [algebra,native,ownership]
area: mathematics
milestone: [nh-ownership]
created: 2026-11-09
updated: 2026-11-25
---

Memory framing does not need a separation algebra: memory is a total
function and stores keep everything outside their span, so locality of a
predicate to a footprint (dynamic frames) is enough, and
[[address-interval-sets]] with [[state-location-and-frame-kit]] give it.
Ownership does: the ownership setup wants "this function holds `xs`
exclusively" as a resource that composes, splits when a borrow is taken and
recombines when it ends. `docs/surveys/native-mathematics-survey.md` §7; survey
rank 7. File-now, build-with-the-ownership-round.

## Scope

- A partial commutative monoid class (composition defined on compatible
  elements; commutative, associative, unit), with products and pointwise
  lifting.
- Exclusive ownership of footprints as the first instance; shared read
  access as the second when a borrow needs it. No fractions until something
  is concurrent.
- A separating conjunction on predicates over a PCM and its frame theorem.

## Done when

The ownership setup's soundness theorem states uniqueness through the PCM,
and an arena allocation hands out a footprint the caller owns exclusively.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the setup and its judgment.
  Assumed here: only that it needs composable exclusive ownership.
- **[[address-interval-sets]]** owns footprints as values.

## Log

- 2026-11-24: First wave of `docs/language/ownership-design.md` §12. Two changes of scope from the direction (§10.7, §10.9): build fractions now, since a frozen view is shared read access and the parallel licence splits tokens; and the resource a token stands for is a store's value split where paths are apart ([[ownership-paths]] states `Apart`), with footprints over `SpanSet` as the memory-side instance.
- 2026-11-24: Built the algebra (docs/library/separation-algebra-design.md, the design note for this round):
  - `lib/std/algebra/pcm.hthr`: the class `Pcm<A>(≈, ∙, valid)` extending `CommMonoidRel` (laws `valid_unit`, `valid_l`, `valid_respects`); `Compatible`, `Exclusive`, `Update` with `update_frame` and `update_exclusive`; `Pcm::product` and `Pcm::pointwise` as dictionaries; `Sep` with `frame`, `mono`, `swap`, `regroup`, `respects`, `emp_intro`/`emp_elim`, `valid_parts`, `own_split`/`own_join`.
  - `lib/std/data/set/footprint.hthr`: exclusive footprints over `SpanSet` (union with a clash bit); `own_valid`, `own_disjoint`, `own_join`, `own_overlap`, `own_split`, `apart_of_valid`.
  - `lib/std/algebra/pcm_share.hthr`: fractions. Carrier: a `Rat` with a nonnegativity field, valid at most one. Why: a frozen view is copyable (§10.8), so its share must split again and again, which counting permissions cannot do for a single token; `Rat` already has `≈`, order, `linarith` and `ring`, so a dyadic carrier would add nothing; the field keeps negative shares out so a part of a valid composite is valid. `whole_exclusive`, `whole_meets_share`, `halves`, `whole_of_halves`, `take_rest`.
  - `lib/std/data/set/access_map.hthr`: the combination, a share per address (pointwise `Share`, as a record so it has a registered instance). Owned values and live paths hold `whole(s)`, frozen views `of(s, q)`; `of_disjoint`, `views_compose`, `whole_overlap` (§10.3's frozen-view obligation as a `¬`), `view_halves`, `footprint_join` (exclusive footprints map in as wholes).
  - `lib/std/machine/footprint_frame.hthr`: the bridge. `Footprint::store_keeps`: a store inside `t` keeps every predicate local to a footprint `g` with `own(t) ∙ g` valid, through any `Numbering`; `store_keeps_sep` the same read through `Sep`.
  - `span_set.hthr`: `disjoint_comm`, `union_disjoint`, `disjoint_union`, `disjoint_same`, `empty_disjoint`, union membership forms (own commit).
  Decisions: partiality as validity of a total operation (the RA presentation), laws modulo `≈`, validity an index; products and pointwise lifting are dictionary functions, not generic instances (their indices are λs instance search cannot key on). Probes in `lib/_tests` mirror each module, with `¬` theorems (overlapping owners, whole beside a half, a store under a live view, a half is not exclusive, a half cannot grow to the whole).
  Done-when: not met yet. The soundness theorem stating uniqueness through the PCM is the second wave's, and the arena handing out an exclusive footprint waits on `ownership-stores-and-keys`; the issue stays open for both. Residue filed as [[separation-algebra-paths-instance]] (the instance at a store's paths, the access-map frame theorem, a decider for `Access::Valid`).
- 2026-11-25: Second wave ([[ownership-library-join]], 2026-11-25): the instance at paths is built ([[separation-algebra-paths-instance]], closed), and an arena allocation hands out a footprint its caller owns exclusively (`Heap::alloc_owns`, `lib/native/runtime/arena_handle_paths.hthr`). What remains of the done-when is the soundness theorem stating uniqueness through the PCM, the third wave's (`docs/language/ownership-design.md` §12).
