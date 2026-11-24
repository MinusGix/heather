# The separation algebra: ownership as composable resources

Status: **built** 2026-11-24 (the first wave of
`docs/language/ownership-design.md` §12; issue `separation-algebra-ownership`).
What is built is the algebra and its bridge to memory; the ownership
soundness theorem that states uniqueness through it is the second wave's
(§12, "Soundness").

Read with: `docs/language/ownership-design.md` §10.3 (three kinds of
access), §10.7 (tokens are the store split where paths are apart), §10.9
(footprints as values, tokens that split); `docs/surveys/native-mathematics-survey.md`
§7 (why memory framing alone needs no separation algebra and ownership
does); `docs/library/relation-indexed-algebra-design.md` (the `≈`-indexed
classes this extends).

## 1. The class

```heather
class Pcm<A>(same as ≈: A → A → Type, op as ∙: A → A → A, valid: A → Type)
    extends CommMonoidRel<A>(same, op)
{
    valid_unit: valid(unit),
    valid_l: (x, y: A) → valid(x ∙ y) → valid(x),
    valid_respects: (x, y: A) → x ≈ y → valid(x) → valid(y),
}
```

`lib/std/algebra/pcm.hthr`. Decisions:

- **Partiality is validity.** The operation is total and `valid` says which
  composites are real; two elements are compatible when their composite is
  valid (`Pcm::Compatible`). This is the resource-algebra presentation
  (Iris's RA without a core). The alternative, a compatibility relation
  indexing a partial operation, needs a three-way side condition in every
  associativity law; with validity, associativity is the monoid's and
  downward closure (`valid_l`) carries the rest.
- **Laws are modulo `≈`.** Footprints are `SpanSet`s, which are lists of
  spans, and fractions are rationals, which are unreduced; neither has
  `=` as its equality. So the class extends `CommMonoidRel` and inherits
  `Equivalence`, `Respects2`, associativity, commutativity and the unit
  from it. A client cites `A.assoc`, `A.comm`, `A.unit_l` as at any
  relational monoid.
- **Validity is an index**, as the relation and the operation are: one
  carrier and operation with two validities (bounded and unbounded shares)
  are two structures.
- **Products and pointwise lifting are dictionaries** (`Pcm::product`,
  `Pcm::pointwise`), functions from the parts' instances to the whole's,
  rather than registered generic instances: their indices are λs over the
  parts' indices, which instance search has no head to key on. The
  combination that clients name (`Access`, §4) is a record with a registered
  instance.

Derived: `valid_r`, `compatible_symm`, `compatible_unit`, `valid_inner`,
`valid_outer`, `op_cong`; `Exclusive(x)` (only the unit composes with
`x`); `Update(x, y)` (every frame valid beside `x` is valid beside `y`), with
`update_refl`, `update_trans`, `update_frame` (an update of a part is an
update of the part beside anything) and `update_exclusive` (an exclusive
element may become any valid one).

**The logic.** `Sep<A>(≈, ∙, P, Q, r)` is the separating conjunction, a
record of the split (`left`, `right`, `parts: left ∙ right ≈ r`, `holds_l`,
`holds_r`). Validity is not part of it; `Sep::valid_parts` reads it back
from a valid whole. `Sep::frame` and `Sep::mono` need nothing of the
carrier; `Sep::swap`, `Sep::regroup`, `Sep::respects`, `Sep::emp_intro`,
`Sep::emp_elim` (for a predicate that `Sep::Respects` `≈`), and
`Sep::own_split`/`own_join` (owning a composite is owning each part) use the
class. Predicates are `A → Type` and stated pointwise, so no entailment
type and no function extensionality appear.

## 2. Exclusive footprints

`lib/std/data/set/footprint.hthr`. A `Footprint` is a `SpanSet` and a clash
bit; composition is the union, clashing when the two share an address
(`SpanSet::disjoint`, the decider); valid means nothing clashed.
`≈` compares the clash bit and the members. `own(s)` is a clash-free
footprint. The laws the ownership design cites:

- `own_valid`/`own_disjoint`: owned footprints compose exactly when they are
  disjoint, `own_join`: to the owned union, `own_overlap`: two claims on one
  address do not compose, `own_split`: a footprint splits along any cut
  (`s ∩ t` and `s \ t`), the callee's part and the caller's rest.
- `apart_of_valid`: the parts of any valid composite are disjoint.

The clash bit, not an `Option`, makes composition total with no case on
the operands; the clash identities are Boolean identities over the pairwise
disjointness verdicts (`regroup_bits`), which `SpanSet::union_disjoint` and
`disjoint_union` instantiate.

## 3. Fractions

`lib/std/algebra/pcm_share.hthr`. A `Share` is a rational with a field that
says it is nonnegative; shares add, and a share is valid at most one.

**Why rationals.** A frozen view is copyable (§10.8), so its share must split
again and again: a copy of a copy is a quarter. Counting permissions (a
source lending `n` unit tokens) cannot split a token, so a view could not
be copied by its holder. Dyadic shares would split, but `Rat` already has
`≈`, its order, `linarith` and `ring`, and a dyadic carrier adds nothing a
client needs. The nonnegativity is a field so that no element of the carrier
is negative: without it `valid(a ∙ b) → valid(a)` fails (`-1/2 + 1`).

Laws: `whole_exclusive`, `whole_meets_share` (no positive share composes
with the whole), `halves` (two halves are the share), `whole_of_halves`,
`take`/`rest`/`take_rest` (split at any covered amount), `half_valid`,
`shares_compose`. `Share::valid` decides validity, with `valid_sound` and
`valid_complete`.

## 4. The combination: an access map

`lib/std/data/set/access_map.hthr`. An `Access` is a share at every address:
the pointwise lifting of `Share`, as a record. §10.3's three kinds are
holdings in one algebra:

| Access | Holding | Composes with |
|---|---|---|
| owned value, live path | `Access::whole(s)` | holdings of disjoint footprints |
| frozen view | `Access::of(s, q)`, `q` a share | views of any footprint while shares total ≤ 1; nothing whole on its footprint |

`of_disjoint`, `views_compose`, `whole_overlap` (a store cannot overlap a
live frozen view: §10.3's obligation), `wholes_overlap`, `view_halves` (a
copied view), `whole_of_halves`, `of_join`, `of_same`, `of_valid`. Exclusive
footprints map in as wholes (`of_footprint`) and compose the same way
(`footprint_join`, `footprint_valid`): the two algebras agree on owned
memory.

Why a pointwise map and not `Footprint × Share`: the product composes
footprints by disjoint union, so two halves of one buffer (the same
footprint) would clash. The map composes shares address by address.

## 5. The bridge to memory

`lib/std/machine/footprint_frame.hthr`. `AgreesOn(nb, s, m, n)`: two memories
agree on the cells numbered in `s` (through a `Numbering`, so naturals and
words below their top). `Footprint::Local(nb, s, Q)`: `Q` reads only `s`.

- `Footprint::store_agrees`: a store whose span is apart from `s` keeps `s`'s
  cells.
- `Footprint::store_keeps`: **the frame theorem.** The owner of `t` stores
  inside `t`; every `Q` local to a footprint `g` with `own(t) ∙ g` valid
  holds after the store if it held before.
- `Footprint::store_keeps_sep`: the same with the resource given as
  `Sep(≈ own(t), P)`, any frame `P` whose holder's predicate is local.

The algebra's part is only the reason the footprints are apart; memory's
part is `Memory::get_set_span_outside` and `Numbering::outside`.

## 6. What is not here

- **Stores and keys as the resource** (§10.7: a token is the store's value
  split where paths are apart). Paths and `Apart` are `ownership-paths`'s;
  the instance of `Pcm` at a store's paths waits on them
  (`separation-algebra-paths-instance`).
- **The access map against memory**: a frame theorem stated with an
  `Access` frame (local to the addresses where the frame holds a positive
  share) rather than a `Footprint` one, and a decider for `Access::Valid` of
  holdings built from finitely many footprints. Filed with the paths
  instance; nothing needs them before the soundness round.
- **Soundness.** The invariant that every live name and path reads its
  value, stated through this algebra (§12, second wave).
