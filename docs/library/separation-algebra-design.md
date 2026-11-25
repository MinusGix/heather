# The separation algebra: ownership as composable resources

Status: **built** 2026-11-24 (the first wave of
`docs/language/ownership-design.md` §12; issue `separation-algebra-ownership`).
What is built is the algebra and its bridge to memory; the ownership
soundness theorem that states uniqueness through it is the third wave's
(§12, "Soundness"). The algebra at paths, with a decider and the frame
theorems with a holding as the frame, was added in the second wave (§7,
2026-11-25).

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

- **Soundness.** The invariant that every live name and path reads its
  value, stated through this algebra (`docs/language/ownership-design.md`
  §12, third wave). §7 gives it the elements to state ("this path's holder
  owns it", "this view is frozen") and a frame theorem for each.
- **A decider over endpoints.** `Held::valid` checks every address below
  the last end; one over the spans' endpoints alone would cost the number of
  spans, not the largest address (`held-endpoint-decider`).

## 7. Holdings: the algebra at paths

Built 2026-11-25 (`ownership-library-join`, the second wave; issue
`separation-algebra-paths-instance`).

**The carrier** (`lib/std/data/set/held.hthr`). A `Held` is a list of
`Hold`s, each a footprint (`SpanSet`) and a share. What it holds at an
address is the sum of the shares of the holds that have it
(`Held::share_at`); that is an access map (`Held::access`), and `≈` and
validity are the access map's. Composition is concatenation, so every
class law is the access map's read through `Held::share_at_append`.

- *Why a list of holds and not `Access`.* An access map is a function,
  which evaluation cannot inspect; a holding is data. So validity has a
  decider (`Held::valid`: every address below the last end of the spans,
  past which nothing is held), sound and complete (`valid_sound`,
  `valid_complete`), and a judgment checks a closed holding by evaluation.
- *Why footprints and not paths in the carrier.* `Apart` of two paths is a
  semantic relation with no decider in general, and paths have no
  decidable equality; a carrier of paths could not decide its own
  validity. A path enters through its footprint (`PathIn`, or `KeyIn` for a
  key): its holder holds `Held::own(span)`, a frozen view `Held::at(span,
  q)`. Composition is then sound for `Apart` (`Held::apart_of_valid`: an
  owned path's holding beside any positive holding of another makes them
  apart) and not complete: footprints over-approximate, and views compose
  however they overlap, since they only read.
- *Keys* are held the same way in the address space of a store's slots,
  a key's footprint its slot (`Held::key`, `Held::keys_apart_of_valid`). A
  resource holding bytes and keys is the product of two holdings
  (`Pcm::product`).

**What a holder may say.** An owned holding leaves any validly composed
frame nothing on its footprint (`Held::own_excludes`); a whole beside a
positive view of an address it holds does not compose
(`Held::view_refuses_store`, §10.3's obligation); views compose while
their shares total at most one (`Held::views_compose`).

**The frame theorems with a holding as the frame**
(`lib/std/machine/access_frame.hthr`):

| Where | Theorem | Says |
|---|---|---|
| a path into a list | `Held::path_keeps` | the holder of `p` writes; a predicate local to the frame's positive addresses (`Held::Local`) is kept |
| the same through `∗` | `Held::path_keeps_sep` | the resource split as `≈ Held::own(span)` beside a frame |
| a frozen view | `Held::view_kept` | what reads only the view's span is kept by every write of a holder it composes with |
| memory | `Access::store_keeps`, `Access::store_keeps_sep` | `Footprint::store_keeps` with an access frame: local to the frame's positive addresses, through any `Numbering` |
| memory, a holding frame | `Held::store_keeps` | the same, the frame a `Held` (its composite with `Held::own` is the access maps' by definition) |

Each cites the algebra only for why the writer's footprint and the frame's
positive addresses are disjoint (`Share::whole_meets_share`); the rest is
the path's footprint (`PathIn::frame`) or memory's
(`Memory::get_set_span_outside`).
