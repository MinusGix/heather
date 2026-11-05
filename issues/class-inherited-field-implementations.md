---
title: A child class implements inherited fields from its other fields
status: open
labels: [traits,classes,ergonomics,design]
area: language
milestone: [math-classes]
created: 2026-10-23
updated: 2026-11-02
---

From the Arend survey (`docs/arend-survey.md` §4). Arend's records support
**partial implementations**: a class that extends another can implement some
of the parent's fields, so no instance of the child has to supply them.
`arend-lib`'s `PseudoRing extends PseudoSemiring, AbGroup` proves
`zero_*-left` and `zero_*-right` once, from additive inverses, and every ring
instance gets them for free. Its `\default` pairs do the same for
interderivable laws: `FrameHom` states `func-Join` and `func-Join>=`, each
defaulted from the other, and an instance implements whichever is easier.

Heather today: `class Ring<A>(…) extends Semiring<A>(…), GroupRel<A>(…) {}`
(`lib/std/algebra/semiring.hthr:143`) adds nothing, so every ring instance re-proves
the semiring absorption laws that the group structure already implies:

| instance | where |
|---|---|
| `CommRing<Int>` | `lib/std/algebra/semiring.hthr:304` |
| `CommRing<Rat>` | `lib/std/num/rat.hthr:1460` |
| `CommRing<CReal>` | `lib/std/num/creal.hthr:1615` |
| `CommRing<Dyadic>` | `lib/std/num/float/dyadic.hthr:282` |

each with `zero_mul := T::zero_mul, mul_zero := T::mul_zero` and a per-type
theorem behind them. That is the restating of laws that the `math-classes`
milestone says clients should not do.

## What is wanted

1. A class body may give an implementation for a field it **inherits**:
   `class Ring … extends Semiring…, GroupRel… { zero_mul := …, mul_zero := … }`.
   The implementation is checked once, at the class, against the instance's
   other fields (Arend's implicit `\this`). An instance of `Ring` or any
   descendant may omit the field. The proof is a generic one over the
   additive group and distributivity (`x * 0 + x * 0 ≈ x * 0`, then cancel),
   written once beside `Ring::neg_mul` (`lib/std/algebra/semiring.hthr:200`), which
   today itself relies on the instance-supplied `zero_mul`.
2. Interderivable pairs: two fields each defaulted from the other, and an
   instance must implement at least one. Arend checks the cycle is broken
   per instance.
3. An instance that does supply the field anyway is an override, and owes
   agreement exactly as `docs/traits-design.md` §4 already says
   ("Overrides owe agreement proofs"). For a proof field in a relation whose
   proofs are not irrelevant, agreement is not needed; say which.

## Questions to settle

- Where the implementation's names resolve. Record field defaults are
  checked hygienically at the construction and see hypotheses only by type
  (`crates/elab/src/constructor.rs`, `elab_field_default`;
  `docs/named-arguments-design.md` §9.6). A class-level implementation has
  to see the instance's sibling fields by name, so it is a different
  scope: the class's own, with the instance's fields as its `self`.
- Interaction with the one-canonical-value rule (`docs/traits-design.md`
  §4): the filled field is computed once where the canonical value is
  minted. A data field filled this way (not only a law) is the
  `nsmul`-style case and must not produce a second value along another path.
- Whether the parent's field can be filled when the parent instance is
  declared on its own (a `Semiring<Int>` declared first, then a
  `Ring<Int>`): the child's implementation then disagrees with nothing, but
  the parent already holds a value.

## What it assumes from elsewhere

- **`docs/traits-design.md`** owns flattening and the canonical value.
  Assumed here: only that inherited fields are the child's own fields after
  flattening, so filling one is filling a field.

## Log

- 2026-11-02: First order consumer (docs/strict-order-presentation-design.md §2.2). `StrictOrder` and `PseudoOrder` now carry tagged views: `Transitive(<)` as `lt_transitive`, the `≈` pairs `same_lt`/`lt_same`/`same_le`/`le_same`, `Preorder(≤)` as `le_preorder`, and the mixed pairs `lt_le`/`le_lt`. They exist so that a generic `calc` works. Each follows from the class's own fields (`lt_trans`, `lt_respects`, `StrictOrder::le_respects`, `PseudoOrder::le_trans`, `lt_of_lt_of_le`). Today they are filled by reference from hand instances at `Rat`, `CReal`, `Dyadic`, `Nat` and `Int` (eight per carrier, plus four `RelId` transports at `Nat` and `Int`), and `Finite(F)` writes them as literal fields twice. A class-level `lt_transitive := Transitive(lt_trans)` and its siblings would retire all of them. One requirement this adds: the filled field is a *tagged parent* dictionary, so it must also work when the default is a whole parent record, not a single law.
- 2026-11-02: Another consumer: `lattice`'s `PartialOrderRel(≈, ≤)` carries tagged `Preorder(≤)` as `le_preorder` and `Trans(≈, ≤, ≤)`/`Trans(≤, ≈, ≤)` as `same_le`/`le_same`, for generic `calc`. Carriers fill them by reference from registered instances; constructors (`PartialOrder::rel`, `product_partial_order_rel`, `Mergeable::meet_semilattice`) write them out. All three follow from the preorder and `le_antisymm`'s reflexivity.
- 2026-11-05: gardener: cites a file it shares with [[class-default-operators]] (`docs/strict-order-presentation-design.md`); [[class-parent-names-resolve-in-client-scope]] (`docs/strict-order-presentation-design.md`); [[floating-point-formalization]] (`lib/std/num/creal.hthr`, `lib/std/num/float/dyadic.hthr`); [[ring-certificate-kernel-cost]] (`lib/std/num/rat.hthr`); [[setoid-roadmap-and-resumption]] (`lib/std/num/rat.hthr`).
