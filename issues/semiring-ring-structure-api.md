---
title: Add a minimally factored semiring and ring API
status: closed
labels: [stdlib,mathematics,algebra,traits]
created: 2026-09-02
updated: 2026-10-20
---

Add the first two-operation algebraic theories without importing a large
pre-existing hierarchy wholesale. Candidate factors include additive and
multiplicative monoids, distributivity as its own theory indexed by both
operations, and zero annihilation. `Ring` should reuse the additive group
rather than repeat inverse laws.

Use `Nat` and `Int` as the primary instances and prove generic finite-sum or
polynomial identities that actually consume the intermediate layers. Record
any missing weaker theory demonstrated by a consumer instead of adding every
possible nonunital/nonassociative variant in advance.

## What it assumes from elsewhere

- **[[algebraic-theory-composition]]** owns how the parents compose.
- **[[big-operator-semantics]]** owns eventual notation and domain-sensitive
  big-operator meaning.

## Log

- 2026-09-02: Filed with distributivity treated as a natural independent
  structure, not an incidental field buried in `Semiring`.
- 2026-10-12: A consumer is waiting: `ring` (docs/tactics/ring-normalization-design.md) normalizes at Int and Nat, and proves Rat laws only through cross-multiplication. Normalizing at a carrier modulo its relation (Rat and ≈, reals later) wants this interface, indexed by the relation, plus Respects2 for + and *; the normalizer and its soundness proof in lib/std/tactic/ring.hthr would be restated over it. Filed from [[ring-normalization]].
- 2026-10-20: LANDED: `lib/std/algebra/semiring.hthr`, relation-indexed, with `MonoidRel`, `CommMonoidRel` and `GroupRel` added to `algebra_rel` beside `SemigroupRel`. Layers: `Distributes(≈, +, *)` as a theory of its own; `Semiring` = `CommMonoidRel(≈, +)` untagged + `MonoidRel(≈, *) as multiplicative` + `Distributes` + zero annihilation on both sides; `Ring` = `Semiring` + `GroupRel(≈, +)`, nothing restated; `CommSemiring`/`CommRing` add `Commutative(≈, *) as commutative`. Instances: `CommSemiring<Nat>` and `CommRing<Int>` under `RelId` (with `designation ≈ at Nat/Int := RelId`, so a generic theorem reads back as `=`), and `CommRing<Rat>` under `Rat::Same` in rat.hthr.

  Consumers that use the intermediate layers: `MonoidRel::fold` and `fold_append` (applied at both `+` and `*` of a semiring, the product through the tag), `CommMonoidRel::fold_map_op` (Σ(f+g), and Π(f·g) at a commutative product), `GroupRel::inv_unique`/`inv_inv`, `Semiring::mul_sum_l`/`sum_mul_r` (needs annihilation for the empty sum), `Semiring::mul_add_add`, `Ring::neg_mul`/`mul_neg`/`neg_mul_neg`. Showcase `docs/showcase/semiring_client.hthr` states them at all three carriers; tests in `crates/elab/tests/lib_std_semiring.rs`.

  The relation-indexed shape needed class-system work (docs/language/classes/operation-indexed-classes-design.md §8.1): inherited `as`-symbol laws take the child's spelling (they were unresolvable in a child that spelled the operation differently), the phantom-index check counts symbols, a flat and a tagged fiber of one class coexist with the flat one answering unqualified requests, and a proof-only ancestor (the setoid) may be reached untagged and inside a tag, every instance owing the tag's copy agreement by conversion. A data-carrying ancestor reached twice stays refused: that is why `CommSemiring` adds the `Commutative` law rather than a second `CommMonoidRel` at `*`, and why the commutative consumers ask for `MonoidRel(same, op) + Commutative(same, op)`.

  Weaker theories a consumer demonstrated: none beyond `Distributes` and the `MonoidRel + Commutative` pair. Annihilation is derivable in a ring (`OrderedField::mul_zero` derived it before the ordered field was rebased on `CommRing`) but stays a `Semiring` law; no carrier here needed the nonunital or annihilation-free variants. Residue: [[ring-modulo-a-relation]] (the normalizer over `CommRing`), [[ordered-field-over-comm-ring]] (the ordered layers restate these laws).
