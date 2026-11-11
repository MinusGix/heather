---
title: "Finite types: a class with enumeration, instances, and quantifiers decided by evaluation"
status: closed
labels: [stdlib,mathematics,finite]
area: mathematics
milestone: [math-finite]
created: 2026-11-10
updated: 2026-11-11
---

From the foundational-mathematics ranking Minus accepted on 2026-11-10
(`docs/roadmap.md` log, that date), area 1.

The library has no notion of a finite type. `Fin` is a builtin whose one
library use outside `lib/std/num/float` is `List::at`. Every client that
ranges over a finite carrier (register sets, opcode forms, DFA states, the
float formats' digit ranges) brings its own list and its own "this list is
everything" lemma.

## Scope

- A class for a type with a duplicate-free list of all its elements
  (name to be chosen against `lib/std/num/float`'s `Finite(F)`, which is
  taken), with membership of every element as a field.
- Instances: `Fin n`, `Bool`, `Unit`, bytes and words at a literal width,
  products, sums, `Option`, and enums through `derive`.
- `Decide` for `∀ x, P(x)` and `∃ x, P(x)` over an instance with decidable
  `P`, by folding the list, so a closed claim is `b = True` by `refl`
  (`docs/proof-patterns.md`, closed verdicts).
- Probes in `lib/_tests` on all four axes of
  `docs/testing-generated-terms.md` for the derived instance.

## Done when

A client proves an exhaustive claim over an enum and over `Fin n` at a
literal `n` by `decide`, with no enumeration lemma of its own, and
[[finite-cardinality-and-pigeonhole]] can start.

## What it assumes from elsewhere

- **[[finite-set-enumeration-and-folds]]** owns enumeration of finite
  *sets*. Assumed here: only that a finite type's full set is one of them.
- **[[automation-lemma-registries]]** owns how a new instance reaches
  tactics. Assumed here: nothing yet; instances are ordinary class
  instances.

## Log

- 2026-11-11: Round 1 built. `lib/std/data/fintype.hthr`: `class Fintype<A> { elems, complete, nodup }` (the name `Finite` is the floats'), `Fintype::all`/`any`/`find`/`card` as evaluating functions with soundness and refutation both ways, and the propositions `Fintype::All<A>(p)`/`Any<A>(p)` with `Decide` instances, so a closed claim is `decide` or `Fintype::all_sound(p, refl)`. Instances: `Bool`, `True`, `False`, `Fin(n)`, `Option`, `Pair`, `Or` (the sum). `lib/std/data/fin.hthr` is new: `Fin::succ`, injectivity and apartness of the constructors, `Fin::all` with completeness, `NoDup` and its length. `list.hthr` gained `mem_map_inv`, `NoDup` with `nodup_map`/`nodup_append`, `all_bit`/`any_bit`/`find` with their laws, and `product`; `logic.hthr` gained `Or`'s injectivity and apartness.

  Elaborator change this needed: `Fin` had no carrier name, so `instance(n: Nat) C<Fin(n)>` and `fn Fin::f` were refused. `Fin` is now a constant carrier as `Nat` is (`head_name`, `names_a_type`, `carrier_of_ty`). Only the unreduced former answers: a `Fin` type already reduced to its sum has no namespace.

  Not built, with owners: `decide` on a bare `(a: A) → …` goal ([[decide-at-dependent-function-carrier]]); enum instances by `derive`, since a generator cannot build a `match` ([[derive-fintype-for-enums]]; a hand instance is three lines and is probed). Words are an instance at every width (`lib/std/bitvec/bitvec_fintype.hthr`, `Fintype<BitVec(n)>`, head bit outermost): a word is its head bit on its tail by the vector's η, so completeness needed no bit lemma. What remains of this issue's scope is only the enum instances, owned by the derive issue.
- 2026-11-11: Closed: the class, the instances and the quantifiers are built (PRs #550 and the cardinality round). The one item of scope left, enum instances by `derive`, is owned by [[derive-fintype-for-enums]].
