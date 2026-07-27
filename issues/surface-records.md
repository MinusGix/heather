---
title: "Records: named-field Sigma sugar"
status: open
labels: [frontend,syntax,elaboration,design]
created: 2026-07-26
updated: 2026-07-26
---

Named-field records desugaring to `Σ`, with `p.field` projection and
non-dependent `A × B`. Specified as a requirement in [[front-end-sugar]]
("Σ sugar — now concrete, motivates the whole issue") since 2026-07-23;
this is the work item.

```
record Monoid<A> { unit: A, op: A -> A -> A, unit_l: (x: A) -> op(unit, x) = x }
```

## Why now, and why after [[surface-polymorphism]]

A trait, an algebraic structure, a `Compile` instance and an
optimization-pass interface are all *records of functions*, and none of them
exists without this — [[compile-typeclass-design]] is blocked on it directly.
But a monomorphic record is nearly useless, since every interesting record is
generic in its carrier, so this lands after (or with) polymorphism rather
than before.

Most of the substrate is already there and already exercised:

- `Type::Sigma`, `Pair`, `Fst`, `Snd` are v0 formers, and **η for pairs is
  definitional** (`conv.rs:668`), which is what makes `let (a, b) = p`
  transparent and what tier 0's field-offset scheme already leans on.
- The tier-0 lowering (`docs/inductive-tier0-lowering.md`) already builds a
  Unit-terminated Σ spine per constructor with field projection as
  `fst(snd^j)`. A record is that scheme with one constructor and named
  accessors.
- A dependent field (`unit_l` above mentions `unit` and `op`) is exactly why
  the spine is Σ and not a product; that part is designed.

## Open questions

1. **Is `record` a distinct declaration form, or a one-constructor
   `inductive` with accessor sugar?** The second is less machinery but
   inherits the nominal tag discipline and the tier classification; the first
   is a second declaration path to keep in step. Related: a record should
   *not* be recursive — that is an `inductive`.
2. **Projection vs. pattern.** `p.op` and `let { unit, op } = p` are both
   wanted; with Σ-η they are interchangeable, which is worth pinning as a
   test rather than assuming.
3. **Where the level goes.** A record over `A : Ty 0` lives at level 1 as
   soon as it stores a type. State the level rule before writing code —
   non-cumulativity has bitten twice already
   ([[unit-level-and-vec-preservation]], `docs/unit-empty-level-indexing.md`).
4. [[dependent-field-injectivity]] applies here verbatim: a later field whose
   type mentions an earlier one is the *normal* case for a record, not the
   exotic one.

Not in scope: instance resolution / typeclass search
([[compile-typeclass-design]]), and coercions of any kind.
