---
title: Probe first-class packaging of value-indexed structures
status: open
labels: [design,traits,elaboration,frontend,mathematics]
created: 2026-08-09
updated: 2026-08-09
---

Investigation issue from the morphism-library discussion. Operation-indexed
classes deliberately make the subject value part of the type:

```heather
class MonoidHom<A, B>(
    opA: A -> A -> A,
    opB: B -> B -> B,
    f: A -> B,
) {
    map_op: ...,
    map_unit: ...,
}
```

This is the right **fiber** for a known function: a value
`h : MonoidHom<A, B>(opA, opB, f)` is evidence about precisely `f`, and the
index pseudo-projection can expose `h.f`. Implicit binders let ordinary generic
functions and composition recover `f` from an explicit `h` without the caller
writing it.

A different use wants the **total space** of that family: one type containing
all homomorphisms between the two chosen monoids, with the map selected inside
each value:

```text
Sigma(f : A -> B). MonoidHom<A, B>(opA, opB, f)
```

Examples are a list containing both identity and doubling, a function choosing
between two morphisms, and the categorical `Hom(X, Y)` type. The distinction is
not "dictionary versus data" — dictionaries are already data — but **an index
fixed outside the value versus an index packaged inside it**.

The design question is how often Heather needs that total-space view, how it
should be expressed, and how much elaborator convenience is justified without
making omitted indices or typeclass search magical.

## One law-bearing definition

The preferred starting invariant is one definition of the laws:

```heather
MonoidHom<A, B>(opA, opB, f)
```

Do not begin with parallel `IsMonoidHom(..., f)` and bundled `MonoidHom { map,
... }` APIs. If a first-class package is needed, it should reuse the indexed
class through an ordinary dependent pair/record:

```heather
record SomeMonoidHom<A, B>(
    opA: A -> A -> A,
    opB: B -> B -> B,
) {
    map: A -> B,
    laws: MonoidHom<A, B>(opA, opB, map),
}
```

Value-parameterized dependent records already make this explicit form
expressible with no kernel feature. The investigation starts there and asks
whether a general surface abstraction earns its cost.

## Candidate surface directions

These are alternatives to probe, not proposals to combine:

1. **No new feature.** Fixed-function theorems use the indexed class;
   first-class customers declare an explicit package record such as
   `SomeMonoidHom`.
2. **Explicit general existential syntax.** For example:
   `some f : A -> B. MonoidHom<A, B>(opA, opB, f)`. This is ordinary Sigma
   presentation and works for any family, not only classes.
3. **Indexed-structure packaging syntax.** For example:
   `some MonoidHom<A, B>(opA, opB)`, closing designated omitted indices into
   the value. This is terser but requires the class declaration or use site to
   say which indices are packaged rather than inferred.
4. **Partial-application convention.** Treating `MonoidHom<A, B>(opA, opB)`
   itself as the total space. This is maximally terse and maximally suspect:
   omitted arguments ordinarily mean inference or partial application, not
   existential closure.
5. **Bundle as the primary record.** Put `map` back in the record and stop
   indexing by `f`. This makes categorical storage easy but loses the precise
   property type, prevents multiple morphisms from being distinct class goals,
   and invites resolver nomination at `(A, B)`; include as the control the
   indexed design is expected to beat.

## What elaboration may do safely

Low-magic conveniences with strong local evidence:

- infer an external implicit `f` from the type of an explicitly supplied
  dictionary;
- expose `f` through the existing index pseudo-projection (`h.f`);
- infer other indices (`opA`, `opB`) from explicit morphism arguments to
  composition;
- construct a package in checking position when both the map and its law
  dictionary are written;
- preserve the hidden indices in hover/diagnostic data and offer an expanded
  fully explicit rendering;
- pretty-print determined indices compactly without changing their type.

Questionable conveniences requiring adverse probes:

- interpreting an omitted argument as existential in one type position and as
  an inference meta in another;
- automatically packing or unpacking when a fiber and total-space type meet;
- coercing a package to its map or its law dictionary;
- allowing expected type alone to choose whether source text denotes the fiber
  or total space;
- asking instance resolution to solve an existential by inventing/selecting an
  unpinned `f`.

Standing safety line: **ordinary typeclass search never chooses the hidden
subject value.** A package is constructed explicitly, inferred from an
explicit value already in hand, or produced by an ordinary function whose
semantics chooses it. Existential closure must not become a route around the
value-slot refusal of [[operation-indexed-classes]].

## Required probes

Write the smallest explicit-record version first, then compare candidate sugar
against the same corpus.

### Fiber uses: no package should be required

1. Prove `id` and `double` are monoid homomorphisms at distinct function
   indices.
2. Apply a generic lemma whose `f` is implicit and learned only from an
   explicit hom dictionary.
3. Compose `hf` and `hg`; infer `f`, `g`, all operations, and return evidence at
   the computed index `compose(g, f)` without registry installation.
4. Recover and call the indexed function through the dictionary pseudo-
   projection.

### Total-space uses: one common type is required

5. Put identity and doubling into one homogeneous `List`.
6. Choose between them by matching a neutral `Bool`, so conversion cannot hide
   the differing function indices.
7. Define the monoid-category candidate `Hom(X, Y) : Type` and identity/
   composition over packaged morphisms.
8. Return a package from a function, open it, and use the recovered map and
   laws in a dependent checking position.

### Boundary controls

9. Refuse a request that asks resolution for "some homomorphism" with no map
   evidence; list known indexed instances without selecting one.
10. Distinguish inferable omission from existential closure in syntax and
    diagnostics.
11. Package two or more value indices selectively (for example a morphism
    whose function is hidden but whose source/target operations remain fixed).
12. Exercise an open carrier/type and a nonzero universe level; dependent
    packaging must not be validated only at closed `Nat`.
13. Test a package under a setoid equality on maps, so the design does not
    accidentally assume record identity or function extensionality.
14. Measure whether repeated automatic pack/unpack would assemble or inline
    large dictionaries compared with the explicit record baseline.

## Questions this issue owns

1. Is explicit value-parameterized `record` sufficient in real library use?
2. If not, is the missing abstraction general Sigma syntax or something
   specifically aware of class indices?
3. How does a declaration mark indices as inferable inputs, packageable
   subjects, or both without reviving a general mode system accidentally?
4. Does a packaged structure expose one uniform spelling (`h.f`, `h.map`) for
   its hidden index and its law dictionary?
5. Where do automatic packing/unpacking boundaries become non-local or make
   elaboration dependent on expected type in surprising ways?
6. How are packages compared: record identity, equality/setoid relation on the
   hidden subject, or a structure-specific extensionality theorem?
7. Can the category customer remain an ordinary type alias over Sigma, or does
   it demonstrate recurring ergonomics that justify first-class syntax?
8. How do alias-class roles and scoped instances behave when their underlying
   index is packaged rather than externally fixed?

## What it assumes from elsewhere

- **[[operation-indexed-classes]]** owns value-indexed class identity,
  inference, pseudo-projection, and refusal of unpinned value slots. Assumed
  here: the fiber form remains the one law-bearing class.
- **[[surface-existential]]** is closed and owns the landed explicit mechanism:
  value-parameterized dependent records. This issue begins with that mechanism
  rather than assuming a missing kernel Sigma.
- **[[class-alias-roles]]** owns elaborator-visible roles on otherwise
  transparent class types. This issue only asks how such metadata behaves when
  indices are hidden in a package.
- **[[setoid-auto-lifting]]** owns automated respectful lifting. This issue's
  setoid probe is manual and asks only what equality first-class morphisms use.

## Log

- 2026-08-09: Filed as an explicit exploration rather than a decided feature.
  Probe the boundary between a class fiber indexed by a known function and its
  total space of first-class morphisms; start from an explicit dependent record,
  compare general Sigma and class-aware sugar, and put every proposed
  elaborator convenience against inference, composition, heterogeneous
  storage, categorical Hom, diagnostics, and the no-unpinned-choice rule.
