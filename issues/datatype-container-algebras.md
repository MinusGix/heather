---
title: Develop inductives as containers and recursion algebras
status: open
labels: [stdlib,inductives,design,mathematics]
area: mathematics
created: 2026-08-09
updated: 2026-10-28
---

Long-range mathematical-library direction, not scheduled. Heather's finitary
inductives are already lowered through `Wf`: a value has a shape/tag, a
shape-computed arity, and a vector of recursive children. That is recognizably
container/polynomial structure. The library can expose the mathematics of
that representation instead of treating every generated eliminator as an
isolated primitive.

The aim is to make **recursion algebras ordinary first-class mathematical
objects**:

- a datatype's case table, fold algebra, and dependent elimination algebra
  have named record types;
- folds, traversals, and induction are obtained from those objects;
- laws such as fold fusion and uniqueness are proved generically where their
  hypotheses genuinely permit it;
- datatype-generic constructions are described through containers rather than
  by elaborator-private constructor tables;
- the derivative/one-hole-context construction eventually gives principled
  zippers rather than a separate zipper design per datatype.

This is a library and mathematical-abstraction direction in its own right. It
does not depend for its value on compilation, certification, or tactic
automation. A generator may later remove declarations users could already
write and understand explicitly.

## The first layer: algebras for concrete datatypes

For a simple datatype, distinguish three objects rather than hiding all three
behind `match`:

- `D::Cases<M>` keeps recursive fields as values of `D`: nonrecursive case
  analysis or open recursion.
- `D::Alg<M>` replaces recursive fields by results of type `M`: the input to a
  catamorphism/fold.
- `D::Elim<P>` replaces recursive fields by both the value and an induction
  result in `P`: dependent elimination as a record of constructor-local
  obligations.

Sketch only, with final parameter placement and member syntax deliberately
left to [[case-algebra-definitions]]:

```heather
record ListAlg<A, M> {
    nil: M,
    cons: (head: A, tail_result: M) -> M,
}

fn List::fold<A, M>(alg: ListAlg<A, M>, xs: List<A>) -> M {
    match xs {
        Nil => alg.nil,
        Cons(h, t) => alg.cons(h, fold(alg, t)),
    }
}
```

The first useful theorem suite is not merely the two constructor equations.
It should include:

- fold uniqueness: a function satisfying the algebra equations equals the
  fold, under whatever function-extensionality formulation Heather adopts;
- fold fusion: a map between result carriers commuting with the two algebras
  commutes with their folds;
- `map`, `append`, `length`, and monoidal folds as instances or consequences
  of the same algebraic interface;
- the free-monoid characterization of `List<A>`, connecting this direction to
  operation-indexed `Monoid<M>(op)` rather than building an unrelated fold
  hierarchy.

The second exercise should be a genuinely branching datatype, so the design
does not accidentally identify an algebra with a left-to-right list fold.

## The second layer: containers as mathematical presentations

The intended abstract presentation has shapes and positions:

```text
Container = (Shape, Position : Shape -> Type)
Ext C X   = Sigma(s : Shape). (Position(s) -> X)
```

Heather's `Wf` is the finitary specialization whose positions are
`Fin(arity(shape))` and whose children are a vector. The library question is
how much of the ordinary container calculus should be expressible directly:

- sums and products of containers;
- composition;
- mapping an extension along a function;
- fixed points and their folds;
- morphisms/natural transformations between container extensions;
- derivatives, whose shapes describe a value with one recursive position
  selected, yielding one-hole contexts and zippers.

The point is not to expose the elaborator's lowering as users' routine datatype
API. The point is to give that lowering a public mathematical model from which
generic theorems and constructions follow. Surface datatypes should remain the
pleasant spelling; containers explain and connect them.

## Indexed and dependent families

Ordinary algebras are only the nondependent first rung. Indexed families need
an indexed result family and constructors whose child results live at their
computed indices. Dependent elimination needs a motive `P : D -> Type` (or an
indexed analogue) as a record parameter.

This is likely where the direction becomes most valuable and where it meets
real language pressure: dependent/higher-kinded record parameters are needed
to state the algebra object cleanly. The resulting design should account for
the distinction between route-1 indexed families and forded families rather
than pretending every surface inductive has one uniform encoding today.

## Design questions this issue owns

1. **Public abstraction boundary.** Is the common interface the finitary
   `Wf` presentation, a more general `W`/container presentation, or a small
   library vocabulary shared by both?
2. **Law boundary.** Which fold equations are definitional consequences of
   the generated eliminator, and which useful principles (uniqueness, fusion,
   naturality) require explicit hypotheses such as function extensionality?
3. **Datatype coverage.** How are nested, indexed, and mutually recursive
   declarations represented, and which are intentionally outside the first
   calculus?
4. **Morphism notion.** What is the right structure-preserving map between
   containers/algebras, and can composition be stated without a parallel
   hierarchy for every datatype?
5. **Derivative boundary.** Does the container derivative produce useful
   typed zippers for Heather's actual finitary/indexed declarations, or only
   for a restricted regular fragment? State the fragment rather than
   overgeneralizing.
6. **Library organization.** The algebra, its fold, and its theorems should be
   subject-owned (`D::Alg`, `D::fold`, …) without flooding the ambient module
   namespace.
7. **Cost.** First-class algebra records must not force repeated assembly or
   large inlined eliminator terms at every use. Measure concrete and open
   carriers before choosing generated representation details.

## A disciplined first exploration

Before designing a general declaration feature:

1. write `ListAlg` and its fold explicitly in Heather;
2. write the constructor equations, fusion, and the free-monoid connection;
3. repeat for one branching recursive datatype;
4. identify exactly which declarations are repetitive and which theorems are
   truly generic;
5. only then decide whether a public `Container` abstraction, generated
   `D::Alg`, or both are warranted.

The exercise should vary an open element type and include checking-position
uses, following `docs/testing-generated-terms.md`; closed `Nat` examples alone
will conceal the level and scoping questions this direction is meant to
surface.

## What it assumes from elsewhere

- **[[case-algebra-definitions]]** owns generated `D::Cases`/`D::Alg`, named
  per-constructor clauses, and the corresponding surface form. Assumed here:
  only that explicit algebra records are already writable and generation is a
  possible later convenience.
- **[[generators-in-the-language]]** owns whether repetitive artifacts are
  eventually emitted by an in-language generator. This issue does not require
  that mechanism for its explicit-library exploration.
- **[[indexed-families]]** owns the surface representation and lowering limits
  of indexed inductives. This issue consumes whatever family fragment it
  exposes; it does not redefine the classifier or lowering routes.
- **[[type-owned-namespaces]]** owns subject-attached names. Assumed here: a
  future algebra API should live with its datatype rather than in a flat
  namespace.

## Log

- 2026-08-09: Filed from the ambitious mathematical-library direction
  discussion: expose the container mathematics already latent in `Wf`, make
  folds and elimination algebras first-class, and explore fusion, free
  constructions, derivatives, and zippers beginning with explicit `List` and
  branching-datatype exercises.
- 2026-08-18: **The disciplined first exploration landed.** `std/list` now
  exposes `ListAlg<A,B>` and `list_fold`, its definitional Nil/Cons equations,
  pointwise uniqueness, fusion, and an equality with the established `foldr`;
  `std/algebra` builds the algebra supplied by an operation-indexed `Monoid`
  and recovers `mconcat` from it. New `std/tree` is the branching control:
  `Tree<A>`, `TreeAlg<A,B>`, its equations and fusion, plus `tree_size` as a
  concrete consumer. The acceptance composes the branching fold with the list
  one: collect a neutral `Tree<A>`'s leaves by `append`, then fuse `len` through
  it into a Nat algebra, at an open `A` and with both recursive results used.

  **Verdict:** ordinary records and ordinary structural recursion are enough
  for the whole concrete rung; no parser, elaborator, generator, or kernel
  feature was needed. Uniqueness is naturally pointwise, so it needs no
  funext; fusion is two ordinary congruences at a branch. The repetitive
  declarations are exactly the predicted datatype-shaped shell — record,
  fold, two equations — while uniqueness/fusion remain real mathematical
  theorems and should not be generated as unexplained boilerplate. This is
  evidence for a future generated `D::Alg`/fold shell, not yet for exposing a
  general `Container` abstraction.

  Two inference boundaries were measured rather than hidden. A polymorphic
  record literal whose type arguments occur only in its fields needs
  `ListAlg<A,B> { ... }`; and a nested `monoid_list_alg(add)` must spell its
  carrier before indexed-class resolution (`monoid_list_alg<Nat>(add)`). Once
  an algebra value or class binder is already in scope, uses are terse. These
  are existing explicit-type-application boundaries, not new blockers; no new
  issue is warranted from the concrete sites. Subject-owned `List::Alg` /
  `Tree::Alg` naming still waits on [[type-owned-namespaces]], so the shipped
  names are deliberately flat. The issue stays open for the next, distinct
  decision: generate the concrete shell, or first probe the public container
  calculus / dependent algebra rung. Full `scripts/test`: suite 1914 -> 1919,
  0 failed.
- 2026-08-18: **The dependent-algebra probe landed next.** `ListElim<A>(P)`
  and `TreeElim<A>(P)` package the constructor-local obligations for an open
  motive `P : D -> Type`; `list_elim` / `tree_elim` consume them by ordinary
  structural recursion, with definitional constructor equations exposed as
  theorems. `append_nil` is no longer a direct recursive proof: its algebra's
  Cons field receives the IH, and the public theorem is one `list_elim` call.
  The branching control folds a tree back into itself and proves the result by
  a `TreeElim` whose Node obligation uses both differently indexed IHs. Two
  negative controls return a tail/left proof at the whole constructor and are
  refused at the dependent index.

  **Verdict:** the old [[case-algebra-definitions]] rung-3 blocker was stale.
  A type-family-valued *record value parameter* is already the needed
  abstraction; no higher-kinded type-parameter feature, parser change,
  elaborator case, or kernel form is required. The only spelling pressure is
  existing constructor inference: `Node` inside `P(Node(left,right))` must be
  `Node<A>` because inference does not recover a type parameter through a
  recursive child in that inference position (the boundary already recorded
  by [[tyvar-scoping-in-lowered-fields]]). This narrows the next decision:
  `Cases` / open recursion should be probed against a real consumer before one
  generator emits the now-known `Cases` + `Alg` + `Elim` family. Full
  `scripts/test`: suite 1919 -> 1923, 0 failed.
- 2026-08-18: **The Cases/open-recursion probe landed against the real IR
  interpreter.** `IrCases<M>` keeps every recursive field at `Ir`, and
  `ir_cases` is the ordinary non-recursive dispatcher with one definitional
  equation per constructor. `step_cases(ev, prog, env)` closes that record's
  clauses over the fuel-indexed recursive call while `step` merely selects a
  clause. A second, unrelated consumer classifies the outer constructor and a
  mutation control refuses the wrong selected result.

  **Verdict:** `Cases` is distinct from both `Alg` and `Elim` in use, not only
  on paper: it reifies a one-layer dispatch without choosing a recursion
  scheme, and open recursion is ordinary closure capture. Again no parser,
  elaborator, generator or kernel feature was needed. The concrete
  `Cases`/`Alg`/`Elim` family is now fully characterized by explicit Heather
  programs; what remains repetitive is precisely the datatype-shaped record,
  dispatcher/fold/eliminator, and constructor equations. Generation is now
  an evidence-backed convenience round, while a public general `Container`
  calculus remains a separate mathematical decision rather than a
  prerequisite. Full `scripts/test`: suite 1923, 0 failed (count unchanged;
  the focused acceptance and mutation control extend the existing IR test).
- 2026-08-18: **Rung 4's first certified-pass probe landed, with an honest
  split verdict** (`docs/certified-pass-algebra-probe.md`). `TreePassLaws`
  indexes a structural `TreeAlg<A,Tree<A>>` by an arbitrary relation and asks
  for one law per constructor; `tree_pass_sound` is the one generic induction.
  The concrete mirror pass visibly changes the tree and preserves `tree_size`:
  its Node law consumes both IHs plus commutativity. A mutation that drops the
  right branch is refused at that Node obligation.

  The same general construction was attempted first over the real
  eight-constructor `Ir`; its nondependent algebra/fold checked, but the
  dependent global theorem exhausted kernel conversion fuel even after the
  motive was named and the relation specialized to equality. That boundary is
  [[ir-pass-dependent-fold-fuel]]. Thus the prove-local-laws-once architecture
  is validated at a genuine branching pass, but not yet at compiler scale;
  no syntax or generation follows from this round. Full `scripts/test`: suite
  1923 -> 1925, 0 failed.
- 2026-08-18: **The compiler-scale half of rung 4 now passes.** The fuel
  refusal was a fallback record-projection spelling mismatch, not an algebra
  limit: the theorem's respelled `laws` binder was checked against inline
  `Fst`/`Snd` annotations. Component-respelling those emitted annotations,
  while retaining the inline Σ for structural reads, removes the conversion.
  The relation-polymorphic eight-constructor `Ir` induction and the concrete
  `add(0, tag)` pass certificate check at default fuel; a `Succ(tag)` mutation
  is refused. [[ir-pass-dependent-fold-fuel]] is closed. The remaining rung-4
  work is semantic—a non-equality execution refinement—not mechanical scale.
  Full `scripts/test`: suite 1925 -> 1926, 0 failed; kernel bench 106/106.
- 2026-10-28: **Proof repair survey (2026-10-28, `docs/proof-repair-algebra-survey.md`).** Plante et al., *Proof Repair and (Co)algebra Equivalences* (arXiv:2610.36669), is the theory of this issue's design question 2 (law boundary). Pointwise fold uniqueness and fusion need no funext at `Wf`, because each child's hypothesis is an ordinary equation. At `W` the fold of the identity algebra is not provably the identity, so the paper's isomorphism theorem stops at tier 2 (survey §4). Its Lemma 3.10 (a signature as one polynomial: label × non-recursive args, recursive positions) is the public presentation question 1 asks about, and the lowering already builds it. The coinductive dual of `list_fold_unique` holds only up to `Bisim`, since the kernel's `M` has no η (survey §5).
- 2026-11-05: gardener: cites a file it shares with [[datarepr-separation]] (`docs/proof-repair-algebra-survey.md`); [[reprgen-recursive-child-via-embedding]] (`docs/proof-repair-algebra-survey.md`).
