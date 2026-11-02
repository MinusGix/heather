---
title: A generic e-graph library: proof forest, congruence closure over any operator, interpretations, and its soundness theorem
status: closed
labels: [tactics,stdlib,design]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

Minus asked (2026-11-02, on [[grind-port]] round 1) for the e-graph to be
generic, so other parts of the system that identify terms up to equations
can use it, and so its correctness can be proved once.

grind's graph (`lib/std/tactic/grind.hthr`) is already split: reading terms
(`Spine`, `View`, `Defeq`) is `Tac`, and everything after it (hash-consing,
union, congruence, the edge forest, explanation) is pure Heather over `Nat`
ids. The pure half is the library.

Wanted, in three layers:

1. **A proof forest** generic in the justification `J`: union, find, and
   `explain(a, b) → Option<List<Step<J>>>`, the unique path between two
   members of a class.
2. **An e-graph** generic in the operator, `ENode<Op> { op: Op, kids:
   List<Id> }` with `Op: DecEq` (logic.hthr's class) or a `same` field:
   hash-consing, congruence closure, a justification `Given(j) | Cong(n1, n2)`.
   grind's curried application is one instance (`Op` = application or atom
   key, two kids); a first-order term language with n-ary operators is
   another.
3. **Interpretations of a path**, as a record of `refl`/`sym`/`trans`/`cong`
   over any evidence type `P`: grind's `Expr` proof builder, a renderer of
   the stuck state, and a `≈` instance with `Proper` congruences for setoid
   goals.

Theorems, stated over a denotation `⟦·⟧: Id → A` and a validity predicate
(every edge's justification proves its two endpoints equal under `⟦·⟧`):
the operations preserve validity, and a valid graph's `explain` path
interprets to a proof of `⟦a⟧ = ⟦b⟧`. Only soundness; completeness is not
needed by any client.

Why the theorems matter: grind does not need them (the kernel checks its
output term), but a client that runs the graph where no checker follows
does. A compiler pass doing value numbering or common-subexpression
elimination over `rt` is proved once against the library's theorem
instead of per program ("prove the generator", docs/compilation-vision.md).
Equality saturation for code generation is the same object. Other likely
clients: atom identification up to equations for omega/ring/linarith
([[omega-record-projection-atoms]]) and theory combination
([[grind-splits-and-theories]]).

Costs to watch: dictionary-passing generic code in the value-domain
evaluator, and n-ary nodes needing a congruence per arity when building
proof terms (grind keeps curried nodes for that reason; a verified client
does not care).

Sequencing: before [[grind-e-matching]], which reworks the core anyway
(patterns match against e-nodes).

## What it assumes from elsewhere
- **[[grind-port]]** owns grind and its reading of terms. Assumed here: only
  that the pure half can move under it unchanged in behaviour.

## Log

- 2026-11-02: Built (Minus approved the same day): `lib/std/data/egraph.hthr`, `docs/grind-design.md` §8. `EGraph<Op, J>` with `add`/`fresh`/`union`/`close` over any operator, explanations through `PathAlg<J, P>`, and soundness against a denotation (`Agrees`, preserved by `empty`/`fresh`/`add`/`union`/`close`; `same_class_sound`). grind runs on it. Probes in `lib/_tests/std/data/egraph_tests.hthr`, including `by_classes`, which proves an equation from a class with no explanation. Not built: the `≈` path algebra, and a value theorem for a hash-consed `add`.
