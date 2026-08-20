---
title: "Give Tree a conventional public API and re-home its algebra probes"
status: open
labels: [stdlib,design,cleanup,inductives]
created: 2026-08-20
updated: 2026-08-20
---

`lib/std/tree.hthr` began as the branching control for the algebra and
certified-pass experiments. It now exposes a useful binary `Tree<A>`, but the
file is dominated by `TreeAlg`, `TreeElim`, pass-law records, fusion, rebuild,
and the historical explanation of why each probe existed. A user opening a
standard-library `tree` module should first encounter the ordinary tree API,
not an experiment transcript expressed as record assembly.

Redesign the module boundary without discarding the mathematical work. Decide
which datatype Heather means by the unqualified name `Tree` (the current leaf
or binary-node tree is plausible, but the choice should be explicit), give it
the conventional constructors and operations users expect, and re-home the
algebra/certified-pass material under clear subject-owned names or an
experimental/proofs module.

The preferred eventual spelling is along the lines of `Tree::Alg`,
`Tree::Elim`, `Tree::fold`, and `Tree::PassLaws`, not `TreeAlg`, `TreeElim`, and
`tree_fold`. That spelling depends on [[type-owned-namespaces]]; the library
split and API decision need not wait if an interim module boundary is clear.
“Less record spam” should come from choosing the right public layer and, later,
possibly generating datatype-shaped shells—not from hiding proof obligations
or replacing first-class algebras with bespoke magic.

## Acceptance

- State the intended `Tree` datatype and the minimal conventional API
  (construction, fold/elimination, map, size, mirror/traversal as appropriate).
- Separate core API, algebra laws, and certified-pass demonstrations so an
  ordinary import does not read like a compiler-IR experiment.
- Preserve useful branching proofs and their acceptance coverage in their new
  home, or explicitly retire ones superseded by a generic construction.
- Adopt subject-owned names when available; record a coherent interim naming
  scheme otherwise.
- Reduce comments to current API and mathematical rationale; historical probe
  narrative remains discoverable through its owning issues/docs.
- Measure whether explicit algebra assembly is still useful at call sites
  before proposing generated `Tree::Alg`/`Tree::Elim` shells.

## What it assumes from elsewhere

- **[[type-owned-namespaces]]** owns `Tree::Alg` / `Tree::Elim` declaration and
  lookup semantics. This issue owns which declarations deserve those names.
- **[[datatype-container-algebras]]** owns the general container/algebra
  research and the mathematical value of the branching probe.
- **[[case-algebra-definitions]]** owns generated per-datatype algebra shells.
  This issue does not require generation to clean up the library boundary.
- **[[stdlib-doc-comment-audit]]** owns the library-wide editorial policy.
  Assumed here: Tree's comments are audited after this issue decides which
  declarations and explanations remain in the public module.

## Log

- 2026-08-20: Filed after revisiting `std/tree` as a library rather than as an
  acceptance fixture. The existing content is valuable, but its experimental
  origin should no longer dictate the public module's shape.
