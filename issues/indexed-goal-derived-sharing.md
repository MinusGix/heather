---
title: The canonical derived table never fires for a value-indexed goal
status: closed
labels: [elaboration,performance,traits]
created: 2026-08-09
updated: 2026-08-31
---

Found by round one of [[operation-indexed-classes]] (docs/language/classes/operation-indexed-classes-design.md §14.2): layer 2's canonical derived table (docs/language/classes/traits-layer2-design.md §8) shares derived dictionaries by an empty-context closedness test, and a goal at a value-indexed class fails it — the index is a term carrying the use site's identity substitution, so every derivation at an indexed goal is minted fresh per use site. Sharing only, never correctness; strengthen_ty was tried during the round and does not help. Pinned by a test that states the fact, with the unindexed-class control beside it (crates/elab/tests/operation_indexed_classes.rs).

Not currently measurable as a cost: the library's indexed goals resolve through scope binders or concrete registry hits, and derivation-heavy paths (generic instances backchained at open element types) have not shown up in timings. TRIGGER for picking this up: a corpus timing that attributes repeated derivation at one indexed goal, or the operators round making designation-driven resolution hot.

Levers, recorded so the fix is not re-derived: (1) key the table by (goal-head, index-spelling) where the index strengthens to a closed term — the common concrete case (add, or) IS closed and only the identity-substitution wrapper defeats the test today, so a smarter closedness reading may recover most sharing cheaply; (2) a per-declaration (not global) cache scoped under the binders the index mentions, the same shape as the upcast read-through's locality; (3) accept per-use minting and rely on the kernel gate's cheapness, measured. See also [[upcast-assembly-cost-at-open-carriers]] (closed) for the house pattern this follows.

Closed 2026-08-31 by making option (3) an explicit policy, with one correction
to the original observation: a sufficiently closed value index *could* pass
the empty-context test and mint a specialization. The resolver now suppresses
canonical derived minting for every class with value parameters, closed or
open. Resolution retains the declared parameterized instance application;
this avoids an unbounded family of synonymous globals (notably one per
collection-literal length), preserves deterministic dictionary identity, and
costs only the optional sharing this issue found no measurable need for. A
resolver-level regression pins the closed-index case independently of literal
syntax.
