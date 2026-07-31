---
title: Sketch: functions defined per-constructor, dispatch as an object
status: open
labels: [frontend,syntax,elaboration,metaprogramming,design]
created: 2026-07-31
updated: 2026-07-31
---

Design sketch, deliberately ahead of need (user, 2026-07-31, off the
[[ir-simulate-design]] round). The observation: ir_v1's \`step\` is not an
arbitrary function — it is a CASE ALGEBRA for \`Ir\`, one clause per
constructor, with the recursive call passed in as a value \`ev\` and the
knot tied elsewhere (\`eval\`, on fuel). That shape was forced by
performance ([[simulate-conversion-cost]]: single ih occurrence), but it
is also exactly how the kernel already thinks: an eliminator application
IS a dispatch table — a telescope of per-constructor cases. The surface
writes that object as a monolithic \`match\` and loses the structure.

The feature space, from mild to radical:

1. **Named per-constructor clauses** as separate declarations that the
   elaborator assembles into one function (strawman only:
   \`fn step@LetCall(...)\`). Buys: per-clause reuse and testing, diffs
   that touch one constructor touch one declaration, and a natural
   anchor for structurally named goals — this is [[split-on-arms]]'s
   naming question appearing on the definition side.
2. **The algebra as a first-class value**: a record of clauses for an
   inductive (the inductive's declaration induces the record type — one
   field per constructor, field types from the constructor telescopes).
   \`fold : Alg(D, M) -> D -> M\` is then THE eliminator worn as a
   library function, and \`step\`-shaped open recursion (\`ev\` passed in)
   is the algebra over the one-layer functor. Generic derived artifacts
   ([[generators-in-the-language]]) would consume such records rather
   than bespoke Rust telescopes.
3. **The performance hook, which makes this more than aesthetics**: the
   single-ih dispatch discipline that [[simulate-conversion-cost]] forced
   should be the SHAPE THE ELABORATOR EMITS, not a style users must know.
   A per-constructor definition form can guarantee it by construction —
   the sugar's lowering is precisely ir_v1's \`step\`/\`eval\` factoring.

Boundaries to hold if this is ever built: tables stay CLOSED per
inductive (an open/extensible dispatch would poison intensional instance
keying and [[elaboration-determinism]]); and clauses are one function's
clauses, not typeclass-style scattered instances — coherence by
construction, not by resolution.

Not scheduled; wants [[nested-match-patterns]] first (its elaboration is
the substrate) and profits from [[generators-in-the-language]] thinking.
