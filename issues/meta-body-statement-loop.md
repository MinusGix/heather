---
title: The meta-fn body has its own statement loop, and annotated `let` stops at its edge
status: open
labels: [metaprogramming,elaboration,frontend]
area: language
created: 2026-08-02
updated: 2026-08-12
---

Found by the coordinator sweep after the let/blocks round
(docs/let-and-blocks-design.md, 2026-08-02). That round's doctrine was that a
declaration body and a block expression "cannot drift in what a \`let\` means",
and it enforced it by lifting \`elab_stmts\` out of \`elab_decl_inner\` so there is
one walk. There is a **third** walk it did not touch: \`elab_meta_decl\`
(\`crates/elab/src/quote.rs\`, the \`for stmt in &decl.body.stmts\` loop) has its
own copy for \`meta fn\` bodies.

The two loops are **dual restrictions of one concept**, which is why neither
is obviously wrong and why the duplication is easy to miss:

| statement | \`elab_stmts\` (program) | \`elab_meta_decl\` (meta) |
|---|---|---|
| \`let x = e;\` | infers, aliases | infers, aliases |
| \`let x: T = e;\` | \`elab_ty\` + \`elab_check\` | **rejected**: "not part of the meta slice yet" |
| \`let { f } = e;\` | projections, aliases | **rejected** |
| \`let code x = e;\` | **rejected**: "meta-layer syntax" | binds code |

## Why it is worth a look now, and was not before

Before the let/blocks round, \`let x: T = e;\` did not parse at *any* \`T\`
([[annotated-let-swallows-the-equals]]), so the meta slice's rejection cost
nothing — nobody could write the form anywhere. Now it is writable everywhere
*except* a \`meta fn\` body, so the restriction is visible for the first time,
and the message's "yet" is a promise nobody has scheduled.

## The questions a round here has to answer

1. Does an annotated \`let\` at \`Layer::Meta\` check its annotation with
   \`elab_ty\` at the meta layer, or does the annotation have to be a code type?
   The meta slice's locals are code-typed or meta-typed, and \`elab_ty\` is a
   program-layer reader.
2. Does \`let { … }\` mean anything at layer m? A record at layer m is an
   ordinary Sigma, so probably yes, but nothing needs it.
3. Can the two loops become one with a layer parameter, or is the duality
   real enough that two loops with a shared table is the honest shape? The
   \`LetCode\`-vs-annotated split is not a subset relation in either direction.

Not urgent: nothing is broken and both rejections are loud, with messages that
name the slice. It is filed so the third walk is *known* rather than
rediscovered the next time someone widens \`Stmt\`.

## What it assumes from elsewhere

- **[[in-language-map]]** owns the meta slice and its deliberate minimality.
- **[[let-inside-quotation]]** is a different question: that one is a \`let\`
  inside a quote *payload* (inside \`code { … }\`); this one is a \`let\` in the
  \`meta fn\` body *outside* the quote, which already works unannotated.

## Log

- 2026-08-12: Correction from the route-1 spike (2026-08-12, docs/archive/certgen-emission-route1-spike.md sec. 5): in-language-certificate-emission had cited this issue as route 1's surface prerequisite ('ordinary match/recursion in a meta body -- meta-body-statement-loop territory'). Wrong on both halves: ordinary match in a meta body already exists (the analyzer round landed it; verified over a Wf-lowered Ir at layer m), and the missing RECURSION's home is the Psi-resident-meta-definitions deferral (docs/in-language-map-design.md sec. 8), not this issue -- this issue is about annotated let and destructuring, and route 1 needs neither. Nobody should schedule this as a certificate-emission prerequisite; it stands on its own visible-restriction merits.
- 2026-11-05: gardener: cites a file it shares with [[frontend-roadmap]] (`docs/in-language-map-design.md`); [[in-language-certificate-emission]] (`docs/archive/certgen-emission-route1-spike.md`).
