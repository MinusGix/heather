---
title: Audit every annotation emission site for spelling one type two ways
status: open
labels: [elaboration,performance,representation]
created: 2026-09-06
updated: 2026-09-06
---

The cheap half of [[unnameable-annotation-occurrences]], split out because it
needs no new definitions. [[inductive-spelling-codes-nonrecursive]]'s round
removed 3 s of a 8.5 s module by making one emission site agree with another
(`respell_ty_deep`'s `Wf` arm now respells the arity's `Case` annotations
with the shape): the kernel had been walking an inline copy against a
respelled copy at every well-formedness check, and "spell alike" beat
"spell smaller" — the shape-code round measured the same
(docs/wf-shape-code-design.md §3.2).

The `Tc::conv_ty` miss sampler ([[perf-profile-build-target]]) shows what is
left on the five-node FunctionIR/x86 module after that round, and every row
is the same pattern — one site respells a monomorphized or value-indexed
copy, another writes it inline:

- `Sigma` vs `Sigma`, 450 queries / 0.49 s: `BitVec(64)`'s
  `Σ(tag). Σ(Vec(⟦Bool⟧; 64)). Unit` inline against
  `Vec(El (Bool#tycode^δ); 64)`.
- `Pi` vs `Pi`, 150 / 0.27 s: `Gprs.at : Gpr → BitVec(64)` inline against
  respelled — the function-typed field, family (1) of the owner.
- `Sum` vs `Sum`, 312 / 0.09 s: a 54 K-char inline monomorphized copy
  against a named-component one.
- `Sigma` vs `El⌜⌝`, 154 / 0.12 s: the 216 K-char `MachineState<M>`
  instance against its boxed code literal.

About 1.3 s of 2.0 s kernel time, on a module where a proper
per-instantiation code scheme is still a design question.

## Shape

Find the *pair of sites* behind each row (the sampler needs item
attribution first — [[conv-miss-sampler-item-attribution]]), then make the
inline side go through the same `respell_ty_deep` as the other, or make
the respelled side decline, whichever keeps structural readers on the
inline copy (docs/wf-shape-code-design.md §4's line). Candidates to check
first: record-literal field annotations and `RecProj`/`RecTail` bodies for
value-indexed records (`BitVec(n)`), `App` `dom`/`cod` at function-typed
record fields, and the code layer's quote of a lowering (`⌜⟦D⟧⌝` vs
`El (D#tycode^δ)` — the boxed-literal spelling).

Acceptance: those rows gone or O(1) per query on the sampler; no
structural reader learns a new spelling; full `scripts/test`.

## What it assumes from elsewhere

- **[[unnameable-annotation-occurrences]]** owns the residual families and
  the per-instantiation-code design. Assumed here: only that a consistent
  spelling with no new definitions is its cheap half.
- **[[perf-profile-build-target]]** owns the sampler. Assumed here: only
  that it reports (expected head, inferred head) buckets with excerpts.
