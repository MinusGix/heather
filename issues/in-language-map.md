---
title: First in-language derived artifact: map, via a quotation slice and an evaluation hook
status: open
labels: [metaprogramming,frontend,elaboration,kernel,design]
created: 2026-08-02
updated: 2026-08-02
---

The opening move of [[generators-in-the-language]]'s migration, scoped by
the 2026-08-02 expressiveness verdict (logged there): the vec.rs schemas
are the one generator family that consults nothing — no whnf/conversion
oracle, no declaration table, no code equality — and \`map\`/\`nth\` never
ANALYZE code at all, only build a fixed template with parameters spliced
in. So the first in-language artifact needs none of the verdict's four
blockers: no code recursors, no match-on-code, pure quotation.

Three parts, which only matter together:

1. **A surface quotation slice** — box/quote syntax, antiquotation, and
   layer-m fn declarations. Deliberately the MINIMAL slice of
   surface-syntax round 2: box-intro + letbox only; match-on-code (the
   52-branch analysis story) stays out. Fix everything at level 0 —
   the surface has no level variables, and ULam can wait
   ([[implicit-level-polymorphism]]).
2. **The evaluation hook — the real deliverable.** Today the elaborator
   calls \`vec::map\` (Rust) while elaborating \`.map\`. In-language, the
   elaborator instead evaluates a Ψ-resident layer-m function on code
   arguments (kernel computation mid-elaboration) and splices the result.
   This hook is the load-bearing core of the whole migration; \`map\` is
   its smallest first client. \`box-synthesis-gap\`'s closed conclusion
   binds here: elaborated code must emit letbox, not β-redexed
   meta-functions.
3. **The cross-check**: in-language \`map_code\` output vs Rust
   \`vec::map\` output, compared up to conversion on concrete instances —
   the "one small artifact, cross-checked against the Rust one" plan
   from [[generators-in-the-language]]'s filing.

The payoff is proving the pipeline (surface → layer m → emitted code →
kernel check → splice back) on ~100 lines before committing to the
analysis story; if the letbox discipline or context indexing is miserable
at the surface, this is where it surfaces cheaply. The shape of the
artifact: \`map_code : □(g ⊢ Ty A) → □(g ⊢ Ty B) → □(g ⊢ A -> B) →
□(g ⊢ Nat) → □(g ⊢ Vec(A;k) -> Vec(B;k))\` — one box literal with
letbox-bound splices where the Rust version hand-shifts; the modal
substitution calculus does the de Bruijn arithmetic that makes vec.rs
fiddly, which is the thesis' selling point demonstrated at minimum size.

Wants a session of its own (a real syntax round plus elaborator
plumbing). Migration order after it, per the verdict: the certifying
generator's fragment transcriber (its input code is elim_N + constructors
+ variables — no global refs, exactly what elim^Trm can walk), then
guard/inj-style generators only after kernel rounds for opaque globals /
oracle access / code equality.
