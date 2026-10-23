---
title: First in-language derived artifact: map, via a quotation slice and an evaluation hook
status: closed
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

## Log

- 2026-08-02: The round opened with its design sketch (docs/in-language-map-design.md): surveys settled the two open questions — Psi cannot hold a layer-m body (typing.rs:149/162, ch. 04 verbatim), so the hook holds kernel-checked (Layer::Meta) meta definitions elaborator-side per box-synthesis-gap's static-computation decision, with true Psi-residency deferred as a metatheory-grade round; and the payload's elim-with-Pi-motive is expressible today via explicit-motive match (function-type motive bodies, lib.rs:288), so the quotation slice needs no new elimination form. Syntax adopted from surface-v0 sections 4-6 (code blocks, $-splices with letbox hoisting, let code, meta fn explicit); match code stays out. Implementing round follows section 7's acceptance list.
- 2026-08-02: LANDED, same session as the design sketch: the pipeline runs end to end — lib/lang/vec_code.hthr's map_code is the first surface declaration checked at Layer::Meta, the hook (elab_vec_map consulting meta_defs) evaluates CtxApp(map_code, Gamma) to a box by delta-transparent WHNF mid-elaboration, and the spliced payload's output is CONVERTIBLE with Rust vec::map's at literal, neutral-length, and open-element-type instances (crates/elab/tests/in_language_map.rs; slice mechanics + diagnostics in tests/quotation.rs, 20 tests). Two corrections to the issue's sketched signature, both calculus facts (design doc section 3): (1) no meta-functions over terms exist, so a code argument's payload cannot index a later type — Code(g |- Vec($a; $k)) is unstatable and the length moved inside the quote; (2) a layer-p type can never appear inside layer-c code (binding invariant i' <= i, typing.rs:593/754), killing TyCode binders for pure quotation entirely — genericity lives INSIDE the code as Pi over Type<0>, ordinary MLTT, and map_code became a closed generic template (level 1: 'level-0 slice' means no level variables). Term splices landed as designed (letbox hoisting, constant motives, wk substitutions doing vec.rs's fourteen hand-shifts) and are proven by the quotation suite; map_code needs none because at the generic type the template is RIGID — parametricity plus the length index force the well-typed template to be map, which is why the planned mutated-motive control was unwritable and a swapped-binder routing control replaced it. Surface additions that fell out: head/tail/cons on successor-length vectors, and universe-typed binders registering as type names in lambdas and written function types (not just telescopes). Psi-residency stayed deferred exactly as decided (meta defs are elaborator-held; box-synthesis-gap's static-computation doctrine). Suites: 783 passed, 0 failed. Remaining from the filing: nothing — the three parts (slice, hook, cross-check) all landed; follow-ons live on generators-in-the-language (migration order: the certgen fragment transcriber next) and the deferred list in design doc section 8.
