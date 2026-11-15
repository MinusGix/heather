---
title: Audit every annotation emission site for spelling one type two ways
status: closed
labels: [elaboration,performance,representation]
created: 2026-09-06
updated: 2026-09-10
---

The cheap half of [[unnameable-annotation-occurrences]], split out because it
needs no new definitions. [[inductive-spelling-codes-nonrecursive]]'s round
removed 3 s of a 8.5 s module by making one emission site agree with another
(`respell_ty_deep`'s `Wf` arm now respells the arity's `Case` annotations
with the shape): the kernel had been walking an inline copy against a
respelled copy at every well-formedness check, and "spell alike" beat
"spell smaller" — the shape-code round measured the same
(docs/inductives/wf-shape-code-design.md §3.2).

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
inline copy (docs/inductives/wf-shape-code-design.md §4's line). Candidates to check
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

## Log

- 2026-09-06: FIXED — all four rows, measured before and after (furnace, dev profile, `HEATHER_FUNCTION_IR_X86_NODES=5`, `scripts/measure-x86-conv-miss`; before is master be13d6e plus the attribution column only). **Attribution → sites** ([[conv-miss-sampler-item-attribution]]'s column, plus a temporary term-form stack and backtrace in the sampler, not landed): (1) `Sigma`/`Sigma` 450 / 0.493 s and (2) `Pi`/`Pi` 150 / 0.275 s were one site: an `App` whose callee is a **local binder** copies `dom`/`cod` off the binder's inline type, and where that application is embedded in a *statement* — `placed_after_binary`'s `equation: … = operation(…)`, `GprOnlyStep`'s field `run(state.gprs)` — it met the cascade-respelled twin at every use (the section `bitvec::band(64, ·, ·)` substituted for `operation`, whose binder types are copied off the respelled Π; the Σ binder's own respelled type). (3) `Sum`/`Sum` 312 / 0.094 s: `build_ctor`'s `sup_f` slots for a **monomorphized** `Wf` (`List<Node>`) stayed inline while the label's injections respelled; after that, 300 of them re-attributed to `build_elim_wf`'s inline arity, which the kernel rebuilds as `Fin(n[ℓ/x])` at every eliminator reduction and which `project_field` then wrote into a `.right` chain against the value's respelled label. (4) `Sigma`/`El⌜⌝` 154 / 0.123 s: a record type arriving as a **decoded code literal** (`RegionHolds(…)`'s `→ Type` body, `∧` inside) whnf's one level per link, and the projection chain wrote each `snd_ty` as the undecoded literal of a tail whose next link's annotations were its decode — the kernel evaluated the 216 K-character literal once per link; the same shape at `values(64, id)` off `Valuation()`'s quoted body (`El ⌜⟦BitVec(64)⟧⌝` against the respelled Σ). **What landed** (docs/elaborator/annotation-component-respell-design.md §2.4): `ExplicitArgElab::respell_application_annotations` — every emitted `App`'s `dom`/`cod` in `apply_explicit`/`apply_implicit` (scratch-world references shifted past the metas, `respell_ty_deep_in`), the continued-with type still structural; `inductive::decode_deep` + `respell_emitted` (decode, then respell) at `project_field`'s fallback walk, `projection`, `build_fields_skel`, `respell_spine` and the application annotations; `respell_ty_deep`'s `Wf` arm as the slot fallback in `build_ctor`, `build_elim_wf` and `build_children` when `wf_slot_refs` declines. No structural reader changed; no new GenDefs. **Numbers** (kernel / wall): 2.043 s / 2.741 s → **0.869 s / 1.743 s**. `Sigma`/`Sigma` 450 / 0.493 s → 20 / 0.001 s; `Pi`/`Pi` 150 / 0.275 s → 30 / 0.016 s; `Sum`/`Sum` 312 / 0.094 s → gone; `Sigma`/`El⌜⌝` 154 / 0.123 s → gone; riders: `Wf`/`Wf` 56 / 0.131 s → 7 / 0.016 s, `El⌜⌝`/`Sigma` 212 / 0.056 s → 112 / 0.012 s. Top rows now: `Id`/`Id` 49 / 0.189 s (`refl` at statements whose endpoints genuinely compute — not a spelling pair), `El(?)`/`El(?)` 23 / 0.078 s, `El^δ`/`Sigma` 1,880 / 0.077 s and `El^δ`/`Sum` 8,587 / 0.070 s (a constructor literal against a respelled field type: one δ and a compare each, the cost the reference spelling is meant to have). **Tests**: three in `wf.rs mod tycode` on docs/testing-generated-terms.md's axes — the local-callee `App` pinned as a reference on a closed and an open (`[T; n]`) domain, the statement-embedded `op(a)` pinned and its section-substitution use checked, literal/neutral computation and a false-equation control; a monomorphized `sup_f`'s shape pinned *equal* to its label's `inr`/`inl` annotations (closed and open instance, the child too); a projection off `El ⌜⟦Pr⟧⌝` pinned with each link's stated pair type equal to the previous link's `snd_ty` instantiated. **Residue, with owners**: the quote layer itself still quotes the inline lowering into `→ Type` bodies and type arguments (`code_of`); consumers now decode it, so it is no longer a measured row, but it is the remaining place one type is spelled a third way — [[elaborator-canonical-type-spelling]]. Family (1) of [[unnameable-annotation-occurrences]] (fn-typed-parameter `App`s) is taken by this round; family (2)'s per-instantiation copies remain, now spelled consistently rather than named. A written lambda binder annotation is still copied off the expected Π rather than respelled on its own — fine while every Π it meets is respelled; noted, no owner needed.
- 2026-09-06: Final verification on the landed tree: plain full `scripts/test` on furnace — `== suite: 2450 passed, 0 failed, 5 ignored ==` (2447 → 2450, the three new tests); `scripts/test --fast` before it 2320 / 0. Five-node module re-measured on the same tree after the suite: kernel **0.643 s** (wall 1.30 s; bucket counts identical to the 0.869 s run — box noise). Closing; residue is owned above.
- 2026-09-10: A fifth row, found by [[unnameable-annotation-occurrences]]'s round (2026-09-10): `project_field`'s fallback walk read its `Fst`/`Snd` annotations off the whnf of the record's `El (D#tycode^δ)` reference, i.e. the registry's inline lowering, and the walker never saw it because the corpus projected no non-dependent-spine record. Fixed by respelling the components (one `emit_ty` each); the new tycode test projects one.
