---
title: One canonical spelling for every type the kernel compares against itself
status: open
labels: [elaboration,inductives,representation,performance,design]
created: 2026-09-06
updated: 2026-09-13
---

Filed from the 2026-09-06 x86 kernel round. Exact first-difference excerpts
of the expected-vs-inferred conversion misses on the five-node
FunctionIR/x86 module showed one declared type written three ways inside one
module: fully inlined (`Σ(…)((Σ…`, 50–300 K characters), through a named
code (`El (u475^δ)`), and as a boxed code literal (`El «(«Σ…»`). Whenever two
spellings meet, the kernel unfolds and walks the larger one in the value
domain; that was ~4.6 s of the module's ~7.7 s of kernel time. The
registration boundary that leaves the x86 model types unnamed is
[[inductive-spelling-codes-nonrecursive]]; this issue is the invariant that
boundary is a special case of.

The three spellings each have an owner today: the inline lowering is what
the recognizers fingerprint (`lower_instance` is the identity the guards
anchor on — the shape-code round's deliberate choice); the named codes are
`GenDef::TyCode`/`ShapeCode`/`ArityFn` respelled site by site behind
structural guards; the boxed literal is what the code layer writes. Every
site that fails a guard silently falls back to inline, and the kernel is
where the fallbacks are paid for.

## Direction

- Decide the canonical spelling per role (statement, annotation, value,
  code payload) and make the *recognizers* see through names rather than
  the emitters guess which copy the recognizer wants — the reverse of the
  shape-code round's mechanism 3, which moved `whnf` back to the inline
  copy to keep readers spelling-insensitive.
- A checked invariant rather than a convention: a debug-only pass over an
  elaborated module that reports two spellings of one declared type meeting
  in a conversion miss (the round's `Tc::conv_ty` miss sampler, filed under
  [[perf-profile-build-target]], already produces the datum).

## What it assumes from elsewhere

- **[[wf-shape-annotation-slots]]** owns the shape-code mechanism and its
  guards. Assumed here: only that guards decline site by site today.
- **[[inductive-spelling-codes-nonrecursive]]** owns the first concrete
  slice; this issue is not a prerequisite for it.

## Log

- 2026-09-06: First slice landed ([[inductive-spelling-codes-nonrecursive]], 2026-09-06): flat declarations' payloads and suffix sums are named and the whole-type code is spelled over the names; monomorphized Wf copies respell shape and arity alike. The sampler that produces this issue's datum is landed behind value-metrics ([[perf-profile-build-target]]); its residual rows are on [[unnameable-annotation-occurrences]].
- 2026-09-06: Latent look-alike found by [[inductive-spelling-codes-nonrecursive]]'s round: the structural guards compare against lowerings, and a lowering can coincide with a *tag type* (a nullary payload at tag 0 is `Σ(Unit). Unit`, the digit-1 component of every later tag type). Any future guard that names sub-declaration components must be positional or must exclude tag types explicitly; the whole-type guard is safe only because no fieldless single-constructor declaration holds tag 0.
- 2026-09-06: Owners filed for the round's residue: [[tag-types-collide-with-lowerings]] (the structural-guard hazard), [[emission-site-respell-audit]] (the no-new-definitions half of the residual rows), [[conv-miss-sampler-item-attribution]] (the datum's missing column), [[recursive-spine-codes]] (the mechanism's other half).
- 2026-09-06: Second slice landed by [[emission-site-respell-audit]] (2026-09-06): every emitted `App` annotation, the `sup_f`/`elim_Wf` slots and children tuples of monomorphized `Wf`s, and every projection/tuple link written off a decoded code literal now take the reference spelling (`decode_deep` first, then `respell_ty_deep`). The third spelling — the boxed literal a `→ Type` body or a type argument quotes (`code_of` of the inline lowering) — is still written; it no longer shows on the sampler because every consumer decodes it, but it is the remaining place one type is written a third way, and quoting the respelled type instead is this issue's next cheap slice.
- 2026-09-06: Third slice landed by [[emission-spelling-chokepoint]] (2026-09-06): one `emit_ty` every emitted annotation slot goes through, and a walker (`crates/elab/src/emission_walk.rs`) that lists every slot the chokepoint would still change — the checked invariant this issue's Direction asked for, at the elaborator's end rather than the sampler's. Its first listing names the boxed literal as the dominant residue: 578 of 578 findings on the five-node x86 module and the whole `Pair` family on `lib/ir_v1.hthr` are an `El ⌜⟦D⟧⌝` quote somewhere inside a slot that the chokepoint would decode and respell — i.e. the quote layer writing the inline lowering into `→ Type` bodies and type arguments (`code_of`), exactly the next cheap slice the previous entry named. Quoting the respelled type once at `code_of` removes them all; routing each consumer is the whack-a-mole the chokepoint exists to end. The per-site residue is on [[emission-walker-residual-sites]].
- 2026-09-10: A datum from [[unnameable-annotation-occurrences]]'s round (2026-09-10): an implicit type argument solved as a code literal (`M := List<BitVec(8)>`, nothing to name) cannot be spelled consistently at the use — `apply_implicit`'s discharge writes `El ⌜Wf…⌝` into the spine's annotations, and re-emitting them decoded only moves the miss from the arguments' checks (`Sigma`/`Sigma`, `El⌜⌝`/`Wf`) to the Π check (`Pi`/`Pi`), because the kernel's own instantiation of the callee's codomain at that argument yields the literal. Measured a net loss and reverted. The third spelling this issue names is therefore the kernel's substitution result, and only a reference (per-instantiation code) removes it.
- 2026-09-10: Fourth slice chartered (2026-09-10): [[per-instantiation-type-codes]] — a reference for the kernel's substitution result.
- 2026-09-10: Fourth slice landed and closed: [[per-instantiation-type-codes]] (2026-09-10). The kernel's substitution result is now a reference for every parameterized instantiation at the level-0 profile; what the walker still lists (260 on the five-node module, the Pair quote family halved) is the closed boxed literal at slots this issue's quote layer owns.
- 2026-09-12: Round chartered (user, 2026-09-12): the Sigma/El(?) bucket of the reused_callee certificate (14,740 misses / 9.7 s of the 2026-09-12 attribution on [[function-ir-x86-proof-scaling]]; the `Fst`/`Snd` rule's reconstituted Σ meeting the reference `El (app(D#tycode_fn^δ; ā))` a parameterized record's value carries). Elaborator, generator and library only, no kernel change; design doc first with a fresh before table on the current tree; bar is the whole-certificate item total and kernel_gate at or below the before column on the same box with every family row recorded, the bucket as the diagnosis. The quote layer's closed boxed literal ([[emission-walker-residual-sites]]) is in scope only if the trace attributes the bucket to it.
- 2026-09-12: Round refuted (docs/record-projection-reference-design.md §9). The bucket is exactly every global-headed field read of `MachineState`/`StackAccess`/`CallMemory` (confirmed in the compiler: 1,811 fallback exits vs 703 reference exits on the certificate); routing them to the reference removes it (14,682 / 9.16 s → 1,657 / 2.57 s) and pays it back with interest under evaluation — `Vec`/`Vec` 0.007 → 11.8 s, `memory_same_28` OutOfFuel at item 2,991 of 3,476 — because the receivers are the 28-deep state chain the predicate's own comment warned about; the unit probe measured flat reads in separate items and never the chained one. Not landed. Surviving leads: a predicate separating chained from flat global receivers (~a third of the misses are flat `call_stack_access()` rows), and the kernel-side [[conversion-typed-eliminator-congruence]], now the more attractive route since a `Fst`/`Snd` rule that does not reconstitute Σ cannot move a read off the walk.
- 2026-09-13: Refuted round's true owner found and landed (2026-09-13): `register_ty_code_fn` quoted `code_of(template)`, the raw inline lowering, so behind every reference the kernel decoded components that met the chokepoint's respelled annotations one δ at a time — the whole `Sigma`/`El(?)` bucket. Now `code_of(emit_ty(template))` (docs/record-projection-reference-design.md §9.8; per-instantiation design §2 amended). Same box, warm: item total 45.12 → 35.18 s, kernel_gate 35.30 → 25.47 s, steps 35.4 M → 16.1 M, misses identical at 237,888, the bucket 8.62 → 0.62 s at the same 14,682 misses, no bucket grew. Method datum: the sampler classifies a miss by its root head pair; its cost lives in the component spelling after the unfold, which only a before/after on the spelling can attribute.

- 2026-09-15: **Two triggers fired by the telescoped-dependent-projection round** (`docs/telescoped-record-projections-design.md`, implemented 2026-09-15), both of them "the elaborator spells one thing two ways". (1) **A declaration's function-typed value-parameter domain has no name.** `Pi`/`Pi` is now the top head-pair row on `docs/showcase/calc_parser.hthr` — 23 711 / 4.23 s → 47 010 / 4.87 s — a partially applied `Recognized<…>` relation against `Certified`'s `relation` domain, written into the `App` annotations of every named field read. `annotation_type`/`emit_ty` can respell the `Π`'s components and not the `Π` itself; naming it is a new definition kind. That is design §5's own follow-up and its trigger condition ("a top row after the device has landed") is met. (2) **A closed type argument is spelled two ways within one lowering**: a binder's type is a structural read and keeps the inline lowering (`docs/annotation-component-respell-design.md` §2.5's rule), while the same type as an application's *type argument* went through the chokepoint and is `El (D#tycode^δ)`. `instance_match`'s positional matcher therefore recovers two disagreeing codes for one hole and declines — `Cursor` 930, `Certified` 196, `Failure` 105 rows of `hole-match-type-hole/two-occurrences-disagree` on the showcase — and no choice of recovered argument can fix it, because step 2 compares the template at that argument against a subject containing both spellings. See [[type-code-fn-template-stale]]'s 2026-09-15 pass-2 entry and design §2.3 as amended.
