---
title: Name the shapes and suffix sums of non-recursive and parameterized declarations
status: closed
labels: [elaboration,inductives,performance,representation,x86]
created: 2026-09-06
updated: 2026-09-10
---

Found by the 2026-09-06 x86 kernel round ([[function-ir-x86-proof-scaling]]).
After the kernel stopped re-comparing stored Π/Σ annotations, the five-node
FunctionIR/x86 module's kernel time was ~7.7 s, of which ~4.6 s was two
families of expected-vs-inferred type conversions that miss the syntactic
shortcut and then walk 50K–300K-character types in the value domain:

- `El (D#tycode^δ)` against the same declaration's **inlined** sum-of-Σs
  (constructor labels checked at a `Wf`/sum type; ~2.0 s / 1,988 queries), and
- a **suffix sum** spelled inline against the same suffix spelled with a
  named component (`inr` chains of a 16-constructor `Gpr`, 11-constructor
  `Instruction`; ~2.6 s / 813 queries).

The exact diffs showed one type spelled three ways in one module: fully
inlined (`Σ(…)((Σ…`), through a named code (`El (u475^δ)`), and as a boxed
code literal (`El «(«Σ…»`). The shape-code machinery of
[[wf-shape-annotation-slots]] (`GenDef::ShapeCode`/`ArityFn`,
`register_wf_slots`) is registered only for **recursive** declarations, and
`register_ty_code` only for **unparameterized** ones. Every x86 model type is
non-recursive (`Gpr`, `Instruction`, `Flags`, `Gprs`) or parameterized
(`MachineState<M>`), so none of them gets a name below the whole type, and
`inl`/`inr` annotations spell the suffix sums out at every level — O(n²) in
the constructor count per literal, paid in the value domain.

## Levers

1. Register suffix-sum codes (`D#tail_k`) and per-constructor payload codes
   for non-recursive unparameterized declarations, and spell the `inl`/`inr`
   annotations of constructor values and `case` spines with them. Each
   level then costs one δ and an `==`.
2. Monomorphized codes for parameterized declarations, keyed by the
   instantiation ([[unnameable-annotation-occurrences]] names the same
   copies): `MachineState<M>` is the one every x86 theorem states.
3. One spelling, not three: whichever of inline / named / boxed-code the
   elaborator writes for a shape, it should write everywhere the kernel
   will compare it against itself.

## Acceptance

- The five-node module's `El` vs sum and sum vs sum shortcut misses are
  gone or O(1) each; measure with the per-bucket miss timing the round
  used (temporary instrumentation at `Tc::conv_ty`, not landed).
- No change to the inline lowering the recognizers fingerprint
  (`lower_instance` stays the identity, per the shape-code round).

## What it assumes from elsewhere

- **[[wf-shape-annotation-slots]]** owns the shape-code machinery. Assumed
  here: only its registration boundary, which this issue widens.
- **[[function-ir-x86-proof-scaling]]** owns the workload.

## Log

- 2026-09-06: The invariant this boundary is a slice of: [[elaborator-canonical-type-spelling]].
- 2026-09-06: **FIXED — both slices, measured first** (furnace, dev profile, `HEATHER_FUNCTION_IR_X86_NODES=5`; the before column is master 5da7982 with only the sampler added, same box, same session). **Measurement first.** The `Tc::conv_ty` miss sampler ([[perf-profile-build-target]], now landed behind `value-metrics`) on the five-node module before any change: kernel 8.45 s; `El^δ` vs `Sum` 1,968 queries / 2.30 s (expected `El (D#tycode^δ)`, inferred the label's inline sum); `Sum` vs `Sum` 813 / 2.99 s. The second family was NOT the `inr` chains of `Gpr`/`Instruction` this issue guessed: its first-difference excerpt is the shape of a **monomorphized recursive** instantiation — `List<Gpr>`/`List<Instruction>` — whose `respell_ty_deep`'d copy had a respelled shape (`Σ(tag). Σ(El (Gpr#tycode^δ)). Unit`) over an **inline arity** (the constant case tree's `Case` annotations still spelled `⟦Gpr⟧`/`⟦Instruction⟧` out), so the kernel walked the inline component under `x : shape` at every well-formedness check of every `Wf` occurrence of every `Cons`. **What landed.** (1) Slice 1, lever 1: `GenDef::PayloadCode(tag, k)` = `D#payloadₖ := ⌜⟦cₖ⟧⌝` (emission spelling: embedded field types as `El (F#tycode^δ)`) and `GenDef::SuffixCode(tag, k)` = `D#suffixₖ := D#payload_{k+1}^δ + D#suffix_{k+1}^δ` (the last tail is the last payload), registered by `register_spine_codes` for a **non-recursive**, unparameterized declaration with ≥ 2 constructors, all-or-nothing, guarded by the inline spine kept in `GenDefs::spine_codes` (a `DeltaEvent::GenSpineCodes`, image magic bumped to 4); `D#tycode`'s body for such a declaration is now `D#payload₀^δ + D#suffix₀^δ` rather than the inline literal, so one δ exposes exactly what a label carries. `respell_spine` takes the references **by position** (one structural comparison per component), `respell_ty` scans them as a fallback, `unspell_here`/`unspell_ty_deep` invert them, `Elaborator::whnf` unspells the two components of a `Sum` the kernel decoded (mechanism 3 one level down), and the display path (`display_shape`, `ctor_value`) sees through them — the omega speller broke on `OfNat(1)`'s `inl` annotation until it did. (2) Slice 2, taken as consistency rather than as monomorphized codes: `respell_ty_deep`'s `Wf` arm now respells the arity's `Case` annotations with the shape (`respell_arity_at`, inverse `unspell_arity_deep`) or declines the whole `Wf` — one spelling end to end, no new definitions. **Numbers.** Kernel 8.45 s → 6.28 s after slice 1 (`El^δ` vs `Sum`: 1,968 / 2.30 s → 8,586 / 0.069 s — more queries, each one δ and an `==`; `Sum` vs `Sum` unchanged, which is what re-attributed it) → **2.86 s** after slice 2 (`Sum` vs `Sum` 813 / 3.1 s → 312 / 0.127 s; module wall 10.2 s → 3.8 s; `execution` category 3.85 s → 0.135 s kernel). Exact rendered size, a `Gpr`/`Instruction` fixture: constructor value `AddRR(Rdx, R9)` 8,566 → 1,100 chars; an eleven-arm `match` body 26,122 → 19,041. Recognizers unchanged; `lower_instance` unchanged. **Residual (the sampler's next rows, 2026-09-06, all named spellings meeting inline copies that no registration covers):** `Sigma` vs `Sigma` 450 / 0.66 s — a value-indexed record instance (`BitVec(64)`'s `Σ(tag). Σ(Vec(⟦Bool⟧; 64)). Unit` inline vs `Vec(El (Bool#tycode^δ); 64)`); `Pi` vs `Pi` 150 / 0.40 s — `Gprs`'s function-typed field `Gpr → BitVec(64)` inline vs respelled; `Sum` vs `Sum` 312 / 0.13 s — a 54 K-char inline copy vs a named one; `Sigma` vs `El⌜⌝` 154 / 0.15 s — the 216 K-char `MachineState<M>` instance against its boxed code literal. Logged on [[unnameable-annotation-occurrences]] (monomorphized and value-indexed copies) and [[elaborator-canonical-type-spelling]] (the invariant). Lever 2 as written — per-instantiation codes — was scoped and not taken: a generated definition is a Ψ push, and every `GlobalVar` in the declaration being elaborated is numbered from the end of Ψ, so a code minted at a *use site* would renumber the term under construction; it needs a pre-pass over the declaration's instantiations, which is that issue's design question, not this slice's. **Tests:** eight in `wf.rs mod tycode` on docs/testing-generated-terms.md's axes — the registration boundary (flat yes, recursive and parameterized no; the last tail has no definition), what the references are with both conversion directions, the whole-type code's decode through its spine and its unspell at `whnf`, look-alike negatives (a twin declaration's components under the wrong tag, a forged payload, a forged suffix), the constructor value and the `match`'s `Case` tree pinned structurally, the four axes with a false-equation control, and the monomorphized `Wf`'s shape and arity respelled alike. `module_delta`'s journal test covers the new event.
- 2026-09-06: Correction from the first full `scripts/test` (81 failures, all one cause): the round's first draft let `respell_ty` fall back to a **scan** over a declaration's registered spine components, and the declaration with nominal tag 0 (`Bool` in most fixtures) has the nullary payload `Σ(Unit). Unit` — structurally the digit-1 component of every later declaration's *tag type*. The deep walk of the statement cascade therefore spelled the tag types inside every later monomorphized lowering as `El (Bool#payload₀^δ)`: convertible, and unreadable by `tag_of` (`Some(5) : Option<Nat>` — "not the expected type here"). Fixed by handing out payload/suffix references **by position only** (`spine_refs_by_position` at `respell_spine`, where the whole spine's tag says whose components they are); `respell_ty` is the whole-type guard again, and a test pins the look-alike. Residue worth one sentence on [[elaborator-canonical-type-spelling]]: the same coincidence exists latently for the whole-type guard — a fieldless single-constructor declaration at tag 0 has the whole lowering `Σ(Unit). Unit` — and is only ever avoided because the prelude's first declaration is not that.
- 2026-09-06: Final verification on the landed tree (scan removed): plain full `scripts/test` on furnace — `== suite: 2447 passed, 0 failed, 5 ignored ==` (2438 → 2447, the nine new tests). Five-node module re-measured on the same tree: kernel **2.02 s** (wall 2.73 s; bucket counts identical to the 2.86 s run — the difference is box noise, not the scan), `El^δ` vs `Sum` 8,586 / 0.049 s, `Sum` vs `Sum` 312 / 0.094 s; the top rows are now the residual family logged on [[unnameable-annotation-occurrences]] (`Sigma`/`Sigma` 450 / 0.49 s, `Pi`/`Pi` 150 / 0.27 s).
- 2026-09-10: Lever 2 landed: [[per-instantiation-type-codes]] (2026-09-10) names MachineState<M> and every other level-0 instantiation through a code function.
