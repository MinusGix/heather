---
title: Per-instantiation type codes: name a parameterized or value-indexed declaration's lowering at each instantiation
status: closed
labels: [elaboration,representation,performance,design]
created: 2026-09-10
updated: 2026-09-10
---
The wall three issues reached on 2026-09-10. `register_ty_code` names
`⟦D⟧` only for an unparameterized, unindexed declaration
(`crates/elab/src/gendefs.rs`, the `params`/`valparams` guard), so every
instantiation of a parameterized or value-indexed one — `List<BitVec(8)>`,
`Box<Flat>`, `CallMemory(file, stack)`, `FetchedFrom(access, memory, span)`,
`MachineState<M>` — is monomorphized by `lower_instance` into a bare inline
`Type` no reference can stand for. Three consequences, each measured:

- an implicit type argument solved as a code literal (`M := List<BitVec(8)>`)
  is written into the spine's annotations by `apply_implicit`'s discharge as
  `El ⌜Wf…⌝`, and the kernel's own instantiation of the callee's codomain
  yields the same literal, so re-emitting decoded only moves the miss
  ([[unnameable-annotation-occurrences]], 2026-09-10: ~0.3–1.0 s per byte
  level on the x86 certificates; [[elaborator-canonical-type-spelling]],
  same date: "only a reference removes it");
- the emission walker's dominant residue is the boxed literal a `→ Type`
  body or a type argument quotes through `code_of` (578 of 578 findings on
  the five-node x86 module, the `Pair` family on `lib/ir_v1.hthr`;
  [[emission-walker-residual-sites]]);
- `MachineState<M>` is the type every x86 theorem states
  ([[inductive-spelling-codes-nonrecursive]] lever 2).

## Direction (coordinator, pre-charter)

One definition per declaration, not one per instance: a code *function*
abstracted over the declaration's own telescope,
`D#tycode_fn := λ(params…)(valparams…). ⌜⟦D⟧[params]⌝`, registered at
declaration time through the unchanged `push_gen_def` gate (closed λ,
`LocalCtx::nil()`, the `ArityFn` precedent), so a use spells
`El (app(D#tycode_fn^δ; ā))` and an inferred type argument's solution is the
*reference-spelled* code term — which is what makes the kernel's
substitution yield the reference rather than the literal. A closed
per-instance memo keyed by the instantiation is the rejected-by-default
alternative: it would have to mint mid-declaration (unsound: `GlobalVar`s
number from the end of Ψ) or pre-scan for instantiations the elaborator only
learns by inference. The design pass probes both against the kernel before
choosing; the choice is its to make and to justify.

Not relitigated: `lower_instance` stays the identity the recognizers
fingerprint; structural reads keep the inline spelling; emission goes
through `emit_ty` and the walker audits it; guards can only decline
(docs/wf-shape-code-design.md §2.3, §4).

## Acceptance

- `crates/elab/src/wf.rs mod tycode`: a parameterized and a value-indexed
  declaration get a code function; the reference at an instantiation is
  `El` of its application, idempotent, both conversion directions; a
  wrong-argument application is not the instance (negative control); the
  four axes of docs/testing-generated-terms.md on a monomorphized
  constructor value and match.
- An inferred type argument's discharge writes the reference: the
  `Sigma`/`Sigma` (~195/item) and `El⌜⌝`/`Wf` (~185/item) rows of
  `mix_native_loaded_byte` in the conv-miss table are gone or O(1); before
  and after on one furnace box, `--item-timings`, release, `value-metrics`.
- The emission walker's boxed-literal findings on the five-node module and
  `lib/ir_v1.hthr` drop, if `code_of` quotes the respelled type (the design
  decides whether that slice rides along; if not, it says why).
- The reflection boundary still unspells (certgen suite green); module
  images encode the new key; `scripts/bench --check` holds; plain full
  `scripts/test` green.

## What it assumes from elsewhere

- **[[wf-shape-annotation-slots]]** owns the shape-code mechanism and its
  guards. Assumed here: only that a `GenDef` body may be a closed λ
  (`ArityFn`) and that guards decline structurally.
- **[[elaborator-canonical-type-spelling]]** owns the invariant. Assumed
  here: only that the third spelling is the kernel's substitution result.
- **[[unnameable-annotation-occurrences]]** owns the x86 datum. Assumed
  here: only the per-item row counts above, as the before column.

## Log

- 2026-09-10: Chartered (2026-09-10) as one design-then-implement managed round; anchor for [[unnameable-annotation-occurrences]] family 2 and [[inductive-spelling-codes-nonrecursive]] lever 2. Design deliverable: docs/per-instantiation-type-codes-design.md.
- 2026-09-10: Implementation pass landed (2026-09-10; docs/per-instantiation-type-codes-design.md amended in place where the tree forced a change). `GenDef::TyCodeFn(tag)` registers one closed λ over each parameterized or value-indexed declaration's own telescope at the all-`Ty 0` profile (§12 item 4 measured: **0 of 1,544** instantiations over `lib/std`, `lib/` and the x86 example are at any other profile; one `List` at level 1 exists in the `build-x86` path and declines, as designed). The use-site guard recovers the arguments by positional hole-matching against the registered open template and then requires **the template at those arguments** to be the subject syntactically — not a re-lowering, which was tried first and cost 204 s on the mutual-recursion fixtures and blew the suite's 4 GB cap. The inverse landed first (§12 item 3): `gen_app_of`, an `unspell_here` arm and an `unspell_ty_deep` arm, all three by instantiating the template and `decode_deep`ing it. Three more readers had to be told the same sentence, and each was a live failure before it was: `unify_ty` (a syntactic congruence — 63 library declarations stopped inferring their implicits), `resolve_goal_from` ("the goal type is not a class"), and the `Wf` slot pair plus `project_field`'s chain, which must ask the *component* question now that `emit_ty` offers a name for the whole. **Result on the chartered row** (one furnace box, release, `value-metrics`, before and after on the same box): `mix_native_loaded_byte` **9.17 s → 4.38 s** total / **8.00 s → 3.56 s** kernel, per heavy item 1.68–1.87 s → 0.77–0.83 s, and the `Sigma`/`Sigma` (195/item) and `El⌜⌝`/`Wf` (185/item) rows are **gone from every byte item** — the acceptance criterion, met. The emission walker's residue on the five-node module 578 → 260, every remaining slot pre-existing. **Whole-run regression, reported rather than worked around:** the same run's item total went 37.36 s → 43.84 s because a *projection* off a binder whose record type now has a name costs a `Σ`-vs-reference conversion where it used to be a syntactic match (`Sigma`/`El(?)` 1,050 → 15,998 misses); it is the accepted `Sigma`/`El^δ` shape of the closed codes at ten times the count. The fix is a **name for the projection** — `register_rec_projs` over the same telescope, [[theorem-field-projection-oom]]'s device at this round's boundary — not more spelling.
- 2026-09-10: Design pass landed (2026-09-10): docs/per-instantiation-type-codes-design.md. Default direction confirmed by 13 probes; the inverse (whnf re-lowers through the applied head) is mandatory and lands first; ref/inline pairing measured ~1000x ref/ref, so partial routing is a regression; quote slice in, as two separable halves. Before column recorded in §10. Implementation pass launched.
- 2026-09-10: LANDED (2026-09-10), three passes on one dirty tree (docs/per-instantiation-type-codes-design.md §1–§13): GenDef::TyCodeFn per parameterized/value-indexed declaration at the all-Ty-0 profile, the hole-match-then-template guard, the inverse first, the discharge respell; then §13's telescoped projection names (non-dependent spines, simple definitions, local receivers) because the type codes alone regressed projections 30 %; then the fix pass (saturate's arity check had silently declined every function-typed field, closed records included; the OutOfFuel was a reference dear to compute through). build-x86 mix on one box: 34.07 → 18.25 s item, 26.15 → 12.36 s kernel; chartered rows gone; walker 578 → 260. Suite 2543 → 2548. Residue owned by [[per-instantiation-projection-boundaries]].
