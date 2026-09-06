---
title: One emission chokepoint for annotation spelling, and a walker that finds the next disagreeing site
status: closed
labels: [elaboration,representation,tooling]
created: 2026-09-06
updated: 2026-09-06
---

Filed from [[emission-site-respell-audit]]'s round (2026-09-06). All four of
its rows, and both riders, were one failure: an emission site copied a type
verbatim from wherever it happened to read it — a binder's type, a `whnf`
result, a decoded code — while a sibling site respelled the same type
(`respell_ty_deep`). Every fix was "route this site through
`respell_emitted`", and the invariant now lives in about a dozen call sites
(`application.rs`, `inductive.rs` ×4, `wf.rs` ×3, `gendefs.rs`) plus
docs/annotation-component-respell-design.md §2.4.

## Shape

1. **One chokepoint.** An `emit_ty(cx, ty, depth)` (today's `respell_emitted`:
   `decode_deep`, then `respell_ty_deep`) that every constructor of a `Term`
   or `Type` with an annotation slot goes through, so a new emitter cannot
   forget it. Structural reads keep taking the inline copy — the line of
   docs/wf-shape-code-design.md §4 is unchanged; only the *emitted* slot is
   funnelled.
2. **A walker.** A debug-time (or `value-metrics`) pass over a checked
   declaration's term and statement that flags any annotation slot whose
   content `respell_emitted` would change — i.e. any site still writing a
   spelling the chokepoint would not. Run it on the library in a test, so the
   next disagreeing site is found before the sampler has to attribute it.
   Two sites the audit already knows the walker would list: a `Lam`'s `dom`
   is copied off the expected Π rather than respelled on its own (agreement
   by luck while every Π it meets is respelled), and `build_ctor`'s label
   type at a constructor literal ([[conv-miss-residual-rows]]).

## What it assumes from elsewhere

- **[[elaborator-canonical-type-spelling]]** owns the invariant. Assumed
  here: only that "one spelling for every type the kernel compares against
  itself" is the target; this issue is the mechanism that keeps it.
- **[[emission-site-respell-audit]]** (closed) owns the audit's numbers.

## Log

- 2026-09-06: DONE (2026-09-06). **Chokepoint**: `Elaborator::emit_ty(cx, ty, depth)` (gendefs.rs; `emit_ty_in` for the application scratch world) is today's decode-then-respell, and every emitted slot the elaborator writes goes through it: the statement cascade and the body's outer λs (lib.rs), `respell_spine`, `build_ctor`/`build_elim_wf`/`build_children`'s `Wf` fallbacks, the match motive, `build_fields_skel`, `projection`, `project_field`, `respell_application_annotations`, the fording inversion's rebuilt `sup_f` (forded.rs, which had no fallback), and now `Term::Refl { ty }` and both `Term::Lam { dom }` emissions (expr.rs, through a new `EmissionElab` supertrait). Structural reads unchanged. **Walker**: `crates/elab/src/emission_walk.rs`, exhaustive over the kernel's variants with no wildcard arm, scope exactly the chokepoint's (no code payloads, no terms inside types), run behind `enable_emission_walk` in `elab_decl_inner` on the pair the kernel is handed; printed beside the sampler by `scripts/measure-x86-conv-miss` and asserted over `lib/ir_v1.hthr`'s closure in `the_full_ir_library_checks`, plus a fast-lane corpus with planted negative controls (`wf.rs mod tycode`). **What it listed**: library 263 findings before, 214 after — `Lam.dom` 49 → 0 (the judgment call resolved to "fix"), every other slot unchanged to the unit; x86 module 578, all but one an `El ⌜⟦Instruction⟧⌝` quote inside the slot. `Refl.ty` was never listed on the x86 module and the `Id`/`Id` row did not move; the constructor label has no slot to spell ([[conv-miss-residual-rows]], closed). **Acceptance**: every emitted annotation goes through one function — yes; the walker reports none on the library — no: 214 remain, listed by slot in `WALK_RESIDUE` and owned by [[emission-walker-residual-sites]] (two already attributed by a probe: `project_field`'s fallback re-reads components off the whnf of the whole-type reference, and `elab_arm`'s alias projections were never routed). Closing on the mechanism; the residue has its owner. **Numbers** (furnace, same tree, kernel/wall): 0.725 s / 1.409 s → 0.700 s / 1.406 s, box noise; rows on the closed issue. Full `scripts/test`: 2454 passed, 0 failed, 5 ignored (2450 before; +2 tests here, +2 elsewhere in the tree).
