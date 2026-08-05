---
title: Supf/ElimWf shape slots are the forded residual: no code names a Wf's shape component
status: open
labels: [elaboration,performance,inductives]
created: 2026-08-05
updated: 2026-08-05
---

The third defect on `forded/declared-index-tags`'s curve, named by [[family-types-as-code-defs]]'s implementing round (2026-08-05) after the code definitions moved every other forded family and left this one at slope 2.61 -> 2.62.

`Term::Supf`/`Term::ElimWf` carry `shape: Rc<Type>` — the `Wf`'s **shape component** (the sum-of-Σs), not the whole `Wf` (`crates/kernel/src/term.rs:514`). The registered codes (`SkelCode`/`IdxCode`, `crates/elab/src/gendefs.rs`) name whole types, so an `El (code^δ)` reference cannot fill a shape slot: decoding the whole-type reference yields a `Wf` whose shape is `El` of the *inline* shape code, which is no smaller. The design's §1.4 `Supf`/`ElimWf` bullet (`docs/family-type-code-defs-design.md`) was therefore unimplementable as written, and those slots were left inline — the one deviation of the implementing round.

Where it costs: the `sup_f` the declared-index inversion rebuilds per index branch (`zj` in `forded_arm_a_decl`, `crates/elab/src/forded.rs`) carries a Θ(n) shape annotation and is instantiated several times per branch (equation domain, motive instantiations, no-confusion transport) across Θ(n) branches — Θ(n²) emitted per form-A arm, which is exactly `declared-index-tags`'s unmoved exponent. The skeleton-side twin (`Supf` per constructor value / arm rebuild, `ElimWf` per match) is the residual over `computed-arms`'s 2.54.

The fix shape, if a round takes it: a **shape code** definition per declaration (`D#shape := ⌜shape⌝`), spelled `El (D#shape^δ)` in the slots — same gate, same best-effort discipline, and the kernel is already indifferent (typing builds a `Type::Wf` from the slots and hands agreement to conversion; the ι-rule only clones them). Whether the conversion side then pays repeated δ+decode per unfold instead — the other candidate reading of the unmoved slope, since the gate is 95–98% of these fixtures — is the first thing that round should measure before writing anything.

## What it assumes from elsewhere

- **[[family-types-as-code-defs]]** owns the whole-type code scheme and the recognizer's nominal branch. Assumed here: only that `SkelCode`/`IdxCode` stay whole-type codes.

## When

Triggered: the next time `forded/declared-index-tags` or `computed-arms` matters — one deliberate round, per the accumulator discipline.
