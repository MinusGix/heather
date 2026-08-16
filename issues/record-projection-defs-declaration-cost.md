---
title: Naming a big record's projections costs seconds at its declaration
status: open
labels: [elaborator,performance]
created: 2026-08-15
updated: 2026-08-15
---

Spun off from [[theorem-field-projection-oom]], whose fix registers three Ψ definitions per Σ spine entry of a dependent, unparameterized record — the tail family (as a code), the field's projection, and the tail — at the record's declaration (`crates/elab/src/gendefs.rs`, `register_rec_projs`). Each faces the gate like any other definition, and for the 11-field record `datarepr` generates for `List<Tok>` the whole registration measures ~3.0 s in a release build. Checking that record's *whole lowered type* once, by contrast, is ~8 ms (its `D#tycode` registration) — so the definitions cost some 350× what the material in them is worth.

Where it goes, as far as the fix round measured it: not the walk (microseconds) and not the term sizes (RSS stays ~70 MB, linear in the record). It is the kernel work each gate check does on a statement that mentions the *earlier* projections: reaching a Π or an Id endpoint under one of them means reducing `El (D#projᵢ^δ v)`, which unfolds a chain as long as the spine — every link copying its annotations — and gets stuck at the neutral `v` at the bottom. `perf` shows no single hot spot: ~12% `ShiftGlobal` (definition bodies being rescoped per unfold, plus the walk's own re-scoping after each push), the rest diffuse `malloc`/`free` and NbE work in `eval`/`conv`.

Two shapes were tried and measured in the fix round; neither is the answer:

- Raw `sndʲ` spines instead of named tails (one definition per field): 13 s — the kernel re-checks the whole spine below every level.
- Naming the Σ tail family as a **code** (what landed): 3.0 s, from 3.4 s. It made the *statements* local, which is why it landed, but it does not stop the reductions that a *body* check triggers.

Effect on the suite as landed: `scripts/test --fast` 402 s → 436 s of CPU, of which ~23 s is the new regression file — so ~+3% on everything that existed, concentrated in the `datarepr`/`reprgen`/`obligation-records` tests that declare a generated `Repr_*` record. A guard keeps every non-dependent record at zero cost (`record_spine_is_dependent`).

Routes worth weighing when this comes up:

- Register lazily, at the first projection of a field, rather than at the declaration. Blocked today by the elaborator's expression path being `&self` throughout; `meta_pushed`'s `RefCell` is the precedent for the alternative.
- Make an unfold cheap enough that the chain does not matter — the annotations copied per link are what makes each one expensive.
- Let a conversion decide `D#projᵢ^δ v ≡ D#projᵢ^δ v` on the spine without unfolding either side, which is the comparison the checks actually keep asking for.
