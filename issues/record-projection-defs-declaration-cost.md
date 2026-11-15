---
title: Naming a big record's projections costs seconds at its declaration
status: open
labels: [elaborator,performance]
area: language
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

- 2026-09-15: **A second family of records now pays this.** `docs/elaborator/telescoped-record-projections-design.md` §7: the dependent *telescoped* device registers `3·nfields + 1` Ψ bindings per record, so every record in `lib/std/parser` and the prelude's own `CollectionLiteral<A>(n)` joins the closed dependent ones. Declaration items, parent → changed (release + `value-metrics`, W=1, one furnace box): `probes/t_pc1..4`'s `Cur<T>(source)` (3 fields) 0.5 → 6.5 ms, its `Cert<T>(source,begin)` (4 fields, equalities over `Cur` projections) 2.7 → 90.3 ms, and the real `lib/std/parser` `Certified<T,A>(source,begin,relation)` 8.4 → 866.4 ms. The cost does **not** grow with how deeply a client chains the record: it is identical across `t_pc1`…`t_pc4`. Against it, the same files' use sites go 11.0 → 6.1 ms, 440.5 → 23.8 ms, 8058.5 → 88.2 ms and an 8 GB allocator abort → 266.4 ms, and `docs/showcase/calc_parser.hthr`'s whole-file serial time falls 137.5 → 123.3 s with the library's registration paid inside it. Per §7 the cost lands on library declarations, so a cached client replays it rather than repaying it. The three routes this issue lists are unchanged and unattempted here; the round adds a customer, not an argument. Numbers on [[parser-certified-composition-cost]].
