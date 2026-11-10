---
title: A std prelude facade every module imports implicitly
status: open
labels: [modules,stdlib,ergonomics,design]
area: language
created: 2026-11-03
updated: 2026-11-10
---

Every library module and client writes the same import lines: on average a
module imports eleven modules, almost four of them from `logic`, `bool`,
`nat`, `option`, `list`, `pair`, `algebra`. Decided with Minus (2026-11-03):
a curated **std prelude facade** that every module imports implicitly, in
place of "all of std sees all of std".

## Shape

- `lib/std/prelude.hthr`: a facade (docs/modules-design.md §3.4) whose
  `export` lists name the everyday surface of the core modules: the types
  and their constructors (`Bool`, `Option`, `List`, `Pair`), the logic
  connectives, the `algebra` classes (`Numeral`, `Default`, `Cmp`, the
  monoid ladder) and the common methods. A list, not whole modules, so
  `nat`'s and `int`'s `le_trans` do not both become bare names everywhere.
- The loader adds `prelude` as an implicit import of every module **outside
  the facade's own closure**; the modules the facade exports from import
  explicitly, as today, and are exempt without a marker. A module may still
  import a core module directly: an export names the same declaration, so a
  name reached both ways is one hit, not an ambiguity.
- Where `issues/feature-implicit-module-dependencies.md`'s "qualified-only"
  visibility lands, the facade is its home.
- The elaborator's own prelude (`crates/elab/src/prelude.hthr`) stays the
  language's: the classes the syntax needs a fixed identity for. A client
  checked without the library on its search path gets that one only.

## Cost, measured 2026-11-02 on the cloud box

- The facade's closure is already in almost every module's: over the 304
  lib modules only 73 closures grow (43 of them by `algebra` alone), and the
  core files change a few times a month. Checking the closure cold is a
  fraction of a second; replaying it warm, about a tenth of one.
- Keep `int`, `omega` and `bitvec` out: with them 225 closures grow.
- The rejected alternative, for the record: an umbrella over all of std costs
  minutes of CPU cold, and replaying its images warm took about a minute for
  a one-line client, mostly the analysis/float stack. Inside std the
  same idea is an import cycle, which one Ψ telescope collapses into one
  unit (no per-module images, cutoff or parallel build). Minus notes it is
  more feasible with parallelised definitions; not this issue.

## Done when

- A new module with no imports uses `Option`, `List`, `True`, a numeral at
  `BitVec` via `import bitvec;` alone, and an `algebra` class, by name.
- The library's import lines for the facade's modules are removed where the
  facade covers them (`scripts/lib-paths --fix`-style sweep), and the
  library gate passes with the exact image lane run once (image keys move).
- `issues/prelude-option-and-friends.md` and
  `issues/literal-classes-need-importing.md` are re-read against it.

## What it assumes from elsewhere

- **[[numerals-without-algebra-import]]** owns the syntax classes read by
  identity. Assumed here: only that a literal does not need its class's name
  in scope, so the facade need not export it for literals to work.

## Log

- 2026-11-03: 2026-11-03: Built (thread 'Design a shared common prelude'): `lib/std/core/common.hthr`, implicit for every module later than it in a run's order (loader, `semantic::module_imports`, elaborator agree). Two rules the facade needed, decided with Minus: a type exported through a facade carries its own module's members (read at lookup), and the prelude's closure is visible qualified-only (instances, designations, `nat::…`). docs/modules-design.md §3.5. Not yet done: removing the now-redundant import lines across lib (a mechanical follow-up; explicit imports stay valid since a facade name is the same declaration). Probe: lib/_tests/std/core/common_tests.hthr.
- 2026-11-10: Minus asked (2026-11-10, issues/linarith-rat-without-ordered-field-import.md) for the ordered-field material the arithmetic tactics name to live in the prelude: common.hthr now has a plain `import ordered_field;` (no export), so ordered_field, semiring, order, int, omega, morphism and mono_laws are qualified-only visible everywhere. This reverses the 'keep int and omega out' line above for those two: of 246 non-test lib modules, about 200 gain ordered_field in their closure, about 120 omega and about 60 int. The seven modules are now inside the prelude's closure and no longer see it.
