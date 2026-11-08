---
title: Tactic-only imports: a module uses grind without putting the tactic library in its clients' closure
status: open
labels: [tactics,modules,design]
area: language
milestone: [tac-general]
created: 2026-11-08
updated: 2026-11-08
---

A module that proves something `by grind()` has to `import grind`. The
import puts grind's whole closure (`char`, `string`, `tactic`, `derive`,
`egraph`, `grind`) into that module's world and into the world of every
module that imports it. The proof terms grind returns do not need any of
that. They cite `trans`, `sym`, `cong` and a few small lemmas of grind's own
(`grind::congr`, `congr_fun`, `exfalso`, `elim_false`, `succ_inj`, `defn`),
which could live in `logic`. The tactic is needed while the module is
elaborated. The declarations are not needed afterwards.

This has decided where grind may be used:

- `grind-library-sweep`'s log (2026-11-02) left `Int::neg_add` and
  `Memory::set_set_comm` by hand even though grind closes them. The reason
  given: importing grind into `int`/`memory` "would put the tactic library
  in every client's closure".
- `docs/grind-design.md` §14.5–§14.6: the x86 conversions were taken back
  because of the closure's cost on the bundled native path. Importing
  `tactic` into `x86_64_asm_table` also shadowed that module's own `At`
  with `Note`'s. That is a scope leak into the client's names, not only a
  cost.

[[grind-closure-cost]] and [[tier2-constructor-value-cost]] make the
closure cheaper. This issue makes it not the client's: an import whose
names are in scope only for `by` blocks and tactic arguments, and that does
not enter the importing module's exported closure. Lean 4's `meta import`
and Racket's phase-1 `require` are the precedents.

Design questions:

- **Spelling and scope.** `import grind for tactics;` (or `meta import`).
  The imported names resolve only inside `by …` and tactic-argument
  positions, and are never visible to the module's own declarations.
- **The world a proof is checked in.** The returned term is checked against
  the module's ordinary world. A term that cites a tactic-only declaration
  is refused, with a note that names the declaration. So the lemmas a
  tactic's certificate cites must live in an ordinary import (for grind,
  move its six lemmas into `logic`).
- **Images and caches.** The module image records tactic-only imports
  apart from ordinary ones. Clients load only the ordinary ones. The cache
  key still covers the tactic modules, because a different tactic may
  produce a different term (`docs/module-interface-cutoff-design.md` decides
  whether that is an interface change).
- **Cycles.** A tactic-only import of a module above the importer (`nat`
  using grind, which imports `nat`) stays refused. This issue does not open
  `nat`/`list` to grind.

Done when `int.hthr` proves `Int::neg_add`'s `Succ` step by `grind_using`
through a tactic-only import, the module list of a client of `int` gains no
module, and a negative control shows that a tactic-only name used outside a
`by` is unbound.

## What it assumes from elsewhere
- **[[grind-closure-cost]]** owns the cost of the closure itself. Assumed
  here: only that the cost is paid by the importer and not by its clients
  once this lands.

## Log
- 2026-11-08: `char` and `string` are in the common prelude now (Minus:
  "for `import char; import string;` we can put those in prelude";
  `lib/std/core/common.hthr` exports `Char` and `String`), so every module
  after the facade has them and grind's closure adds `tactic`, `derive`,
  `nat_map`, `egraph` and `grind`. grind's certificate also cites
  `grind::congr_dep` now (docs/grind-design.md §15.1), a seventh lemma to
  move.
