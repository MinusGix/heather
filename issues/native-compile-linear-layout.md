---
title: Make write-elf's build time linear in code size
status: closed
labels: [native,cli,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-27
---

Split from [[native-compile-capacity]], which made `write-elf`'s memory flat
in code size and left its time quadratic. Two families of certificate
statements walk the whole program once per item, and one constant is large
enough to dominate below them.

- **Layout stretches** (`{p}_unique_k`, `_lands_k`, `_named_k`, `_landing_k`,
  `_naming_k`, `_fresh_k` in `crates/cli/src/native/elf.rs`): each stretch of
  `STRETCH` items proves its part of `Prog::laid_out` by `refl`, and each
  label lookup (`asm_target`, `prog_len` under `jumps_land_in`,
  `targets_named_in`) walks the whole program. Items × program = quadratic.
- **Byte pieces** (`{p}_piece_k_is`, and the fork's `piece_numbers_k`): each
  piece's encoding resolves its jump targets through the same whole-program
  lookups. At cat_x16 (about 16 KiB of code) the first piece runs out of
  kernel fuel, so past about 8 KiB this is a wall, not only a cost
  ([[native-compile-capacity]]'s log).
- **Literal elaboration** (`{p}_at_k`, paid by both the read module and the
  certificate): linear, but each `At`/`Start` constructor costs about a
  hundred `instance_match` calls in gendefs (per-instantiation type codes,
  `crates/elab/src/gendefs.rs`). At cat_x8 it is as large as any one
  stretch family, and it is paid twice.

## Directions

- **Prove `laid_out` once for every emission**, not per program: a theorem
  over `Stmt::emit` that its output names labels uniquely, lands every jump
  and names every target, given the shape's counter discipline. This is the
  compiler-proved-once direction ([[program-logic-design]]) and removes the
  stretch family outright.
- **A verified label table** for the byte pieces: build the label → offset
  map once (a bit-trie over label numbers, or a `List` indexed by label since
  emission numbers labels densely), prove it agrees with `asm_target`, and
  look jump targets up in it.
- **Elaborate the code literal once**: the read module and the certificate
  each elaborate `{p}_at_k`; and the per-constructor `instance_match` cost is
  worth its own elaborator issue if it shows up beyond write-elf.

## Done when

`write-elf` time grows linearly in code size (the families above scale with
items, not items × program), and `cat_x8` builds inside the suite's CPU
rail, so [[native-compile-capacity]]'s test can run it.

## What it assumes from elsewhere

- **[[native-cat-executable]]** owns `write-elf`'s certificate shape.
  Assumed here: only that `{p}_laid` may be proved by any route that states
  the same `laid_out`.

## Log

- 2026-10-27: design chosen, a verified label table (the second direction),
  because the byte pieces need fast lookups whichever way `laid_out` is
  proved, and one table serves both. Per program, Rust writes two decision
  trees as Heather functions (comparisons on literals, depth logarithmic in
  the label count): `slot(name) = (index, offset)` and `name_at(index)`.
  One pass from the program's end, carrying the item index and the offset
  (so nothing recomputes `prog_len`), checks at each item that `name_at`
  gives its name, that a named item's `slot` gives its index and offset,
  that its jump lands by the table's offsets, and that its target is named
  (`name_at(slot(t).index) = t`, index in range) and nonzero. Proved once:
  the pass implies `names_unique`, `asm_target(p, n)` equals the table's
  offset for every nonzero `n`, and so `jumps_land` and `targets_named`:
  `laid_out` follows. The pass is stated a stretch at a time over the
  literal's cut definitions, so a stretch evaluates only its own items.
  The byte pieces then read labels from the table, through a congruence
  lemma (`asm_code` with labels that agree on every jump target), over an
  offset-carrying `asm_code` variant. Cost per item: logarithmic.
- 2026-10-27: built. `lib/std/arch/x86_64/x86_64_asm_table.hthr` holds
  `LabelTable`, the pass (`checked`, and `checks_last`/`checked_back` a
  stretch at a time), `laid_out_of`, and `piece_by` (bytes by the table
  over `asm_code_ending`, which carries offsets down). Probes in
  `lib/_tests/std/arch/x86_64/x86_64_asm_table_tests.hthr`, two wrong
  tables among them. `crates/cli/src/native/labels.rs` writes the table
  and the statements; the literal is also cut where each byte piece's
  window ends, so a piece's window and the pass up to it are definitions.
  Width one, cloud box, fresh copy of a warmed cache:

  | probe   | code   | before   | now   |
  |---------|-------:|---------:|------:|
  | cat_x4  | 4.3 KB | 204 s    | 69 s  |
  | cat_x8  | 8.2 KB | 572 s    | 111 s |
  | cat_x16 | 15.9 KB | refused (fuel) after 2490 s | 249 s |
  | cat_x60 | 58.1 KB | —       | 892 s, 3.5 GB run growth |

  Time is linear now. At cat_x60 the code literal's two elaborations
  (`at_k`, read module and certificate) are 407 s, the pass 116 s, the
  byte pieces 110 s and their `upto` chain 61 s; the largest memory row is
  the shape read (2.7 GB, linear, one evaluation of every leaf's
  emission). Those are [[write-elf-build-constants]]. `compile-x86`'s
  certificate (`verified::layout`) still uses the stretch families; it
  builds per-function programs, small so far. Closed: cat_x8 builds in
  `crates/cli/tests/native_cat.rs` (`larger_program_runs_as_cat`).
