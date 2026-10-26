---
title: Make write-elf's build time linear in code size
status: open
labels: [native,cli,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
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
