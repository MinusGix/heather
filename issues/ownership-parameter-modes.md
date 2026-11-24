---
title: A parameter's mode in the surface: &T and &mut T on any parameter, kept by the AST
status: open
labels: [ownership,language,frontend]
area: language
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

The surface half of `docs/language/ownership-design.md` §10.3: a parameter's mode is something the language keeps, and `&T` and `&mut T` are written on any parameter. Today `mut` is a parser desugaring with no trace in the AST (`crates/syntax/src/parser.rs` `param_list`, `mut_params`), and a `mut self` method is known only by its `Mutated` result type.

## Scope

- **A mode on `Param`** (`crates/syntax/src/ast.rs`): owned, frozen view, live path. Carried through elaboration and module images (`crates/elab/src/module_image.rs`), and readable by a generator, so the reflector can see what was written. `mut self` records the live-path mode; its elaboration is unchanged.
- **`x: &mut T` on any parameter, several per function.** The result type gathers the parameters' values after the call with the answer, generalising what `mut self` does for one; a call site passes `&mut place` and rebinds each place, by the rules `mut self` calls follow for a receiver (a place rooted at a `let mut` local or a `mut` parameter, field paths included).
- **`x: &T`**: recorded, with no change of meaning (a frozen view means the value).
- **Refusals**, each a declaration under `// expect-error:`: `&mut` of something that is not a place; of an immutable local; the same place passed to two `&mut` parameters (the design's §10.3: a meaning that gives each parameter its own value asks its arguments apart; places that differ only by an index wait for the judgment's `Apart` request).
- `&` is free in prefix position (it is an infix token only). The Heather lexer has the token already, so the linked lexer does not change; say so in the log if that proves wrong.

The spelling is the note's open question §13.1. Build `x: &mut T` and `x: &T`; record alternatives met on the way.

## Done when

Existing `mut self` code is unchanged, the forms above elaborate and are probed in `lib/_tests` with their refusals, a generator can read a parameter's mode, and `docs/language/sequencing-surface-design.md` says what was built.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the judgment that reads the modes. Assumed here: only that it reads them from the reflected declaration.
