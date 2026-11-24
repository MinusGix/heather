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

## Log

- 2026-11-24: Built (docs/language/sequencing-surface-design.md §24). **A mode on `Param`** (`ParamMode::{Owned, View, Path}`, `crates/syntax/src/ast.rs`), carried to `ParamMeta::mode`, both image encodings (`HTHMOD`/`HTHIFC` versions bumped; round-trip test `module_image::parameter_modes_roundtrip_and_replay`) and a generator: `tactic::modes(g)`, request `Modes`, one `ParamMode` (`ByValue`, `FrozenView`, `LivePath`) per parameter of the table, type parameters included, lined up with the `λ`s `body(g)` opens. `mut self x: T` records `Path`; `self x: &mut T` is accepted as the same declaration (decided: yes, one meaning, the spelling the design's notation uses). **`x: &mut T` on any parameter, several per function**: decided the result shape is `Mutated` nested in parameter order with the answer innermost (`Mutated<A, Mutated<B, R>>`), so one path is exactly `Mutated<T, R>`, the record is the one the statement joins already thread, and nothing is minted per signature. The parser's body end (`receiver_end`, §19.2's per-arm return, §22's `return`) now runs over the list of paths; `mut self` is the one-entry case and its terms are unchanged (the existing probes and the suite say so). **`&mut place` at a call** where the call is a statement, a `let`'s value or a block's end: expanded by the parser (`imperative::expand_path_call`) into `let #path = \0pathcall(call); place := #path(.value)*.after; …`, so a lent place follows `:=`'s rules (mutable, threaded through loops and statement forms, field paths and elements). The elaborator (`crates/elab/src/path_calls.rs`) holds lent arguments to the callee's recorded modes and the call's type to one `Mutated` per place. **Apartness**: the same place twice or one inside another refused; places parting at an element refused naming the judgment's `Apart` request (not built). `x: &T`: recorded, meaning unchanged. Refusals: parse-time ones in `crates/syntax/tests/parameter_modes.rs` (a parse error refuses a whole file, so they cannot be `expect-error` probes): no place, named `&mut`, immutable or λ-captured place, overlap, element pair, `&mut`/`&` implicit, `mut` beside a mode, default on `&mut`, `&mut` on a theorem, `mut self` with another `&mut`; elaboration-time ones as `expect-error` in `lib/_tests/std/core/parameter_modes_tests.hthr`: lending to an owned parameter, a path given a value, `&mut` inside an expression, a method call whose receiver is a path, and a generator's wrong expectation of modes. The linked lexer needed no change (the probe module checks the same under `HEATHER_LEXER=linked`). Also on the way: the formatter writes a mode tight (`crates/syntax/src/fmt.rs`, test `a_mode_hugs_what_it_marks`), and the loop lifter's `mut self` receiver test (`loops::mut_receiver`) skips a `self` parameter when another parameter is the path. Alternatives met (recorded in docs/language/ownership-design.md §13.1): a mode before the name (`&mut x: T`), and a named record of the values after. Residue: [[parameter-modes-residue]]; a pre-existing lint false positive met on the way: [[unused-payload-lint-statement-if-decreases]].
- 2026-11-24: Verified: plain `scripts/test` (exact image policy, the whole library re-elaborated after the image-format bump and the `tactic` protocol's new request) `== suite: 4136 passed, 0 failed, 3 ignored ==`; `scripts/test --fast` before the formatter fix showed the one corpus-formatting failure that fix answers.
