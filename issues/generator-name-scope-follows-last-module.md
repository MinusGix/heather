---
title: Generators resolve source names in whatever module was checked last
status: closed
labels: [compiler,x86,elaboration]
created: 2026-09-25
updated: 2026-09-28
---

The native producer's generators (`read_loop::generate_loop`,
`generate_format`) resolve source functions with `Elaborator::global_abs`,
which answers from the name scope of whichever module the session checked
last. Run `generate_format` after checking a module that does not import
`decimal_line`, and `decimal_line::line_word` fails with "unknown source
function", qualified spelling and all. The round fixed this by ordering:
generators run immediately after the context check, and the context imports
`decimal_line` whenever `--bound` is set (`crates/cli/src/native.rs`,
2026-09-25).

Order-dependence of that kind is a trap for the next generator, and for a
Heather-side generator even more ([[scoped-declaration-generators]]).

## Scope

Give generators a lookup that resolves a qualified name against the checked
global environment, not the last module's scope. Or name the scope
explicitly: resolve as if in module `M`. The latter matches what a
certificate's text will be checked in. A base name should still resolve per a
named scope, never per history.

## Acceptance

- `generate_format` works when called after an unrelated module's check, in a
  test.
- `native.rs`'s ordering comment goes, or states a reason that is not the
  lookup.

## What it assumes from elsewhere

- **[[host-elaboration-interface]]** owns the Heather-facing version of the
  same interface. Assumed there: only that it resolves names against an
  explicit scope.

## Log

- 2026-09-28: Added `Elaborator::with_module_scope(module, callback)` for reflection and generation against a checked module's saved name-resolution environment. It shares the existing temporary scope stack, supports nesting, and restores the caller's scope on success, error and panic. Bare names retain named-scope ambiguity and listed-import choices; qualified names still require visibility, and an unknown checked module is refused before calling the callback.

  The native loop generator now receives its checked context's name explicitly. The formatter selects `decimal_line`'s declaration scope and can run after the loop pieces are checked. Removed the context's print-only `decimal_line` import and the ordering workaround. Regression coverage compares all three formatter certificates and their bytes before and after checking an unrelated module with a colliding `line_word`; it also checks that generation leaves the unrelated module's visibility unchanged. Named-scope tests cover qualification, ambiguity, import lists, missing scopes, nesting, errors and panic restoration. The scoped interface is documented in `docs/modules-design.md` §10.2.
- 2026-09-28: Verified with the focused named-scope and formatter regressions, then the full `scripts/test`: 3069 passed, 0 failed, 5 ignored. The native read/print integration tests pass with formatter generation after the loop pieces are checked and without the context's `decimal_line` import workaround. `scripts/issue check` passes with its existing unrelated warning.
