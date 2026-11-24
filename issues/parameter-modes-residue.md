---
title: Parameter modes: the forms ownership-parameter-modes left (method calls with paths, &mut off statements, elements apart)
status: open
labels: [ownership,language,frontend]
area: language
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-24
---

What `ownership-parameter-modes` did not build (docs/language/sequencing-surface-design.md §24.4). Each is a surface form; none is a checker.

- **A `mut self` method with other `&mut` parameters**, and a method call that lends places when the callee's receiver is itself a path (`a.g(&mut b)` for `fn g(a: &mut A, b: &mut B)`). Both are refused today with the plain call named. A method call threads one receiver (`elaborate_mut_call`, `crates/elab/src/statements.rs`); building it means a call that rebinds its receiver from the outer `Mutated` and its lent places from the inner ones, with the result's order fixed (receiver first is the natural reading).
- **`&mut` where the call is not a statement, a `let`'s value or a block's end**: `let x <- f(&mut a);`, `return f(&mut a);`, an arm of a tail branch that is the bare call (`True => f(&mut a),`), an operand (`f(&mut a) + 1`). Refused by the elaborator with where it may stand. Each needs the expansion (`imperative::expand_path_call`) at that position, which the `\0mutcall` candidates have for some of them already.
- **Two elements of one owner lent at once** (`g(&mut u[i], &mut u[j])`), refused saying the indices' apartness is a proof the judgment will ask. Waits for the judgment's `Apart` request ([[ownership-discipline-over-code]]); the surface then passes the request instead of refusing.
- **A frozen view at a call** (`f(&a)`) has no spelling: a view means the value, so the call passes the value. Wanted only once a view's region is named (`&{self} V`, docs/language/ownership-design.md §10.5).
- **A generator publishing modes**: `tactic::Param` (the `Publish` side) has no mode, so a generated declaration's parameters are all owned. Reading them (`tactic::modes`) is built.
- **A callee's own recursion** is checked against its modes by the call's type only (one `Mutated` per lent place), since the declaration's table is not registered while its body elaborates (`crates/elab/src/path_calls.rs`).

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the judgment and the `Apart` request. Assumed here: only that it reads the modes from the declaration (`tactic::modes`).
