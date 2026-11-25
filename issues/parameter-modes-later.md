---
title: Parameter modes: what the residue round left (elements apart, f(&a), generators publishing modes)
status: open
labels: [ownership,language,frontend]
area: language
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

What [[parameter-modes-residue]] left of the parameter-mode surface (docs/language/sequencing-surface-design.md §24.6). Each is a surface form or a protocol change; none is a checker.

- **Two elements of one owner lent at once** (`g(&mut u[i], &mut u[j])`), refused saying the indices' apartness is a proof the judgment will ask. Waits for the judgment's `Apart` request ([[ownership-discipline-over-code]]); the surface then passes the request instead of refusing. A design discussion is settling how a proof of apartness reaches the compiler: build no route here before it ends.
- **A frozen view at a call, `f(&a)`.** Notation only (a view means the value), but a spelling that says `&` should be held to a `&` parameter on every route an argument meets its parameter in the application elaborator (inference and checking, implicit insertion, named arguments, `crates/elab/src/application.rs`). The `&mut` side gets this from one statement-level marker (`\0pathcall`); a `&` argument has no statement to hang on. Worth building once a view's region is named (docs/language/ownership-design.md §10.5), when the argument carries something.
- **A generator publishing a declaration with modes.** More than a field on `tactic::Param`: the host's `decl_param_*` reads (`crates/elab/src/host.rs`, `decls`), every generator that builds a `Param` (`lib/std/tactic/derive.hthr`, `lib/std/machine/laid.hthr`, and the `runtime` generator's `lib/native/runtime/runtime.hthr`, `rt_lower.hthr`), and a published live path's result must be the `Mutated` nest the parser writes for a written one, which the publisher has to check or build. Reading modes (`tactic::modes`) is built.
- **The method's own call that lends places as a `mut self` body's end** (§19.3's tail call, `\0mutated_whole`): a body ending `c.f(&mut b, …)` binds the call and takes it apart, which a `decreases` function's companions follow but a `runtime fn`'s loop rule does not.
- **A statement `f(&mut a);` in a block of another carrier** drops the answer, as a `mut self` call's statement does, where `e;` would bind it; `let _ <- f(&mut a);` binds it. Whether the statement should bind is the carrier design's question (docs/language/sequencing-surface-design.md §3.1, §8.2).
- **An `if` whose condition lends a place** (`if f(&mut a) = 1 { … }`): the condition is a proposition, read in a type, where nothing is lifted; bind the call first.

## What it assumes from elsewhere

- **[[ownership-discipline-over-code]]** owns the judgment and the `Apart` request. Assumed here: only that it reads the modes from the declaration (`tactic::modes`).
