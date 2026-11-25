---
title: Parameter modes: the forms ownership-parameter-modes left (method calls with paths, &mut off statements, elements apart)
status: open
labels: [ownership,language,frontend]
area: language
milestone: [nh-ownership]
created: 2026-11-24
updated: 2026-11-25
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

## Log

- 2026-11-25: Built (docs/language/sequencing-surface-design.md §24.4–§24.6; probes in `lib/_tests/std/core/parameter_modes_tests.hthr`, parse-level facts in `crates/syntax/tests/parameter_modes.rs`). In the order taken, each easing the next:

  1. **Whether a dot call rebinds its receiver is the receiver's written mode** (`Members::threads_receiver`/`receiver_mode_of`, `crates/elab/src/dispatch/member.rs`; `statements::threaded_record`), not a `Mutated` result head: the fix [[mutated-result-dot-call-diagnostic]] asked for and what a method lending places needs, since its result is `Mutated` whether or not the receiver comes back. Its own recursion reads `SelfRef::receiver_mode`; a callee with no table falls back to the result head. The loop lifter's generated methods (`crates/elab/src/loops.rs`) now record their receiver as `Path`, which they are.
  2. **A method call lends places, and `mut self` takes other `&mut` parameters.** A call with `&mut` arguments on a mutable place is a `\0mutcall` candidate of it (`imperative::expand_path_call`, `receiver` flag): the elaborator binds the receiver from the outer `Mutated` and `#path` to the rest when the receiver comes back, `#path` to the whole call otherwise, so the places' rebinding reads `#path` either way and loops/statement forms thread the receiver by the rules they already had. `PathCalls::path_call` takes a `candidate` flag (a `&mut` receiver is accepted there, and counts one `Mutated` more). The receiver is a place of the call for apartness. Decided: a `mut self` receiver is written first among the `&mut` parameters (refused otherwise at the declaration), so parameter order stays the one rule and puts the receiver outermost. The `decreases` self-call rewrite (`measure::MethodCalls`) keeps a claimed self-call that lends places lending them (receiver marked lent when it comes back) and reads "comes back" from the mode.
  3. **`&mut` off statements**: `Parser::hoist_path_calls` lifts every call that lends places out of a statement's expression where it is surely evaluated (argument, operand, receiver, literal field, index, scrutinee), inner first and left to right. So `let x <- f(&mut a)` (the answer bound), `return f(&mut a)`, `x := f(&mut a)`, a tail arm `True => f(&mut a),`, an operand, and nested lending calls elaborate. Decided: a place lent inside an expression and read elsewhere in it is refused at parse time (order of evaluation would decide the read); the call's own arguments may read it; two calls lending one place run left to right. Not lifted under a λ, in a value-position arm or block, on the right of `&&`/`||`, or in a type: refused by the elaborator, whose message now names where a lending call may stand. A top-level lending call expands exactly as before, so existing terms are unchanged.
  4. **A callee's own recursion is held to its modes**: `SelfRef::modes` for `PathCalls::check_modes`, and `measure::Rewrite::self_call` checks lent arguments against the parameters before a `decreases` self-call becomes the hypothesis (its measure reads a lent place's value going in, where a `\0mutarg` had reached the elaborator).

  Not built, re-filed in [[parameter-modes-later]] with reasons: elements apart (waits on the judgment's `Apart`; no route built), `f(&a)` (as notation it should be held to a `&` parameter on every route an argument meets its parameter; nothing carried until regions are named), generators publishing modes (a tactic-protocol change touching every `Param` builder, the `runtime` generator's included, plus the published result's nest), a lending own call as a `mut self` body's tail call, a lending statement in another carrier, a lending call in an `if` condition.
