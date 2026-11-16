---
title: Functional induction and branch equations through a match on a call's result
status: open
thread: Make compiler correctness proofs elegant
labels: [tactics,proofs,induction,native]
area: tactics
milestone: [tac-general]
created: 2026-11-16
updated: 2026-11-16
---

`induct f(x̄)` and the branch equations read a body that is a tree of tests on `Bool`s and on parameters (`docs/tactics/functional-induction-design.md` §1). A compiler is not that shape. It is a pipeline of partial steps:

```
fn St::emits(self s: St, p: List<Nat>, names: Nat) → Option<Out> {
    match s {
        Seq(first, rest) => match first.emits(p, names) {
            None => None,
            Some(c) => rest.emits(c.code, c.names),
        },
        …
```

`Stmt::emits` (`lib/native/native_compile.hthr`), `Source::compile`, `compile_calls`, `Procedure::code` and the node emitters all are. On the mini-model in `/mnt/project-files/compile-proofs/` (2026-11-16) `induct St::emits(s, p, names)` gives:

- one case `Seq`, not `Seq::None` and `Seq::Some`: the match on the call's result is not a test it reads;
- an IH for `first.emits(p, names)` (the scrutinee, called outright) and none for `rest.emits(c.code, c.names)`, which sits under the `Some(c)` arm whose `c` the case does not bind;
- the hypothesis `e: s.emits(p, names) = Some(c)` restated over the raw stuck match.

So the `Seq`, `If` and `Loop` cases cannot be finished from the principle, and every theorem about `emits` is written as a structural `match s` with the pipeline inverted by hand in each arm: `(match one: first.emits(…) { None => λ none => absurd(none), Some(c1) => λ two => … })(emitted)`. `native_compile_correct.hthr` does this 64 times (`absurd(none)`), its neighbours 154, and proves the same inversion again as standalone lemmas for the certificate reader (`Stmt::emits_then_of`, `emits_repeat_of`, `emits_branch_of`, `Source::compile_calls_ran`, `compile_of`, about 350 lines).

## Wanted

1. **A match on a call's result is a test.** `branch_equations` reads `match g(ā) { C(ȳ) => … }` (and `match h: g(ā)`) where `g(ā)` is any term of an inductive type, not only a parameter: one leaf per arm, the arm's fields bound by the case, the hypothesis `g(ā) = C(ȳ)` in scope under the name the source gave it or a default. Cases are named by the path as now (`Seq::Some`, `If::True::Some::None`).
2. **An IH at a recursive call under such an arm.** The case binds the arm's fields, so a call that mentions them (`rest.emits(c.code, c.names)`) gets its IH, quantified as the other IHs are.
3. **The equations too.** `f::Seq::Some(first, rest, p, names, c, h: first.emits(p, names) = Some(c)): Seq(first, rest).emits(p, names) = rest.emits(c.code, c.names)` is `Stmt::emits_then_of`, which is written by hand today and which `write-elf` cites once per sequence.
4. `Option::and_then`, `Bool::guard` and `e?` pipelines read the same way: a body written `first.emits(p, names).and_then(λ c => rest.emits(c.code, c.names))` should give the same cases, or the docs say to write the match.

With [[constructor-equations-in-context]] the `None` cases close themselves, and `Stmt::emits_extends` on the model is one `induct` with an arm per construct that has something to say.

## Built (2026-11-16)

Items 1 to 4 (`docs/tactics/functional-induction-design.md` §1.1): a
`match` on any term of an inductive type that is not a parameter is a test,
its type the elaborator's; the case binds the arm's fields and
`h: g(ā) = C(ȳ)` (a `match h:`'s name where it gives one), with an IH at
the matched call and at each recursive call under the arm; the equations
come with it (`Stmt::emits::Then::Some` on `lib/native` states
`Stmt::emits_then_of`); `and_then`/`map` on `Option` and `Result`, a postfix
`?`, and `Bool::guard` read as the `match` they are. Probes in
`lib/_tests/std/tactic/induct_tests.hthr` (`Prog::run`, a `match h:`, a
nested one, a measured recursion) and
`lib/_tests/std/core/branch_equations_tests.hthr`. On the mini-model,
`St::emits_extends` is one `induct` whose `None` cases are `absurd(e)`.

Left: the conversions below, which the proof-forms thread
([[native-compile-correct-proof-forms]]) does with
[[constructor-equations-in-context]].

## Done when

`Stmt::emits_extends` and `Stmt::emits_runs` are `induct s.emits(p, layout, out, known, names)` with no hand inversion of a `None`/`Some` match, and `Stmt::emits_then_of`, `emits_repeat_of` and `emits_branch_of` are the generated equations (deleted from `native_compile_correct.hthr`). Probes in `lib/_tests/std/tactic/induct_tests.hthr` cover a result match with a recursive call under its arm, a `match h:` on a result, and a nested one.

Related: [[definition-branch-equations]] (the equations this extends), [[induct-case-goal-report]] (what a case shows today), [[native-compile-correct-proof-forms]] (the cleanup that needs it).
