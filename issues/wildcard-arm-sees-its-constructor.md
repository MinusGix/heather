---
title: A wildcard arm sees the scrutinee as the constructor it stands for
status: closed
thread: Make compiler correctness proofs elegant
labels: [elaborator,matching,proofs]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-16
updated: 2026-11-16
---

A `_` arm in a proof stands for each constructor it covers, and the goal is specialised per constructor, but the arm cannot name the value it matched: the scrutinee variable keeps its unrefined type there. At `lib/native` (probed 2026-11-16, `/mnt/project-files/compile-proofs/real.hthr`):

```
theorem wild_runs(s: Stmt, p: (x: Stmt) → Type, all: …, other: (x: Stmt) → p(x)): p(s) {
    match s { Then(a, b) => all(Then(a, b), trivial), _ => other(s) }
}
// refused: this has type `p(s)`, but `p(Compute(_))` is expected here
```

`_ => false_elim(is)` works, because the arm does not mention the value. Where it does, every constructor is written out with its fields only to be put back together:

```
Sequence(prefix, continuation) => λ p out known names c emitted => Sequence(prefix, continuation).region_extends(layout, p, out, names, c, emitted),
Compose(prefix, continuation) => λ … => Compose(prefix, continuation).region_extends(…),
Conditional(inputs, condition, arguments, outputs, when_true, when_false) => λ … => Conditional(inputs, condition, arguments, outputs, when_true, when_false).region_extends(…),
Lend(views, callee, arguments, result) => …, Call(callee, arguments, result) => …,
Loop(inputs, bound, parameters, count, body, exit, next, outputs, exhausted) => λ … => Loop(inputs, bound, parameters, count, body, exit, next, outputs, exhausted).region_extends(…),
```

`native_compile_correct.hthr` has this block four times (`Stmt::emits_extends`, `Stmt::emits_runs` twice, and the `first` split of `Then`, eleven more arms calling `t.then_nil`), and a new `StructuredRegion` constructor edits each.

## Wanted

In a `_` arm (and a binding arm `other => …`), a scrutinee that is a local variable is the matched constructor applied to that case's fields, as it is in a written arm after substitution: `_ => other(s)` checks at `p(Compute(_))` because `s` is `Compute(_)` there. A binding pattern `other => …` or `r @ _` is the spelling when the scrutinee is not a variable.

## Done when

`wild_runs` checks as written (a probe in `lib/_tests/lang/`, with a negative control that the arm cannot use a field it did not bind), and the four blocks in `native_compile_correct.hthr` are `Dataflow(body) => …, _ => λ … => region.region_extends(…)`.

## Resolution (2026-11-16)

Where the motive depends on the scrutinee, a `_` arm that names it expands to one arm per constructor no earlier arm names, each opening with `let s: TypeOf(s) = C(fields);` (`Patterns::rebind_default`, design `docs/language/matching/nested-match-patterns-design.md` §4.1). The scrutinee may be a local or an enclosing arm's field, which the structural lowerings bind as an alias. `wild_runs` and its controls are in `lib/_tests/lang/wildcard_arm_tests.hthr`. The four blocks in `native_compile_correct.hthr` are now `Dataflow(body) => …, _ => …` and `_ => t.then_nil(first, …)`.

Left out:

- The binding arm `other => …` / `r @ _` for a computed scrutinee. It is new syntax, so it waits for a design decision.
- A constructor that only deep arms name keeps the plain `_` (the §4.1 list says why).
