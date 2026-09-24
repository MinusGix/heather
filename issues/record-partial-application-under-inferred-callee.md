---
title: A partially applied record type is refused where the callee's type argument is still being inferred
status: open
labels: [frontend,elaboration,inference,records,diagnostics]
created: 2026-09-24
updated: 2026-09-24
---

A partially applied record type is refused as an argument whose parameter
type still mentions an unsolved type argument of the callee. With the type
argument written, or pinned by an earlier argument, the same spelling checks.

```heather
record Grammar(level: Nat, value: Nat) { at_level: level = level, }
fn takes1<A>(rel: A -> Type, a: A) -> Type { rel(a) }
fn later_arg_first<A>(a: A, rel: A -> Type) -> Type { rel(a) }
fn GrammarSpec(level: Nat, value: Nat) -> Type { Grammar(level, value) }

fn explicit_prefix() -> Type { takes1<Nat>(Grammar(0), 1) }      // ok
fn inferred_after() -> Type { later_arg_first(1, Grammar(0)) }   // ok
fn inferred_wrapper() -> Type { takes1(GrammarSpec(0), 1) }      // ok
fn inferred_prefix() -> Type { takes1(Grammar(0), 1) }           // refused
fn takes<A>(rel: Nat -> A -> Type, a: A) -> Type { rel(0, a) }
fn inferred_bare() -> Type { takes(Grammar, 1) }                 // refused likewise
```

The refusal:

> cannot infer the value argument(s) of `Grammar` here — a value parameter
> appears only inside a field's type, so nothing in `Grammar(…)` determines it.
> Put the expression in a checking position: … or an argument of a declaration
> that expects one

It *is* an argument of a declaration that expects one, so the advice is wrong
as well. Hypothesis from the wording (not instrumented): `Grammar(0)` has two
readings, the type former and the record's constructor, and the type-former
reading is chosen only against a solved expected Π into `Type`. The parameter
type `?A -> Type` is deferred (it mentions `?A`), so the argument falls to
inference, where the name reads as the constructor. The codomain `Type` is
known even while the domain is a meta, and that is enough to choose the type
former.

Found by [[showcase-spec-relations-as-records]] (2026-09-24):
`docs/showcase/calc_parser.hthr` keeps its `GrammarSpec` wrapper, with a
comment, at the eight `forget_at`/`forget_post`/`post_on_success`/
`complete_sound` calls. Acceptance: those calls take `Grammar(n)`, the wrapper
goes, and the probe above checks. Follows [[record-type-partial-application]],
whose tests all write the type arguments.
