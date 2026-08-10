---
title: absurd cannot read a constructor equation whose endpoint is the match's own scrutinee
status: closed
labels: [frontend,elaboration,proofs]
created: 2026-08-05
updated: 2026-08-10
---

Found writing [[list-algorithms-exercise]] (2026-08-05), on the third `Bool`
lemma of the file. The discrimination pattern — case-split a variable that a
*hypothesis equation* mentions, and refute the impossible branch — does not
work:

```
theorem t(a: Bool): a = True -> a = True {
    match a { False => λ p => absurd(p), True => λ p => p }
}
// error: `absurd` needs both sides of the equation to be constructor applications
```

**Why.** `case_tree` (crates/elab/src/inductive.rs) instantiates each arm's
motive at the *injected binder*, `M[inl(Var 0)/z]`, not at the constructor
literal — which is right for reduction (a `Case` on `Inl(v)` reduces whatever
`v` is, so `append(inl z, Nil)` computes fine) and wrong for **reading**:
`read_ctor` recovers the constructor index from the `Inl`/`Inr` spine but then
wants a `Pair` to walk the nominal tag and the payload off, and a bare binder
is not one. So `absurd`/`inj` decline. Confirmed for a nullary constructor
(`Bool::False`) and for one with a payload (`Option::Some`), so it is the
shape of the arm scrutinee and not the arity.

**What it costs today.** Every `inversion`-shaped step has to be re-stated so
that the equation's endpoint is a *computation* rather than the scrutinee
itself: `andb(a, b) = True -> a = True` works (the endpoint reduces to a
literal in each arm) while `a = True -> …` does not. In the exercise file the
workaround was to prove `andb_true` by rewriting under `andb` instead of by
cases — fine there, but it is a real restriction on how a decided predicate's
kit can be stated, and the error message points at the wrong thing (it says
the equation is not between constructors when it is).

**Two candidate fixes**, neither costed:

1. `read_ctor` learns the neutral case: given the inductive and a term of the
   arm's summand type, recover the fields by *projection* (`fst`/`snd` of the
   binder) rather than by pattern-matching a literal. Field-for-field this is
   what η for `Σ` gives, so it should be sound; the question is whether every
   consumer of `read_ctor`'s field list wants terms it can compare.
2. `case_tree` η-expands the arm binder into the literal it must be —
   `(tag, x₁, …, tt)` — before instantiating the motive. Bigger terms at every
   arm, which [[simulate-conversion-cost]] bills per conversion step, so this
   is the expensive one.

## What it assumes from elsewhere

- **[[list-algorithms-exercise]]** owns the exercise that found it. Assumed
  here at filing: only that its workaround stated the hypothesis over a
  computation. The closing round retired that workaround from the live file.

## Log

- 2026-08-05: Filed 2026-08-05 off [[list-algorithms-exercise]]; the body has the reproducer, the cause (case_tree instantiates an arm's motive at the injected binder, so read_ctor can determine the constructor index but not walk the fields off it), and two candidate fixes. Ranked third in that file's still-hurts list.
- 2026-08-10: LANDED: `read_ctor` now accepts a constructor index witnessed by an arm motive’s injection path, projects neutral payload fields when `inj` needs them, and lets `absurd` ignore neutral recursive children it never consumes. Arbitrary outer neutrals remain rejected. Bool, Option payload/injectivity, recursive List, and the real `andb_true` proof pin the boundary; suite 1405 -> 1407, full `scripts/test` green.
