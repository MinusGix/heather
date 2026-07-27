---
title: "Motives are lambdas: retire the bespoke binder syntaxes"
status: open
labels: [frontend,syntax,elaboration]
created: 2026-07-26
updated: 2026-07-27
---

Filed by [[surface-function-types]] as its own follow-on ("two special-form
syntaxes collapsing into one general one. Worth its own small round after
this lands").

`match … as x -> M` and `j(p, (y, q) -> M, case)` (`ExprKind::Match`,
`ExprKind::J`, `crates/syntax/src/ast.rs:245–260`) each carry a hand-rolled
binder syntax that exists only because the surface had no λ when they were
written. Two costs, one aesthetic and one real:

- **`->` is overloaded.** It is now the type arrow (`(x: A) -> B`) *and* the
  binder-to-body marker in these two forms. Reading `as z -> M` as a function
  type is the natural reading and the wrong one.
- **They are special features rather than language features.** A motive is a
  function from the scrutinee to a type. Now that the surface has λ, it can
  simply *be* one, and the elaborator stops carrying a second binder path.

```
match xs as (λ z => P(z)) { … }          // or: match xs : (λ z => P(z)) { … }
j(p, λ y q => P(y, q), case)
```

## Why it is small

Pure surface + elaborator, no kernel change: the kernel's `ElimNat`/`J`/`Case`
motives are already `Type`s under a binder, and the elaborator already builds
them from the current syntax. This is a parse-and-desugar change plus the
motive-synthesis path in [[elab-stage2-metas]] staying green (motive-less
`match` in checking position must keep working — most uses write no motive at
all).

## The follow-on it sets up

Once motives are ordinary functions and [[surface-polymorphism]] +
[[implicit-binders-in-function-types]] have landed, `j` has no reason to be
syntax at all: it can be an ordinary generic declaration with implicit
endpoints and an implicit motive, resolved like any other name. Same for
`refl`, and plausibly for `absurd`/`inj` (today name-directed elaborator
forms from the no-confusion generator). Whether the motive can be *inferred*
rather than written at a use site is the pattern-unification question tracked
in [[elab-unifier-completeness]] — the higher-order case, so the round should
say what it rejects.

## Watch for

- `Ty` vs `Expr` position: a motive written as a λ is an *expression* whose
  body is a type. The surface has no `Ty`-valued expression form today, and
  inventing one is the actual design decision in this round — the alternative
  is a λ-shaped syntax in type position that is not an `ExprKind::Lam`.
- The `Succ(k, ih)` low-level arm form and the `as z -> M` motive are the two
  survivors of the pre-[[match-recursion]] surface; check whether both should
  go at once.

## Log

- 2026-07-27: Gated on [[surface-universe]], and that is where this issue's 'Watch for' fork gets decided rather than here. The flagged design decision -- 'the surface has no Ty-valued expression form today, and inventing one is the actual design decision in this round' -- dissolves once TyKind can say Type<n>: a motive becomes an ordinary function at '(z: A) -> Type', a lambda into it is a plain ExprKind::Lam, and the Expr/Ty bridge is the EXISTING path (checking an expression against an expected Ty l, lib.rs:950, today only a diagnostic arm) rather than a new invention. So this lands as phase 3 of that session rather than as its own round. Also recorded there: the follow-on this issue sets up (j/refl/cong/absurd/inj as ordinary declarations) can only go through at CONCRETE level 0, because a fully general motive is polymorphic in its level, which is UPi, which is layer m. Every current use is at level 0, so that is not a blocker -- but the round should state it rather than discover it.
