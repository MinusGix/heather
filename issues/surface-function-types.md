---
title: Function types and lambdas at the surface
status: open
labels: [frontend,syntax,elaboration,design]
created: 2026-07-26
updated: 2026-07-26
---

The surface has no function type and no lambda. `TyKind` is
`Nat | a = b | Named<args>` (`crates/syntax/src/ast.rs:146`) and `ExprKind`'s
only application form is `Call { name: String, … }` — the head is a *name*,
not an expression (`ast.rs:181`, "the head is a name (stage 1)").

The kernel has had the machinery since v0: `Type::Pi`, `Term::Lam`,
`Term::App`, plus `UPi`/`ULam` and `CtxPi`/`CtxLam` for the modal layers. So
this is a **pure surface + elaborator round: no trusted-base change, no
metatheory obligation, no ch. 07 pass.** It cannot break soundness, which is
a different risk class from the last two rounds ([[wf-former]],
[[unit-level-and-vec-preservation]]) and a good one to spend on after them.

## Why this is ahead of the things that name it as a blocker

Function types appear in three issues as someone else's parenthetical and in
none as their own item, which is why the roadmap's focus order pointed past
them. They are load-bearing for:

- [[nested-inductives-container-fields]] — the natural eliminator for a
  container field is a fold, and a fold wants a function argument. Without
  one, the fold has to be a *syntactic form* next to `match`, which is a
  second special-form eliminator to be deleted later. The alternative
  no-lambda route (match the container by its length, push the tail
  recursion into an auxiliary) needs mutual declarations and cross-function
  termination checking — a bigger round, less reusable.
- [[surface-operators]] — `.cong(Succ)` was deferred there for exactly this.
- [[surface-proof-automation]] — `apply`.
- [[compile-typeclass-design]] / [[certifying-generator]] — a `Compile`
  instance is a record of functions; user-written optimization passes are
  functions; multi-level pass hooks are a higher-order interface. None of
  that picture exists without this.
- The mathematics half generally: an algebraic structure is operations.
- [[stress-proof-suite]] item 3 — `Acc` is not even *stateable* at the
  surface today, because `Acc.intro`'s field is a function. It stays
  kernel-only until this lands.

## Decisions taken (2026-07-26)

**Dependent from the start.** `(x: A) -> B(x)`, not simple-arrow-then-
generalize. `cong` only needs the non-dependent arrow, but the mathematics
side needs dependency throughout and a non-dependent surface would be rebuilt.

**Type syntax:** `(x: A) -> B` dependent, `A -> B` non-dependent,
`{x: A} -> B` implicit (matching the existing `{}` implicit-parameter
spelling on `fn`/`theorem`). Right-associative. Consistent with `fn f(…) -> T`,
which already reads this way.

**Lambda syntax:** `λ (x: A) => e`, with

- `λ` the canonical spelling, `fun` accepted as an ASCII synonym, `λ`
  pretty-printed. One lexer alternation; nobody is blocked on input method.
- binder groups as in `fn`: `λ (x: A) (y: B) => e`, parens optional when the
  type is omitted (`λ x => e`), `{}` for implicits.
- **`=>`, not `,`.** The comma is Lean 3's spelling and the one thing Lean 4
  moved away from (it kept `λ`, with `fun` as synonym). The reason applies
  here *one round early*: container literals `[a, b, c]` arrive with
  [[nested-inductives-container-fields]], and `[λ (x: Nat), f(x), g]` is then
  genuinely ambiguous between a one- and a two-element vector — the same
  ambiguity Lean 3 hit with `⟨λ x, e, y⟩`. Σ-pairs will want a surface
  spelling too.
- **`=>`, not `->`.** `->` is the type arrow, so `λ (x: A) -> e` reads as an
  ascription. Keeping `->` for types and `=>` for binder-to-body also makes
  `=>` mean one consistent thing — `Nil => 0` and `λ x => e` are both
  "binders left, body right".

**Not** Rust's `|x| e`, despite the Rust-flavoured core ([[surface-syntax]]):
`|` is wanted for divisibility, absolute value, and cardinality on the
mathematics half.

## Scope

In:

- `TyKind::Fn` (dependent, implicit-capable) + parsing/printing.
- `ExprKind::Lam` + parsing/printing.
- **`Call`'s head becomes an `Expr`.** Mechanical but broad — it touches
  every call site in the elaborator, and it is the bulk of the diff.
- Elaboration of application and abstraction against the kernel's
  `Pi`/`Lam`/`App`, in both checking and inference mode.

Out, and each to be *diagnosed* rather than mis-elaborated (the discipline
[[goal-holes]] used):

- Anything outside the pattern fragment of higher-order unification. This
  round solves patterns and rejects the rest with a message naming the
  restriction and pointing at [[elab-unifier-completeness]], which already
  tracks general pattern inversion.
- Function values in `inductive` field types (that is the infinitary tier,
  [[inductive-compiler]] tier 2; a finitary declaration must stay finitary).
- The trait/instance layer ([[compile-typeclass-design]]) — records of
  functions are a separate round on top of this one.

## Follow-on this enables (do not do inline)

`j(p, (y, q) -> M, case)` and `match … as x -> M` use `->` for binder-to-body
today. Once `->` is the type arrow those read wrong, and once lambdas exist
the motives can simply *be* lambdas — two special-form syntaxes collapsing
into one general one. Worth its own small round after this lands.

## Log

- 2026-07-26: Opened. Filed after the post-[[stress-proof-suite]]-item-2
  direction review, which found (a) `Acc`/W is not on the critical path —
  `simulate` is fuel-indexed per [[ir-simulate-design]], so nothing before
  [[end-to-end-compile-instance]] reaches `W` — and (b) the actual bottleneck
  is that the surface type grammar is three constructors wide. Syntax
  decisions above taken in the same discussion. Next step: the scheme doc
  before the code, per the tier-0/tier-1 discipline.
