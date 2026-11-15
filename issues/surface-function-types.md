---
title: Function types and lambdas at the surface
status: closed
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

**Type syntax:** `(x: A) -> B` dependent, `A -> B` non-dependent.
Right-associative. Consistent with `fn f(…) -> T`, which already reads this
way. ~~`{x: A} -> B` implicit~~ — **struck 2026-07-26 by the scheme**, see
"Corrections" below.

**Lambda syntax:** `λ (x: A) => e`, with

- `λ` the canonical spelling, `fun` accepted as an ASCII synonym, `λ`
  pretty-printed. One lexer alternation; nobody is blocked on input method.
- binder groups as in `fn`: `λ (x: A) (y: B) => e`, parens optional when the
  type is omitted (`λ x => e`). ~~`{}` for implicits~~ — struck, see below.
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

## Corrections the scheme made (2026-07-26)

Writing `docs/language/surface-function-types.md` against the actual elaborator
contradicted two things above. Recorded here because that is what the
scheme-before-code discipline is for.

1. **No implicit binders in function types or lambdas this round.**
   Implicitness is not in `Type::Pi` — the kernel has one function type and no
   notion of an implicit argument. It lives in the elaborator as
   `ParamMeta.implicit` on a *declaration*, looked up **by name**
   (`crates/elab/src/lib.rs:1303–1315`) and consumed by `apply_implicit`'s
   `mask`. A function *type* has nowhere to put the flag and a λ-bound value
   has no `ParamMeta`. It also buys nothing yet: the surface has no universe,
   so `{A: Type}` is not writable and implicit *value* binders are the only
   expressible case. Explicit binders only; `{` diagnosed. Revisit with the
   universe/polymorphism layer. (Consequence: implicit insertion stays
   name-directed, so applying a function *value* is always explicit.)
   **Tracked as its own issue: [[implicit-binders-in-function-types]]** —
   wanted on by-value functions too, not merely for symmetry with `fn`, so
   this is a deferral and not a rejection.

2. **The `Call`-head refactor is small.** 13 sites — 9 in the parser, 4 in the
   elaborator (`lib.rs:759, 774, 806, 1643`), three of which are name-keyed
   special forms that want a `Var` head anyway. The bulk of the diff is the
   `ty()` restructure (its `Ident '<'` early return currently bypasses any
   arrow check) and the new elaboration arms.

A third finding, not a correction but worth having in the issue: **η at `Π` is
definitional and unconditional** (`crates/kernel/src/conv.rs:535` compares at
a `Π` by applying both sides to a fresh variable, at every layer). So
`λ (x: Nat) => f(x) ≡ f`, including for neutral `f`, and `refl` proves it.
Pinned as an acceptance item. `docs/kernel/wf-former-design.md`'s opening calls `Π`
"the one type family this kernel deliberately does not η-expand", which read
literally is wrong and wants a clarifying edit — what route A lacked is that a
*neutral* children-function cannot be reconstructed from a projection, which
is not the same as lacking η.

## Scope

In:

- `TyKind::Fn` (dependent, explicit binders only — see Corrections) + parsing/printing.
- `ExprKind::Lam` + parsing/printing.
- **`Call`'s head becomes an `Expr`** (n-ary, not curried, so implicit
  insertion and `@` keep working). *Measured at 13 sites, not "broad" — see
  Corrections.*
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
- Implicit binders ([[implicit-binders-in-function-types]]).

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
- 2026-07-26: Scheme written: docs/language/surface-function-types.md (grammar, the ty() restructure with every existing call site checked for arrow ambiguity, elaboration arms, five interactions to observe rather than assume, eight rejections with messages, and a 15-item acceptance checklist). Two corrections to this issue's plan came out of writing it against the real elaborator, both recorded above: implicit binders are out of scope (implicitness lives in ParamMeta keyed by declaration name, not in Type::Pi, and the surface has no universe to make them worth having), and the Call-head refactor is 13 sites rather than 'broad'. Also pinned: eta at Pi is definitional and unconditional, so lambda x => f(x) is convertible with f. Ready to implement.
- 2026-07-26: IMPLEMENTED and green: 26 acceptance tests in crates/elab/tests/function_types.rs, workspace at 379 passing. Landed: TyKind::Fn (dependent, right-associative, one binder per paren group), ExprKind::Lam with the lambda/fun spellings and juxtaposed binders, postfix application so a call's head is any expression, Call -> App n-ary with an Expr head plus the Expr::as_named helper, elab_ty's Fn arm sharing elab_decl_inner's max(dom,cod) level rule, lambda checking (expected domain wins; a written annotation must be convertible) and inference (every binder annotated), apply_explicit generalized to an optional callee name, and reject_function_fields keeping a Pi out of an inductive field. Three things implementing it corrected, all in docs/language/surface-function-types.md §10: (1) the first parenthesis rule in ty() was too narrow and the EXISTING suite caught it — add_assoc's statement '(a + b) + c = a + (b + c)' opens with a group that is an expression, not a type, so the discriminator is now a top-level '->' rather than 'not followed by ='; (2) a latent lexer panic, since the two-byte token window '&src[i..i+2]' sliced into a codepoint the moment a non-ASCII token existed — '(λ' does exactly that, and λ is the first non-ASCII token the language has; (3) two claims in the scheme had no referent — there is no surface printer at all, and '@' on a non-name head is caught by the grammar, one layer earlier than §8 placed it. §6.3's predicted rejection was WITHDRAWN: a hole under a lambda binder works, because an on RHS is elaborated in the goal world so the binder is legitimately in scope; kept as a test WITH a negative control, since 'the name resolves to the wrong variable but the term still typechecks' is [[tyvar-scoping-in-lowered-fields]]'s hazard class. Nothing else in §6 misbehaved: guards, aliases and partial application all survive the extra binder a lambda pushes. Found in passing and filed rather than fixed: [[annotated-let-swallows-the-equals]], pre-existing and confirmed against 13dd25d.
- 2026-07-26: Correction to the landing note: constructors did NOT become first-class function values, and the '.cong(Succ)' spelling that [[surface-operators]] deferred still does not work. An ordinary global does — 'twice(inc, 0)' checks — but 'twice(Succ, 0)' is 'unbound name Succ' ('Succ' is not a name at all; resolve knows only 'Zero', and 'Succ' exists solely as the applied form) and 'ap(Wrap, 1)' for a declared constructor is an arity error, because the bare-constructor checking arm calls build_ctor with no arguments rather than eta-expanding against the expected Pi. What this round delivered is the CAPABILITY — cong taking an 'f: Nat -> Nat' — not that spelling. Split out as [[constructors-as-function-values]]; docs/language/surface-function-types.md §10.2 records it. Found by asking whether twice(Succ, 0) works rather than assuming it did.
