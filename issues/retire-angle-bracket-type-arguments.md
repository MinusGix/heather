---
title: "Retire `<…>` type arguments: the kernel has no type/term distinction to hang them on"
status: open
labels: [frontend,syntax,design,elaboration]
created: 2026-08-16
updated: 2026-08-16
---

`List<Nat>`, `And<P, Q>`, `fn map<A, B>(…)`, `nil<Nat>()`. Four spellings of
one idea — *give the leading implicit parameters positionally* — in a language
whose kernel has no notion of a type argument at all.

The claim: **`<…>` is surface convention borrowed from languages that have a
type/term distinction, Heather does not have one, and the borrowing is what
every `<`-ambiguity round has been paying for.** Retiring it deletes grammar
rather than adding it.

## Why the ambiguity is structural rather than unlucky

`<` is both a bracket and a comparison operator. That is survivable in Rust,
where types are a separate syntactic category and no type can contain `<` the
operator; the disambiguation lives entirely on the expression side (turbofish).
It is **not** survivable here, because propositions are types: `n < m` is
`Lt(n, m)`, a type, written exactly where a hypothesis goes
([[nat-order-kit]]). So `<` the operator and `<` the bracket occur in the same
positions, and no amount of local cleverness separates them:

- The expression site has speculated since [[surface-polymorphism]].
- The type site got two ad-hoc discriminators (a following `(`; a following
  connective) before the `Lt` round made it speculate too.
- That made the pair exponential ([[type-argument-speculation-cost]]), fixed by
  a memo.
- Two positions are *still* wrong: [[comparison-inside-type-arguments]] and
  [[quantifier-notation-in-type-arguments]], both of which are the same
  sentence — "the type-argument grammar admits less than the type grammar".

Five mechanisms and two known-wrong positions, all to spell something the
kernel does not have.

## What the kernel actually has

A type parameter is **a leading implicit value parameter at `Ty 0`**
(`docs/surface-polymorphism.md` §2): `fn f<A, B>(x: P)` lowers to
`Π(A : Ty 0). Π(B : Ty 0). Π(x : ⟦P⟧). …`. There is no second binder form, no
kind, and nothing in `Term` that distinguishes a type argument from any other.
`<…>` is sugar over `Π`, exactly as `(…)` is.

## Both replacements already exist in the language

This is the finding that makes the issue worth filing rather than musing, and
both halves were run (2026-08-16):

1. **Implicit binders at `Type` work today.** `fn f({A: Type}, x: A) -> A { x }`
   **checks**. `docs/surface-polymorphism.md` §3.3's "there is still no way to
   say `Type` in a function type" is stale. So `fn map<A, B>(…)` has a spelling
   that needs no new mechanism: `fn map({A, B: Type}, …)`.
2. **Positional explicit instantiation is `@`.** `@sym(b, a, p)` suppresses
   implicit insertion and gives every parameter positionally
   (`crates/elab/tests/nat_suite.rs`), which is what `nil<Nat>()` is for.

So `<…>` is a **third** mechanism duplicating two that exist, and it is the
only one of the three that is ambiguous.

## The one thing that does not work yet

`fn g(xs: Or(Nat, Nat)) -> Nat` is refused — "`Or` cannot be used here". A
declared inductive cannot be applied with ordinary call syntax in type
position. That is the whole implementation surface of this issue, and it is a
**restriction to remove**, not a mechanism to add: in the kernel `Or(Nat, Nat)`
and `Or<Nat, Nat>` elaborate to the same application.

## What it would cost

Mechanical churn across `lib/` and the test corpus — every `List<A>`,
`Option<A>`, `And<P, Q>`, every `<A: Monoid>` constraint head and generic
`instance<A>`. Large, boring, and reviewable by the suite. Against that: the
whole `<`-disambiguation apparatus is **deleted** — `try_tyargs`, the `ty()`
speculation, the two discriminators, the failure memo — and `>`/`>=` become
addable without a second thought ([[nat-order-kit]] is holding them back partly
for this reason).

The open question is **readability**, and it is a real one rather than a
formality: `List<Nat>` vs `List(Nat)`, and especially the constraint heads,
where `<A: Monoid(op)>` is dense and `{A: Type}` + a `requires` clause may read
worse. Lean, Coq and Agda all write type application as juxtaposition and
nobody finds `List Nat` unclear — but none of them has Heather's `(…)` call
syntax, so the comparison is suggestive rather than decisive. **A design round
should write the same file both ways and read them**, per
[[list-algorithms-exercise]]'s method, rather than deciding from a table.

## What it assumes from elsewhere

- **[[surface-polymorphism]]** owns `<…>` as it stands. Assumed here: only its
  §2 lowering — a type parameter is a leading implicit value parameter at
  `Ty 0` — which is what makes the retirement a surface question.
- **[[nat-order-kit]]** owns the propositional order. Assumed here: only that
  `n < m` is a type, which is what makes the ambiguity structural.
- **[[implicit-binders-in-function-types]]** owns the `{…}` binder. Assumed
  here: only that it binds at `Type`, which was verified rather than assumed.

## Log

- 2026-08-16: Filed out of the `Lt` round's aftermath, after its own fix was
  found to be exponential ([[type-argument-speculation-cost]]) and the question
  became "is speculation the right shape at all". Not scheduled: this is a
  design round with a large mechanical tail, and [[std-api-waves]] wave 2 is
  the standing next thing. Filed now because the two grammar gaps the same
  round produced are both *instances* of it, and they should not be fixed
  separately if this is the answer.
