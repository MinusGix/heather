---
title: An induction hypothesis typed by a motive application cannot fill implicit arguments
status: closed
labels: [frontend,elaborator,inference,proofs]
created: 2026-08-17
updated: 2026-08-17
---

Filed by the `Int` round ([[std-int-encoding]]), ranked #2 there. It is what makes
a hand-written induction principle expensive to *use*, as opposed to expensive to
state.

`Int` is a non-recursive inductive, so nothing recurses on an integer and every
law that needs induction goes through `lib/std/int.hthr`'s `int_ind`, whose motive
is a value parameter `P: Int -> Type`. In an arm written as

```heather
λ (k: Nat) (ih: add(a, OfNat(k)) = add(OfNat(k), a)) => trans(cong_int(isucc, ih), …)
```

the `cong_int` call is **refused**: "could not infer the implicit argument `b` of
`cong_int`". `cong_int(f: Int -> Int, {a, b: Int}, p: a = b)` fills its two
implicits by unifying against a type, and the type it has to read is `ih`'s, which
is the motive *applied* — `(λ (z: Int) => add(a, z) = add(z, a))(OfNat(k))`. That
is a β-redex, not an `Id`, so nothing can be read off it. The λ's own annotation
does not help: the binder is checked *against* the parameter type, and the entry
that lands in the context is the expected one.

The same happens with `sym(ih)`, so it is about implicit-filling from an argument
type in general, not about `cong_int`.

## What works, at what cost

All three of these check, and the round used the first:

1. `@cong_int(isucc, add(a, OfNat(k)), add(OfNat(k), a), ih)` — the implicits
   spelled positionally. Costs one restatement of `ih`'s type per rewrite; **10
   sites** in `lib/std/int.hthr` (`add_comm`, `add_assoc`, `neg_add`,
   `mul_add_distr` and the three cancellation/`mul_isucc` chains).
2. A named helper theorem per arm, taking `ih` as an ordinary parameter — the
   conversion check at the call site accepts the redex, and inside the helper the
   hypothesis has a real `Id` type.
3. Reordering the `trans` chain so the deferred argument is on the other side —
   works only when some *other* argument determines the middle point, which is why
   `std/nat`'s existing `trans(cong_nat(…), lemma)` sites were never affected.

## The fix

whnf the argument's type before reading implicits off it (or, equivalently, β-normalize
a motive application when it is used as a hypothesis type). This is the same
sentence as the fix that landed 2026-08-17 for
[[match-arg-of-polymorphic-callee-needs-motive]]'s sibling — "an argument's type
is evidence even after the parameters run out" — extended to *reducible* argument
types.

A narrower alternative that would also have paid for this round: have a λ binder's
written annotation replace the expected type in the context when the two are
convertible. That is a smaller change and it makes annotations mean what a reader
thinks they mean, but it fixes only the arms a writer thought to annotate.

## What it assumes from elsewhere

- **[[std-int-encoding]]** owns the round and the `int_ind` spelling. Assumed
  here: only that `Int`'s induction principle has to be a declaration with a
  value-parameter motive, because `Int` has no structural recursion of its own.
- **[[ih-generalization]]** owns the curried-recursion tax. Assumed here: nothing;
  this is the *hypothesis's type*, not the recursion's shape.

## Log

- 2026-08-17: Filed by the `Int` round. 10 sites, each paying one restatement of the hypothesis's own statement inside `@cong_int`. Ranked #2 of that round's six.
- 2026-08-17: **Landed** (managed round; docs/argument-type-reduction-design.md).

Route: **whnf at the read site**, not at the binder. `Elaborator::unify_arg_ty` (`crates/elab/src/lib.rs`) wraps both places `apply_implicit` reads an argument's inferred type — the declared-parameter loop and the spilled-argument loop [[curried-tail-type-arg-inference]] added — and reads the type's weak head normal form *only when the syntactic read learned nothing*. So `cong_int(isucc, ih)` and `sym(ih)` both check at a motive-applied hypothesis, and so does anything else that fills implicits from an argument, which is the reason for the general site: the consumer never knows how its implicits were found. It is also the same sentence `solve_from_expected` already applies to the *expected* type twenty lines below — the two sides of the elaborator's evidence now agree.

Three properties keep it from being a widening: learn-only twice (`unify_ty` records into `Unsolved` and never fails, so the retry can add a solution and cannot retract one; a wrong one is still a kernel rejection); **no progress** is the trigger rather than "something is still unsolved", so a call that already elaborated never reaches the reduction; and the reduction is opportunistic — `whnf` is fuel-bounded and out-of-fuel is swallowed, because the honest report is the caller's own per-slot "could not infer", not a complaint about a type nobody asked to reduce. Termination of the not-an-`Id` case is the fuel's.

**The narrower alternative (§The fix, second paragraph) is declined, and its stated benefit turned out not to exist.** It fixes a spelling rather than a class — the same redex arrives unannotated from a `let`, from a function returning `P(x)`, and from a `match` arm at a synthesized motive, none of which has an annotation to promote. And its second argument, that the context entry would then print as written, is empty: goal-hole entries are *already* displayed reduced (`display_type`'s reader stage), so a `?step` in the issue's own arm lists the equation either way. Not worth having as ergonomics; the verdict is decline, not defer.

**The library, and a correction to this issue's own count.** `lib/std/int.hthr` now contains **no `@` call at all** — all 22 `@cong_int(f, lhs, rhs, p)` spellings are terse. But only **eight** of them were this defect (`add_comm`, `add_assoc`, `neg_add`, `mul_add_distr`, two arms each). The other fourteen — the cancellation and `mul_isucc`/`mul_ipred` chains this issue counted toward its ten — rewrite by an ordinary lemma call at a real `Id`, so nothing was ever hidden there; verified by re-checking the module with the reduction disabled, where all fourteen check terse on the OLD elaborator. They were spelled out for consistency with the arms that had to be, which is how a tax spreads past its own sites and why the filed count was high. [[congruence-by-anti-unification]]'s "23 of 58" is corrected on that issue.

Tests: `crates/elab/tests/argument_type_reduction.rs`, 8 — the headline arm, the same hypothesis under `sym` (nested in inference position), an already-normal hypothesis on the unchanged path, an OPEN element type (`list_ind` at `List<A>` with `A` a theorem parameter), the composition with [[goal-motive-by-scrutinee-abstraction]]'s synthesis (a motive-less `match` whose expected type is itself an applied motive, each arm filling implicits from the step hypothesis), and three negative controls: an underdetermined `?f` still refused with its own message, a redex whose normal form is `Nat` and not an `Id` refused rather than misfilled or looping, and a hypothesis reduced at the wrong endpoints still refused.

Suite 1846 -> 1854. `scripts/bench --check`: ok, 106 comparisons, zero flags (a sixth clean full run, logged on [[kernel-bench-full-run-flags-drift]]).

Residue with an owner: [[goal-context-entry-printed-in-the-wrong-context]], filed by this round's display probe — an entry's type is rendered against the whole of Γ instead of the prefix it is scoped in, so `p: add(a, 0) = a` prints as `add(p, 0) = p`. Pre-existing and general; it has nothing to do with redexes, and it is the reason the display half of the road not taken was checked rather than assumed.
