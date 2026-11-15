---
title: Constructors are not first-class function values
status: closed
labels: [frontend,elaboration,surface]
created: 2026-07-26
updated: 2026-07-26
---

With [[surface-function-types]] landed, an ordinary global *is* a function
value. A **constructor** is not:

```heather
fn twice(f: Nat -> Nat, n: Nat) -> Nat { f(f(n)) }
fn inc(n: Nat) -> Nat { Succ(n) }

twice(inc, 0)              // ok
twice(λ x => Succ(x), 0)   // ok
twice(Succ, 0)             // error: unbound name `Succ`
```

```heather
inductive Box { Wrap(Nat) }
fn ap(f: Nat -> Box, n: Nat) -> Box { f(n) }

ap(Wrap, 1)                // error: `Wrap` takes 1 argument(s), found 0
```

## Two distinct causes

1. **`Succ` is not a name at all.** `resolve` (`crates/elab/src/lib.rs`)
   special-cases `Zero` to `Term::Zero` and knows nothing about `Succ`;
   `Succ` exists only as the applied form matched at the top of `elab_infer`'s
   application arm. So a bare occurrence is genuinely unbound. `Zero` works
   bare only because it needs no arguments.

2. **A declared constructor is saturated-only.** A bare constructor in
   checking position already has an arm (`elab_check_hinted`, the
   `Var(name) if ctor_here(…)` case), which calls `build_ctor` with an empty
   argument list. Against an expected Π that is an arity error rather than an
   η-expansion.

## Why it is worth fixing, and roughly what it takes

The natural spellings all want it: `cong(Succ, p)`, `map(Wrap, xs)`,
`fold(Cons, nil, …)`. Note in particular that **`.cong(Succ)` — the exact
example [[surface-operators]] deferred — still does not work**; what
[[surface-function-types]] delivered is the *capability* (`cong` taking an
`f: Nat -> Nat`), not that spelling. This issue is the rest of it.

The fix looks well-localized rather than deep, because the position is
already a **checking** one: `apply_explicit` checks each argument against the
parameter's domain, so `twice(Succ, 0)` elaborates `Succ` with
`Nat -> Nat` expected. So:

- give `Succ` a `resolve` entry — `λ(n : Nat). Succ n` at `Π(Nat). Nat`, which
  is two lines and needs no expected type at all;
- in the bare-constructor checking arm, if the expected type is a `Π` and the
  constructor is unsaturated, peel the Π binders, bind them, and build the
  saturated constructor under the lambdas.

The care is in the second: the field types (and, for a parameterized
declaration, the type arguments) come from the expected type today, so the
peeling has to line the Π domains up with the constructor's fields and
diagnose a mismatch rather than mis-lower it — the standing hazard of
`docs/inductives/inductive-tier0-lowering.md`. Tier-1 constructors go through the `Wf`
lowering, so the same arm has to work for a `sup_f` payload.

Partial application of a constructor (`Cons(1)` at `Nat -> List`) is the same
feature and should land with it.

## Related

- [[surface-function-types]] — the round that made this observable.
- [[surface-operators]] — the deferred `.cong(Succ)` spelling.
- [[implicit-binders-in-function-types]] — the other "function values are
  second-class in one respect" gap.

## Log

- 2026-07-26: Found immediately after [[surface-function-types]] landed, by
  asking whether `twice(Succ, 0)` works. It does not; a user-defined `fn` in
  the same position does. Filed rather than folded into that round, which was
  already closed.
- 2026-07-26: Done, in one round and roughly at the estimate. Scheme:
`docs/language/constructor-function-values.md`; acceptance
`crates/elab/tests/constructor_values.rs` (9 tests, 388 total).

The two causes wanted the two separate fixes named above. `Succ` is now a
`resolve` entry beside `Zero` — `λ(n : Nat). Succ n`, no expected type needed,
which is why it also fixes the *inference* positions that a declared
constructor cannot reach (an argument to a callee with implicits, i.e.
`p.cong(Succ)`: [[surface-operators]]' deferral is now fully discharged). The
declared-constructor half is `build_ctor_value` in `inductive.rs`: one λ-binder
peeled off the expected Π per missing field, the missing arguments supplied as
*surface* variables at unspellable `#`-names, and `build_ctor` called unchanged
at the codomain. Partial application (`Cons(1)`) landed with it, as this issue
asked.

Nothing tier-aware was needed: a plain child, a container field, and a
dependent expected type (`(n: Nat) -> [Rose; n] -> Rose`) all work because the
synthetic argument is a surface expression and the codomain is used under the
binder just pushed.

On the hazard this issue flagged — lining the Π domains up with the fields —
the answer is that the η arm must *not* line them up: field annotations keep
coming off the encoding, so a domain that disagrees yields an ill-typed `Pair`
and a kernel rejection (negative control:
`a_domain_that_disagrees_with_its_field_is_rejected`). Adding a conversion
check here would duplicate conversion at one arbitrary site, against
`elab_check`'s standing doctrine.

One case was missing from the scheme and is written up as §5.1: `Cons(1)(xs)`
reaches *inference* (its head is an application, not a name), where an
unsaturated constructor has no type. Fixed by re-associating the spine
(`ctor_spine`), not by building a field telescope. So the real boundary is
narrower than filed: an unsaturated constructor needs a checking position only
if it stays unsaturated.

Still open, deliberately: a bare unsaturated constructor in inference position
(`let f = Wrap;`, `p.cong(Wrap)`). Inferring its type means a second copy of
the lowering's field layout, and it cannot work at all for a parameterized
declaration, whose type arguments are monomorphized rather than inferred. The
`p.cong(Wrap)` half of that is really `apply_implicit` inferring where it could
check — [[elab-unifier-completeness]].
