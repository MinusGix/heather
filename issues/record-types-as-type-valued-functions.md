---
title: A record type cannot be passed as a Val -> Type function value
status: closed
labels: [frontend,elaboration,types]
created: 2026-08-01
updated: 2026-08-01
---

Found during [[cross-ir-refinement]] (2026-08-01): the clean general form of
the cross-IR refinement family is `RefinesOn(dom: Val -> Type, p1, i1, p2, i2)`,
but it is not writable today, because a record type applied to its value
parameters cannot appear in **expression** position — it is read as the
record's *constructor* even when the expression is being checked against
`Type`.

## The boundary, reproduced exactly (2026-08-01)

```heather
record Boxed(v: Nat) {
    pf: v = v,
}
```

What **works** today:

```heather
// Type position: TyKind::OfExpr, how Converges is used everywhere.
fn mk(v: Nat) -> Boxed(v) { Boxed { pf: refl } }

// An ordinary fn returning Type IS a first-class Nat -> Type value:
fn IsZero(v: Nat) -> Type { v = 0 }
fn AllOf(dom: Nat -> Type) -> Type { (n: Nat) -> dom(n) }
fn UseNamed() -> Type { AllOf(IsZero) }                     // ok
fn UseLambda() -> Type { AllOf(λ (v: Nat) => IsZero(v)) }   // ok
```

What **fails**, both with the same diagnostic:

```heather
fn BoxedT(v: Nat) -> Type { Boxed(v) }                      // error
fn UseIt() -> Type { AllOf(λ (v: Nat) => Boxed(v)) }        // error
```

```
error: cannot infer the value argument(s) of `Boxed` here — a value
parameter appears only inside a field's type, so nothing in `Boxed(…)`
determines it. Put the expression in a checking position: …
```

The diagnostic's advice is wrong for this caller: `fn BoxedT(v: Nat) -> Type
{ Boxed(v) }` **is** a checking position — against `Type` — and `v` is not an
uninferable field-determined parameter, it is right there as the argument.
The constructor arm fires on the name before the expected type is consulted,
and then reports the constructor's inference problem instead of noticing that
no constructor can produce a `Type`.

So the missing piece is exactly one arm: *a record (or inductive) name
applied to arguments, in expression position, checked against a universe,
should elaborate to the lowered type* — the same term `TyKind::OfExpr`
produces in type position, with the value parameters substituted. Everything
around it already exists: types are expressions ([[type-definitions]],
docs/language/types-as-expressions.md), `fn`-returning-`Type` values flow through
higher-order positions (controls above), and the lowering-with-substitution
is `OfExpr`'s existing job.

## Why the ambiguity resolves this way

[[constructors-as-function-values]] (closed) decided a bare/applied
constructor name in expression position means the **constructor**, using the
expected type (a Π over the field types) to η-expand. That decision is right
and stays. The disambiguator here is the same one, pointed the other way:
when the expected type is a **universe** (`Type`, or a Π whose codomain is a
universe reaching a λ-body, as in `UseIt` above), the constructor reading is
*ill-typed on its face* — no constructor inhabits `Type` — so selecting the
type former is not a heuristic, it is the only type-correct reading. A
mismatch (record name at `Type` with wrong-arity value arguments) should
diagnose against the record's value-parameter telescope.

Inference position (`let T = Boxed(3);`) can stay unsupported, exactly as the
constructor round left bare unsaturated constructors: the closed round's
lesson was that the boundary belongs at "needs a checking position," and both
failing examples above are checking positions.

## Scope fence: monomorphized type parameters stay out

`record Monoid<A>` type parameters are **monomorphized** per instantiation
(docs/language/surface-records.md §1.1, the [[surface-polymorphism]] asymmetry):
`Monoid<Nat>` and `Monoid<Bool>` are unrelated kernel types. So `Monoid` as a
`Type -> Type` *value* is not expressible under the current polymorphism
model and is NOT this issue — this issue is value-parameterized (and plain)
records only, where the lowered kernel type genuinely is a function of the
value arguments. A `Type -> Type` story is [[generators-in-the-language]] /
level-polymorphism territory.

## Acceptance sketch

Per docs/testing-generated-terms.md discipline (vary the axes):

1. `fn BoxedT(v: Nat) -> Type { Boxed(v) }` checks; `BoxedT` then flows as a
   `Nat -> Type` value into `AllOf` (named *and* λ-wrapped).
2. The motivating consumer: `RefinesOn(dom: Val -> Type, p1, i1, p2, i2)` in
   lib/certgen/ir_v1.hthr, with `RefinesNat2` restated as
   `RefinesOn(λ (e: Val) => NatEnv(e), …)` for a `NatEnv` record packing
   `a, b, tail` and the `e = VCons(embed_nat(a), VCons(embed_nat(b), tail))`
   shape proof — and `loop_refines_rec`/`rec_refines_loop` re-proved through
   it (the comment above `RefinesNat2` is the marker).
3. An **open** element type in the record's fields (the docs/testing axis
   that hid three of five past defects).
4. Negative controls: the constructor reading still wins when the expected
   type is the record itself (`fn mk(v: Nat) -> Boxed(v) { Boxed { pf: refl } }`
   keeps checking, and positional `Boxed(refl)` at `Boxed(v)` still means the
   constructor); arity mismatch at `Type` diagnoses against the parameter
   telescope, not with today's misdirected inference error.

## Related

- [[constructors-as-function-values]] — the value-level sibling and the
  precedent for both the mechanism (expected type selects the reading) and
  the boundary (checking positions only).
- [[type-definitions]] — made `fn … -> Type` first-class; this is the same
  courtesy for declared records.
- [[cross-ir-refinement]] — the consumer; its `RefinesNat2` comment records
  the exact failure.

## Log

- 2026-08-01: Landed: routing in elab_at_universe (type_former_app -> existing OfExpr lowering, committed so diagnostics re-point), plain/indexed inductives came along, plus two El-of-beta-redex reader repairs (record_of_at, unify_ty decode) the consumer forced — see docs/language/record-type-values.md. RefinesOn is stated generally in lib/certgen/ir_v1.hthr with NatEnv as the domain and both refinement directions re-proved through it; RefinesNat2 survives as sugar. 7 acceptance tests (record_type_values.rs), full suite green, ir_v1 check time unchanged (~41s). Follow-up filed: [[el-reader-decode-audit]].
