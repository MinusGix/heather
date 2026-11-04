---
title: Accept a class field that names its carrier as a term at generic uses
status: open
labels: [classes, elaboration]
area: language
created: 2026-11-04
updated: 2026-11-04
---

A class field whose type mentions the class's type parameter as a bare term
(an equation between types, `typed: F = (Nat → Nat)`) declares and
instantiates fine, but any **generic** use of the class is refused with
`unbound name \`F\``, reported at the end of the file once per declaration:

```heather
class C<F>(f: F) { n: Nat, typed: F = (Nat → Nat) }
fn leaf(a: Nat) → Nat { a }
instance C<Nat → Nat>(leaf) { n := 1, typed := refl }        // accepted
fn get<F>(f: F, c: C<F>(f) := infer) → Nat { c.n }           // refused: unbound name `F`
```

The same field through a function, `typed: Itself(F) = Itself(Nat → Nat)`
with `fn Itself(T: Type) → Type { T }`, is accepted everywhere, so the
carrier as a type works and only its spelling as a term at the generic
instantiation is lost (the class's parameters are substituted in type
positions and not in the term an equation's sides are).

The customer: `Compile<F>(f)`'s `typed` field (lib/native/runtime/runtime.hthr,
docs/runtime-fn-setups-design.md §16.8) is spelled through `Itself` for this.

## Done when

The bare form above is accepted at a generic use, `runtime.hthr`'s `Compile`
drops `Itself`, and a probe in `lib/_tests` uses such a class generically.
