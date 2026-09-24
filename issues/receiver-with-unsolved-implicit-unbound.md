---
title: A method on a receiver whose type has an unsolved implicit is refused as an unbound name
status: open
labels: [frontend,elaboration,inference,modules,diagnostics]
created: 2026-09-24
updated: 2026-09-24
---

A method call whose receiver's type still carries an unsolved implicit does
not resolve the member: it is refused as an unbound name. This is not
BitVec-specific — a plain record, and `List`'s `Nil`, do the same:

```heather
record R(n: Nat) { x: Nat, p: x = n }
fn R::mk({n: Nat}) → R(n) { R(x := n, p := refl) }
fn R::get({n: Nat}, self r: R(n)) → Nat { r.x }
fn r00(n: Nat, r: R(n)) → Nat { r.get() }       // ok
fn r02(n: Nat) → Nat { R::mk(n := n).get() }     // ok
fn r01() → Nat { R::mk().get() }                 // error: unbound name `get`. `get` is declared below
fn l02() → Nat { Nil.len() }                     // error: unbound name `len`
fn a01(n: Nat) → BitVec(n) { BitVec::zero().iterate_increment(3) }
                                                 // error: unbound name `iterate_increment`
```

Two defects:

1. **Resolution.** The receiver's *carrier* (`R`, `List`, `BitVec`) is known
   even while its arguments are metas, and the carrier is all member lookup
   needs to pick `R::get`. Hypothesis, not yet instrumented: the lookup reads
   the carrier through `carrier_of_ty` → `tag_of`
   (`crates/elab/src/dispatch/carrier.rs`), and the structural recognizer
   declines a type with a meta inside it. Once the member is chosen, the
   ordinary application route unifies the receiver's `R(?n)` against the
   member's `self` domain and the expected type (as in `a01`) can solve the
   rest.
2. **Diagnostic.** "`get` is declared below" is false — `get` is declared
   above the use. Whatever computes that hint is reading the wrong thing on
   this path.

Found by the 2026-09-24 probe of the remaining `@` sites in `lib/`
(all 80 are BitVec): about 16 of them (`(@BitVec::zero(n)).f(…)`,
`(@BitVec::ofNat(n, x)).toNat()`) are this. Some of those stay spelled even
after the fix, because nothing pins the width at all (`zero().band(zero()) =
zero()` inside a statement); for those the right spelling is a named argument,
`BitVec::zero(n := n)`, which already works — not `@`.

Part of the namespace round (#1a) with the rest of the refactor residue on
[[type-owned-namespaces]]. Acceptance: the probe above, and the library's
receiver-position `@BitVec::zero`/`@BitVec::ofNat` sites respelled.
