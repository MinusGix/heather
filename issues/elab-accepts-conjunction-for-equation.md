---
title: A conjunction passed for an equation argument is refused only by the kernel
status: open
labels: [frontend,elaboration,diagnostics]
area: language
created: 2026-10-04
updated: 2026-10-26
---

Found while proving the stat pass (`lib/elf64_stat_width.hthr`, 2026-10-04).
A proof of a conjunction passed where an equation is expected gets past the
elaborator, and only the kernel refuses it, at the whole declaration, with no
span and no types:

```heather
theorem bad4(a, b: Nat, p: (a = b) ∧ (b = b)): b = a { sym(p) }
// error: the kernel rejected `bad4`: NotConvertible
//   --> …:1:1
theorem bad2(a, b, c: Nat, p: (a = b) ∧ (b = b), q: b = c): a = c { trans(p, q) }
// the same; `trans<Nat>(p, q)` and a `let r: (a = c) = trans(p, q)` too
```

`sym` and `trans` are ordinary prelude theorems (`crates/elab/src/prelude.hthr`)
whose equation's sides are implicit, so the check of `p` against `?a = ?b`
should fail to unify `Eq` with `∧`. Something in that path accepts it instead
(the sibling [[check-fallback-discards-expected-type]] was the inference
fallback; that one is closed, so this is a different route).

How it cost time: one projection too few (`regs.right…right` stopping at the
last conjunction instead of its right side) inside a 40-line proof. The
kernel's refusal named the theorem only; finding the line took a bisection
with `axiom hole<A>(): A;` stand-ins, and it hid behind an unused `let`
(dropped before the kernel sees it), so a stand-in for the *use* passed while
the bad `let` was still in the source.

Not a soundness problem (the kernel refuses), a diagnostics one: the
elaborator should point at `p` and say it is a conjunction, not an equation.

The counting that produced the bad projection is [[conjunction-facts-read-by-counting]].

## Log

- 2026-10-04: A second shape of the same gap, in `lib/elf64_row_fields.hthr`'s `row_selected`: inside a `match first as λ f => … → RowAt(…, f, …) → …` whose arm bound the refined record as `head1`, a record built from `page := head.page` and `holds := head1.holds` elaborated, and the kernel refused it (`PageNext` "where a type that displays the same is expected"). Here the kernel's message did carry a span. The elaborator treated `head1.page` and `head.page` as the same; they are different variables.
- 2026-10-25: Another mismatch only the kernel refuses, under a let-bound or β-redex head: [[elab-accepts-mismatch-under-redex-head]].
- 2026-10-26: The filed `bad4`/`bad2` are now reported by the elaborator at `p` (`this has type `And<a = b, b = b>`, but `a = b` is expected here`), since `OwedChecks` (#168): `sym`/`trans`'s equation sides are implicit, so `p` was an inferred argument. The redex-head case is closed. The second shape in the log (a refined record's `head1.page` taken for `head.page`) is not rechecked.
