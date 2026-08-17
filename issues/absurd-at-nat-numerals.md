---
title: absurd cannot refute an equation between Nat numerals
status: open
labels: [frontend,elaboration,proofs]
created: 2026-08-17
updated: 2026-08-17
---

Found by wave L3 ([[std-list-mem-and-perm]]) writing the negative control for
`Mem`: refuting membership needs a DISEQUALITY of elements, and at `Nat` there
is no one-step way to say one.

```heather
theorem c_not_mem(): ¬ Mem(7, Cons(1, Cons(2, Nil))) {
    λ (m: Mem(7, Cons(1, Cons(2, Nil)))) => match m {
        Inl(e) => absurd(e),                       // error: `absurd` needs an
        …                                          // equation at a declared
    }                                              // inductive type
}
```

`absurd` reads a constructor equation at a **declared** inductive
([[absurd-on-branch-scrutinee]] extended it as far as neutral payloads), and
`Nat` is the kernel's own type, not a declared one. So the refutation is written
by peeling successors down to `Succ(k) = 0` by hand:

```heather
Inl(e) => succ_ne_zero(5, succ_inj(6, 0, e)),                    //  7 ≠ 1
Inr(Inl(e)) => succ_ne_zero(4, succ_inj(5, 0, succ_inj(6, 1, e))),  //  7 ≠ 2
```

One `succ_inj` per unit of distance between the two numerals, so the cost is
**O(min(n, m))** terms for `n ≠ m` and it is written per site. `std/nat` names
the same boundary at `succ_ne_zero` ("the small tax `Nat`-as-a-kernel-type
charges, and it is worth naming because nothing else in the library pays it") —
this is the first customer that pays it more than once, and the first where the
distance is a numeral rather than one `Succ`.

Two candidate answers, and they are not exclusive:

1. **Library.** `std/nat` states `ne_of_lt`, or `succ_ne_succ`, or simply
   `theorem nat_ne(n, m: Nat, h: Not(Le(m, n)) …)` — but the cheap one is
   `eq_dec`: at closed numerals `eq_dec(7, 2)` *computes* to `Inr(…)`, so
   `or_resolve`-shaped consumption of the decider is a one-liner that needs no
   language change at all. Whether that reads as the right API is the open
   question, and it belongs to [[nat-arithmetic-kit]]'s successor if the answer
   is yes.
2. **Language.** `absurd` learns the kernel's `Nat`, which is the same
   no-confusion fact for `Zero`/`Succ` that it already has for declared
   constructors. Small, and it removes the tax at every future site rather than
   at the ones a lemma is written for.

The wave did neither: the control was written at `Bool`, where the list is still
`List<Bool>` and `absurd` works, and the `Nat` cost is recorded here rather than
absorbed into a helper nobody asked for.

## What it assumes from elsewhere

- **[[absurd-on-branch-scrutinee]]** owns what `absurd` can read. Assumed here:
  only that its subject is declared inductives and that `Nat` is outside them.
