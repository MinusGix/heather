---
title: A generic congruence whose type argument is inferred is rejected with LevelMismatch
status: open
labels: [frontend, elaboration, kernel, stdlib]
created: 2026-09-18
updated: 2026-09-18
---

A polymorphic congruence applied with its type argument **inferred** produces a
term the kernel refuses:

    error: the kernel rejected `list_eq_dec`: LevelMismatch

Spelling the type argument fixes it, and nothing else about the site changes.
`lib/std/list.hthr`'s `list_eq_dec` therefore writes `cong_tail<A>(p)` where
`cong_tail(p)` is what a reader would write.

## Reproducing

With `lib/std/list.hthr` at HEAD, in a module importing `logic`, `nat`, `list`:

```heather
theorem my_cong_tail<A>({xs, ys: List<A>}, p: xs = ys): xs.tail() = ys.tail() {
    j(p, λ y q => xs.tail() = y.tail(), refl)
}
// …used inside a decider that matches two `Cons` cells and refutes through it:
//     Inr(λ (p: (Cons(h1, t1) = Cons(h2, t2))) => tail_ne(my_cong_tail(p)))
// LevelMismatch.  `my_cong_tail<Nat>(p)` at the same site: accepted.
```

Three controls narrow it:

- the *same* theorem declared monomorphically at `List<Nat>` is accepted;
- `cong_head`, which is equally polymorphic but takes an explicit `A`-typed
  argument (`fallback`), is accepted — so it is the **inference** of `A`, not
  polymorphism;
- the congruence's own declaration always checks; only the use site fails.

So `A` is solved by unification from an implicit equation binder, and whatever
level that route assigns does not survive the kernel.

## Acceptance

The site above checks without the type argument, and the reproduction is a
test beside the other inference tests in `crates/elab/tests/implicit_args.rs`.
`lib/std/list.hthr`'s `cong_tail<A>(p)` drops back to `cong_tail(p)`.

## Log

- 2026-09-18: Filed from the `Char`/`String` rework. It cost one wrong
  diagnosis first: the failure was read as a level problem in `cong_fn`, and
  rewriting both congruences with `j` changed nothing.
