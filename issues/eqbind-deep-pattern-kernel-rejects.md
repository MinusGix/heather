---
title: match h: with a deep pattern: the elaborator accepts h as the clause equation, the kernel refuses
status: closed
labels: [elaboration,match,patterns,defect]
area: language
created: 2026-10-31
updated: 2026-11-01
---

Found by [[dependent-match-compiler]]'s survey (2026-10-31, docs/language/matching/dependent-match-compiler-design.md §2.1 P4), master `35b223d`:

```heather
fn mk(n: Nat) → List<Nat> { [n, n] }
theorem deep_eq_comp(n: Nat): Nat {
    match h: mk(n) {
        Cons(x, Cons(y, t)) => { let k: (mk(n) = Cons(x, Cons(y, t))) = h; y },
        _ => 0
    }
}
```

The elaborator accepts the annotation, and the kernel rejects with `NotConvertible`: in the term, `h` is the one-level equation `mk(n) = Cons(x, #col)`, because the generated inner match does not refine it. This is the same class as the closed `elab-match-refines-hypothesis-kernel-rejects`. It is owned by [[match-clause-equations]], which makes `h` the clause equation.

## Log

- 2026-11-01: Fixed by match-clause-equations (design §7.1): the inner match's motive rebuilds the children tuple around the column, so h is the clause equation; P4 and a swapped-binder negative control are in lib/_tests/std/data/list_tests.hthr.
