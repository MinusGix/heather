---
title: Unused-payload lint fires on a payload read only by a statement if in a decreases function
status: open
labels: [lint,frontend]
area: language
milestone: [none]
created: 2026-11-24
updated: 2026-11-25
---

Met by `ownership-parameter-modes` (2026-11-24). In a `decreases` function, a constructor payload read only by the condition of a statement `if` is reported "constructor payload `x` is not used in this arm; write `_` instead", though the arm reads it:

```heather
fn count_true(n: Nat, xs: List<Bool>) → Nat decreases xs.len() {
    match xs {
        Nil => n,
        Cons(x, rest) => {
            let mut m = n;
            if x { m := m + 1; }
            count_true(m, rest)
        },
    }
}
```

The declaration elaborates and computes; only the warning is wrong, and following it (`Cons(_, rest)`) breaks the function. Likely the lint reads a lowered or companion copy of the arm in which the statement form's join no longer mentions `x` by its written name. `lib/_tests/std/core/parameter_modes_tests.hthr` (`split_count`) binds the payload to a local first to stay quiet; drop that once fixed.

## Log

- 2026-11-25: Another case of a payload reported unused though the arm reads it, from [[reflected-languages-typed-by-construction]]: a payload read only as an explicit type argument. `match a { TElem(t, i) => Path::elem<t>(i), TFst(x, y) => pfst<x, y>(), … }` (a family indexed by types, `t`, `x`, `y` of type `Type`) warns "constructor payload `t` is not used in this arm" for each. Here following the advice happens to work, because inference recovers the type arguments from the expected type (`TElem(_, i) => Path::elem(i)`, as `lib/_tests/lang/ownership/typed_steps_tests.hthr` now writes it), but the lint is not reading type arguments as uses.
