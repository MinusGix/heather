---
title: have's right-hand side sees a let-shadowed name as the outer binding; the kernel rejects with a bare HeadMismatch
status: open
labels: [frontend,elaboration,diagnostics]
area: language
created: 2026-09-30
updated: 2026-09-30
---

A `have` whose right-hand side names a variable that an earlier `let` has
shadowed is checked by the elaborator against the outer binding, but the
term it emits refers to the `let`. The kernel then rejects the declaration
with a bare `HeadMismatch` at its head, naming neither the `have` nor the
variable.

```
import nat;
import logic;
record Box { v: Nat }
theorem same_box(c: Box): c.v = c.v { refl }
theorem t_shadow4(c: Box, n: Nat): c.v = c.v {
    let c = n;
    have done = same_box(c);
    done
}
```

`heather check` reports `the kernel rejected t_shadow4: HeadMismatch`.
With `let done = same_box(c);` instead, the elaborator refuses correctly
("this has type `Nat`, but `Box` is expected here").

Found 2026-09-30 in the R2 round of native-stack-refactor: a parameter
`c: FieldsCodes` and a later `let c = three.third(total)` in
`fields_tail_runs`; renamed to `codes` there.
Expected: `have` elaborates its right-hand side in the scope that includes
earlier `let`s, as `let` does, and so refuses at the argument.
