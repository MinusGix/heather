---
title: A match code at a recursive motive is refused when a written arm builds a constructor value
status: open
labels: [metaprogramming,elaboration,inductives,defect]
created: 2026-10-03
updated: 2026-10-03
---

Found 2026-10-03 by [[recursive-spine-codes]]'s round, and present on master
before it (1334d9a, checked with the release CLI). A `match code` whose motive
is a **recursive** declaration is refused by the kernel as soon as a written
arm returns a value of it from a branch with no recursive result:

```
inductive T { T0, T1(x: Nat, r: T), T2(y: Nat, r: T) }
meta fn probe(g: Ctx, body: Code(g |- Nat)) -> T {
    match code body as T { tm_zero => T0, _ => T0 }
}
```

- `tm_zero => T0` or `tm_zero => T1(0, T0)`: `LevelMismatch`.
- `tm_var => T0`: `HeadMismatch`.
- Accepted: only the default arm (`_ => T0`), an arm that returns its
  recursive result (`tm_succ(t) => t`), and every arm shape at a **flat**
  motive (`Flat { FA, FB(n: Nat), … }`), which is what
  `lib/certgen_code.hthr`'s `TA`/`SA` motives are.

The difference between the accepted and refused arms is where the constructor
value is *built*: the default arm is elaborated in the outer scope and
weakened into each branch telescope by `shift_univ`/`shift_global`/
`shift_local` (`quote.rs`), while a written arm is elaborated in `acx`
(`shift_cx` over the branch's universe and global binders, with the
telescope's globals pushed onto `meta_pushed`). A recursive constructor value
carries `D#shape`/`D#arity` references and a `Wf` whose level comes from the
lowering; a flat one carries no `Wf`. The first suspect is therefore the
level or the generated-reference numbering of a tier-1 constructor value built
under a branch telescope's universe binder. Not diagnosed further.

## What it assumes from elsewhere

- **[[recursive-spine-codes]]** found it. Assumed here: nothing; the
  reproduction above is independent of that round's change.
