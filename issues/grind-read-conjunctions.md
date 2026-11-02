---
title: grind: read the equations inside a conjunction or a record of them
status: open
labels: [tactics]
area: tactics
milestone: [tac-general]
created: 2026-11-02
updated: 2026-11-02
---

grind reads a local only when its type is an equation (or an equation under
binders). A conjunction of equations (`k: a = b ∧ b = c`), or a record of
them (`Env::Same`'s fields, `settle_kept`'s `.left`/`.right`), is listed as
"not an equation, not read". Found by [[grind-library-sweep]] in
`Env::compose_same` (`lib/native/native_structured_meaning.hthr`), whose
`trans(ka.left, trans(k0.left, sym(kb.left)))` chains read the projections
of such locals.

Wanted: a local (or hint) whose type is a one-constructor inductive is read
field by field, recursively, as facts named `k.left`, `k.right` (the proof is
the projection), with the same depth bound as the reader; `↔` and
existentials stay unread. Pairs with [[grind-constructor-facts]], which
reads constructor equations the other way.

Done when `theorem conj(a, b, c: Nat, k: a = b ∧ b = c): a = c { by grind() }`
closes and `compose_same`'s `args_same` and field chains close by grind.
