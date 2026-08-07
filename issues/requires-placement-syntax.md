---
title: Where do requires binders live? Sketch the call-signature syntax options
status: open
labels: [frontend,syntax,design,ergonomics]
created: 2026-08-07
updated: 2026-08-07
---

From the adoption round's reading (2026-08-07): `fn sum<A> requires m: Monoid<A> (xs: List<A>) -> A` reads oddly — the requires clause sits BETWEEN the type parameters and the value parameters, and with several dictionaries the head of the declaration becomes a wall before the first real argument. The position is semantically motivated (solver parameters are moved to the front because later parameter TYPES may mention them — rare but legal, e.g. `p: m.op(x, y) = z`) but the surface need not mirror the elaboration order.

Options to sketch against real library signatures before deciding:

- **(a) Status quo**: prefix clause. Honest about dependency order; heaviest to read.
- **(b) Trailing where-clause**: `fn sum<A>(xs: List<A>) -> A requires m: Monoid<A> { … }` (or `where`). Rust-familiar, keeps the argument list first; desugars to the front, so a later value parameter's type referencing `m` reads textually forward — acceptable if rare, worth a lint if confusing. Name could be optional (`requires Monoid<A>`) when the dictionary is only consumed by resolution/dispatch, never projected by name — auto-named binder.
- **(c) In-list bracketed binders**: `fn sum<A>([m: Monoid<A>], xs: List<A>)` Lean-style — interleaves freely, no reordering question, but adds a third bracket kind to parameter lists.
- **(d) Both (a) and (b)**, prefix for the dependent case, trailing for the common one — two spellings of one thing has cost (traits record §12's own warning about the instance forms).

Also from the same reading, separate but adjacent: **instance shorthand** — `instance Default<Nat> { default := 0 }` is already short, but a one-field instance may want `instance Default<Nat> := 0`-grade concision or a positional literal; sketch alongside since both are call-signature/declaration ergonomics over the same feature. Decide in one small design pass; no implementation until then.
