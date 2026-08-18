---
title: A markless function type stores no binder names, so a value callee cannot be called by name
status: open
labels: [frontend,elaboration,ergonomics]
created: 2026-08-18
updated: 2026-08-18
---

Found by the [[named-arguments]] round (docs/named-arguments-design.md §7 and
§12.1), which needed parameter *names* off a value head and discovered the
boundary is not where it looks.

`skel_of_ty` (`crates/elab/src/lib.rs`) returns `Some(Skel)` only when the
written type carries an **implicit mark** somewhere — that is
`docs/implicit-binders-design.md` §3.1's deliberate sparseness rule, "existing
declarations store nothing new". A `SkelBinder` carries `name: Option<String>`,
so the names are *available* in the syntax; they are simply not stored when
nothing else about the type needed storing.

The user-visible consequence, now that names are callable:

```heather
fn apply(f: {A: Type<0>} -> (x: A) -> A, n: Nat) -> Nat { f(x := n) }   // works
fn apply(f: (x: Nat) -> Nat, n: Nat) -> Nat { f(x := n) }              // refused
```

Both are pinned by `a_value_callee_needs_binder_names` in
`crates/elab/tests/named_arguments.rs`, so the line cannot move by accident —
but it is a strange line to have to explain, and the refusal message ("this
callee's type binds no parameter names") is *true* and still misleading, since
the writer visibly wrote one.

## The fix, and what it costs

Store a skeleton whenever a binder **has a name**, not only when a mark is
present — i.e. widen `skel_of_ty`'s `any` condition. The cost is exactly what
the sparseness rule was avoiding: a `Skel` allocated for every annotated
function-typed parameter in the codebase, and a `Cx::skels` entry per binder
that previously stored `None`. Whether that matters is a measurement, not an
argument, and `scripts/bench --check` is the gate.

## What it assumes from elsewhere

- **[[implicit-binders-in-function-types]]** owns the structural gap (a
  `Type::Pi` has no names and no implicitness). Assumed here: only that the
  *surface* `Ty` does have them, which is what `SkelBinder.name` already
  records.
- **[[named-arguments]]** owns the calling convention. Assumed here: only that
  it reads names off `skel_params`, which it does.
