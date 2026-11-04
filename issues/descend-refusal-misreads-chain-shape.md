---
title: The "must descend" refusal calls a chain-shaped type branching when no window was built
status: closed
labels: [diagnostics,frontend]
area: language
code: crates/elab/src/recursion.rs:776 @ ff5be99
created: 2026-11-02
updated: 2026-11-02
---

`GuardKind::Wf { cov: None, .. }` explains a non-descending self-call by
saying a window of earlier values exists only for chain-shaped declarations
"and this one is not". `cov` is also `None` for a chain-shaped type whose
match simply built no window, so the claim is false there:

```
inductive Chain { end, link(next: Chain) }
fn Chain::depth(self c: Chain) → Nat { match c { end => 0, link(next) => depth(c) } }
// error: recursive call to `depth` must descend: … A window of earlier values
// exists for **chain-shaped** declarations … and this one is not: a branching
// constructor has no chain to walk …
```

Found while pinning [[self-reference-hides-same-named-global]]. The branch
should ask the type's shape, not the guard's window, before saying which.

## Log

- 2026-11-02: Done. `GuardKind::Wf` carries a `shape: WfShape` (`Chain`,
  `Branching`, `NoWindowRoute`), set where the guard is built (`wf.rs` from
  `chain_shaped(ind)`; the indexed, IWf and infinitary routes say
  `NoWindowRoute`), and the windowless refusal reads it: a chain-shaped
  declaration is told that a deeper subterm is reachable only as a value a
  nested `match` on the recursive field binds; a branching one keeps the old
  text; a windowless route says so. Pinned in
  `lib/_tests/lang/descend_refusal_tests.hthr`, with the two-links-down
  positive beside it.
