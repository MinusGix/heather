---
title: First slice of type-owned namespaces: attach members, reach through the receiver
status: open
labels: [frontend,elaboration,modules,syntax]
created: 2026-08-05
updated: 2026-08-05
---

Small round item (2026-08-05 ergonomics round): the receiver half of
[[type-owned-namespaces]], sized to land on existing machinery. Two pieces:

1. The checked declaration form that attaches a fn/theorem to a type's
   namespace (`List::nth`, `Le::refl` as declarations, not naming
   convention) — the `Type::member` grammar already exists for
   constructors; this opens membership.
2. Elimination-shaped reachability only: `t.nth(k)`, `p.trans(q)` resolve
   through the receiver's type via the existing method fallback
   (`resolve_dot` / the `self`-parameter desugaring,
   crates/elab/src/lib.rs). No expected-type (introduction-shaped)
   resolution, no head-symbol namespace picking — those stay with the
   parent.

Success shape: `lib/std/list.hthr` declares `List::nth` and call sites in
[[list-algorithms-exercise]] write `t.nth(k)` (with
[[call-site-overapplication]] handling the curried tail).

## What it assumes from elsewhere
- **[[type-owned-namespaces]]** owns the design and its duality argument.
  Assumed here: only that the receiver direction is the
  uncontroversial half.
- **method-receiver-position** (closed) owns where the receiver lands in
  the argument list. Assumed here: only that `self`-parameter desugaring
  works for members resolved by type, same as for bare fns.
