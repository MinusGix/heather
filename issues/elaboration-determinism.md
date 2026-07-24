---
title: Elaboration determinism as an enforced guarantee
status: open
labels: [frontend, elaboration, testing, metaprogramming]
created: 2026-07-24
updated: 2026-07-24
---

For most compilers, deterministic output is hygiene. For Heather it is a
**semantic commitment**, and that is the reason to enforce it early rather
than assume it.

The commitment comes from sketch round 2 ([[surface-syntax]] log,
docs/sketches/surface-v2.md): `.code` on a top-level `fn` quotes the
*elaborated* term, and intensional analysis keys on that. So the elaborator's
output is observable *inside the language* — a meta-function can branch on
it. Two elaborations that differ in any way a `match code` can see are two
different programs, not two spellings of one. Anything downstream that keys
on elaborated syntax inherits this: [[certifying-generator]]'s prove-once
shape, [[compile-typeclass-design]]'s dedup by "(syntax, descriptor)"
keying, and [[setoid-auto-lifting]]'s boxed-code introspection.

## What could break it today

Nothing known to be broken — this is about not *acquiring* the bug:

- **Hash-map iteration.** `Elaborator.globals` is a `HashMap<String,
  GlobalInfo>` and `goal_spans` a `HashMap<(usize,usize), usize>`. Both are
  only ever *looked up*, which is fine; the day one is iterated, output order
  becomes hash-seed dependent. Rule: never iterate a `HashMap` in a way that
  reaches the emitted term — use `BTreeMap`, or a `Vec` in insertion order,
  or sort. (`rustc-hash` would make iteration deterministic within a build
  but is a footgun as a *fix*, since it hides the intent.)
- **Address/pointer identity.** `Rc::ptr_eq`-style shortcuts are legitimate
  optimisations but must never change *which* term is emitted, only how fast
  it is found. Hash-consing ([[dependency-policy]]) is where this will get
  tempting.
- **Ordering coming out of goal machinery.** Goals are already numbered in
  creation order and discharged in source order, both deterministic by
  construction ([[goal-holes]]) — worth a regression test rather than a
  comment, since the padding/dedup logic is the kind of thing a refactor
  reorders.
- **Anything time-, path-, or environment-derived** in a term. None today.

## Deliverable

1. A determinism test: elaborate the same source twice in one process and
   assert the emitted terms are identical (`PartialEq` is derived on the
   kernel types), plus the suite run under a different hash seed
   (re-running with a changed `RandomState` is enough to catch iteration
   order).
2. A golden hash of the elaborated Nat suite — cheap, and it turns "the
   elaborator's output changed" into a visible event rather than a silent
   one. This is a good `insta` snapshot once that lands
   ([[dependency-policy]]).
3. A line in `crates/elab`'s module docs stating the guarantee and the
   `HashMap` rule, so the next person adding a map knows it is load-bearing.

## Later, harder version

Determinism *across versions* of the elaborator is a stronger and much more
awkward property: it means an elaborator change can invalidate a proof that
pattern-matched on generated code. Worth knowing this is coming before
[[certifying-generator]] leans on syntax keying; the mitigation is probably
that certified generators prove things about the code they *see*, not about
code the elaborator promised to keep producing. Not a problem to solve now,
but a reason not to let syntax-keying spread casually.
