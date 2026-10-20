---
title: "Let decision instances own recursive procedures without public helper names"
status: open
labels: [design,frontend,traits,stdlib,ergonomics]
area: language
created: 2026-08-20
updated: 2026-08-20
---

The standard library currently declares public helpers such as `le_dec` and
then installs a one-field instance whose body merely calls that helper. Most
clients should ask for `Decide<P>` or write `if h : P`; naming a carrier's
specific procedure leaks implementation vocabulary into proofs.

Inlining is not equivalent today. Nat's deciders recurse, while an instance
body has no recursive self-name or derived structural implementation. Explore
one of: named recursive instance bodies, a private/local declaration usable by
the instance, or derivation of a decision dictionary from the structurally
recursive relation. Preserve transparent computation at closed inputs: making
the helper an opaque theorem would break conversion-based proofs.

## Acceptance

- Nat order and equality decisions can be implemented without a separately
  public `le_dec` / `eq_dec` API name.
- Bool and Int follow the same client-facing convention.
- `decide<P>()` and proposition-directed `if` compute at closed inputs exactly
  as before.
- Recursive termination and transparency are explicit and kernel-safe; this
  is not achieved by hiding an unchecked recursive call in resolution.

## What it assumes from elsewhere

- [[decide-class]] owns the landed `Decide<P>` interface. This issue changes
  where its implementation may live, not the meaning of decidability.

## Log

- 2026-08-20: Filed from the standard-library surface review after confirming
  that nonrecursive instances could inline today but Nat's recursive deciders
  cannot, so deleting the names mechanically would make the library uneven.
