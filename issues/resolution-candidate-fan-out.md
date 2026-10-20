---
title: Resolution tries every instance of a class; Decide makes that the widest it has been
status: open
labels: [elaboration,performance,traits]
area: language
created: 2026-08-17
updated: 2026-09-09
---

Selection filters the registry on the **class key alone** and then elaborates
each candidate in checking position against the goal
(`crates/elab/src/resolve.rs`, the candidate loop):

```rust
let mut cands: Vec<(String, bool, String)> = self
    .instances.iter()
    .filter(|((c, _, _), _)| *c == ckey)
```

The carrier head never narrows the set. So a goal at a class with N instances
costs up to N checking-position elaborations plus their conversions, and a
failed candidate is not cheaper than a successful one — it is the same work,
discarded.

## Why now

[[decide-class]] landed 2026-08-17 with six instances (`True`, `False`, `And`,
`Or`, `Not`, and whatever a caller adds), which makes `Decide` the widest class
in the registry — every other one has one or two. It is also the class most
likely to keep growing, because every new decidable proposition is another
instance, and composition instances are re-entered per subgoal during
backchaining, so the fan-out multiplies with depth rather than adding.

**Not measured.** Per `CLAUDE.md` this was not a perf round and nothing here is
a number. Filed as the accumulator the perf-work discipline asks for: the shape is
identified, the customer exists, and a round that names performance as the
point can pick it up.

## The obvious lever, and why it is not free

Narrowing candidates by carrier head before elaborating would cut the set to
one or two in the common case. But the head is *syntax* and goals are *types*:
`Le(3, 5)` reduces to `True`, so a goal already in whnf has head `True` while
the instance is keyed at `Le`, and a head filter would silently miss it. That
is a completeness change, not an optimization, and it wants deciding rather
than assuming — which is precisely why the current code tries everything.

A cheaper first move that risks nothing: order candidates so that a head match
is tried *first* and the rest still follow. Wins the common case, changes no
outcome.

## Related

- [[value-generic-instances]] would add instances at relations, widening
  `Decide` further. **Landed 2026-08-17**: `Decide` is at seven instances, one
  of them at `Le`. Still unmeasured, per `CLAUDE.md` — but the head-match-first
  ordering above is now worth more, since the new candidate is the one an
  arithmetic goal wants and it sorts in the middle.
- [[instance-binder-occurrence]] removed one *class* of wasted candidate
  (2026-08-17): an instance with a binder absent from its head can never
  resolve, and was tried on every goal of its class regardless. That is a
  guard against the fan-out growing, not a reduction of it — nothing in `lib/`
  had such an instance, so today's count is unchanged.
- The derived-instance table (`resolve.rs`'s canonical minting) already
  short-circuits repeat goals, so this is about distinct goals, not repeated
  ones.

## Log

- 2026-09-09: 2026-09-09: Ordering landed, set unchanged (docs/reflection-through-decide-instances-design.md §3): Traits::candidates(class, prefer) puts the instances registered at the goal carrier's head first, the head read off the solver parameter's written type at the call site (ResolveOb::applied carries the application's type arguments) and carried into the canonical-derivation mint. Datum for the narrowing this issue owns: over computed width-64 operands every Decide candidate whose head differs from the goal's costs ~6.5 GB to unify, won or rejected ([[type-level-reduction-over-computed-operands]]); with 15 instances the order alone took the closed fact from that to the library's footprint.
