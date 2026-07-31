---
title: Substitution still visits closed subtrees; skipping them needs per-node metadata
status: open
labels: [kernel,performance]
created: 2026-07-28
updated: 2026-07-31
---

**Deferred on purpose. Do not start this without the trigger below.** It is
filed so the measurement is not lost and so [[ir-simulate-design]] has
something to point at, not because it is next.

[[subst-rebuilds-unchanged-subterms]] made the traversal *share* a subtree it
did not change instead of rebuilding it. What it did not do is avoid walking
that subtree: `map_type`/`map_term` still descend into a closed annotation,
build a temporary node from `Rc`-cloned children, compare the change counter,
and drop the temporary.

`perf` on `wf/mirror-involution` after that fix (2026-07-28, release):

| | share of time |
|---|---|
| traversal proper (`sub_ty`/`map_term`/`map_type`, `SubstLocal` + `ShiftLocal`) | ~43% |
| `drop_glue` for the discarded temporaries (`Type` 13%, `Term` 12%, `Level` 3%) | ~28% |
| libc allocator (the nodes that genuinely change) | ~10% |

So roughly 70% of what remains is walking and discarding material that cannot
change. `nat/step-into-closed-body` says the same thing as a curve: still slope
~1, at 20 ns per closed node instead of 55.

## The two ways to stop visiting

**A′. `Option`-returning traversal.** Have `map_*` return `None` for
"unchanged" so a node is never *built* when nothing under it moved. Removes the
temporaries (~28%) and some of the traversal cost, keeps the failure mode
harmless (an unnecessary copy), and keeps the debug-time verification that
already guards this. Cost: every arm of the 65-arm match becomes
conditional — a much bigger diff than the counter was, in the one file where
binder bookkeeping lives, for a fraction of the remaining win.

**B. Per-node free-variable metadata.** Cache on each node whether it mentions
any local/global/universe variable (or the tighter loose-de-Bruijn range), and
return a closed subtree in O(1) without descending. This is the asymptotically
right answer — cost becomes proportional to the paths to the affected
variables — and it is what production kernels do.

Cost, and the reason this issue is deferred: the flag becomes part of the
**trusted base**. A wrong cached flag is a silently wrong substitution, i.e. a
soundness bug rather than a slow path, and the invariant has to be maintained
at every construction site in the kernel *and* in `elab`. That is a bad trade
against a 2–3× win nobody has yet needed.

## The trigger

Take this up when a real workload shows the remaining constant matters — the
concrete candidate being [[ir-simulate-design]]'s `simulate ir fuel` fixture in
the bench suite, since a fuel-indexed interpreter is one large recursor arm and
pays this cost per step. If that fixture lands and its per-step cost is
dominated by traversal of closed annotations, do A′ first and re-measure before
considering B.

Until then the numbers to beat are recorded in
`crates/kernel/benches/baseline.tsv`: `nat/step-into-closed-body` at 20 ns per
closed node, `wf/mirror-involution` at ~10 µs per tree node.

## What it assumes from elsewhere

- **[[subst-rebuilds-unchanged-subterms]]** owns the change-reporting
  traversal. Assumed here: only that sharing is decided by a counter checked
  per subtree, so "do not build" and "do not visit" are the two steps left.
- **[[kernel-benchmarks]]** owns the bench suite. Assumed here: only that
  `nat/step-into-closed-body` exists as the isolating curve.

## Log

- 2026-07-31: Promoted to the front of the [[simulate-conversion-cost]] queue by the 2026-07-31 delam reading: this is the cheap majority of that issue's cost (pure implementation, per-node free-variable bounds, no metatheory), and conv/simulate-payload (slope 0.91 today) is its acceptance instrument -- closed-subtree skipping should send that slope toward 0.
