---
title: Substitution rebuilds subterms it cannot change, so a β-step costs the whole body
status: open
labels: [kernel,performance]
code: crates/kernel/src/subst.rs:560 @ 489b241
created: 2026-07-28
updated: 2026-07-28
---

`map_term`/`map_type` allocate a fresh node for **every** node they visit. A
subtree containing no occurrence of anything being substituted is therefore
rebuilt identically — same shape, same indices, new allocations — and the `Rc`
sharing that made it cheap to carry around is thrown away. The traversal has no
notion of "nothing happened here".

Sequel to [[subst-copies-payloads-at-depth-zero]], which fixed the case where
the *whole operation* was the identity. This is the case where the operation is
real but most of the tree is untouched by it, and it is the larger one.

## What it costs, measured

`nat/step-into-closed-body` isolates it: one `elim_Nat` β-step whose body is
`add n̄ y`, so instantiating it must replace `y` and walks the closed numeral
`n̄` for nothing.

| closed nodes in the body | one β-step |
|---|---|
| 64 | 2.9 µs |
| 256 | 13.7 µs |
| 1024 | 65.3 µs |

Slope 1.11, ~55 ns per node that cannot change.

**The real workload it explains is `wf/mirror-involution`** — `Wf` elimination
at depth, i.e. the shape every generated recursor has. Decomposed
(2026-07-28, depth 5, 63 constructors):

- 2432 reduction steps, i.e. a flat **38 steps per constructor** at every
  depth. The algorithm is fine: step count is linear in the data.
- 85 ms total, so **35 µs per reduction step** — against a step body of 413
  nodes, which is ~700 nodes rebuilt per step once the payloads and the `nth`
  instance are counted.
- `perf` agrees about where it goes: `map_term::<SubstLocal>` 8.9%,
  `map_type::<SubstLocal>` 6.1%, `map_term::<ShiftLocal>` 6.3%,
  `Rc::drop_slow` 12%, libc `malloc`/`free` ~23%. Over half the time is
  allocate-copy-free of terms; nothing is *searching*.

A generated recursor arm is mostly closed type annotations (`Tree`,
`Vec(Tree; 2)`, `Fin 2`, the case motive) wrapped around a handful of variable
occurrences. Substitution currently pays for the annotations, every step, at
every node of the data.

## Why it matters

This is the cost model of *running a user-declared datatype's eliminator*, and
by extension of [[ir-simulate-design]]'s `simulate`: a fuel-indexed interpreter
is one big recursor arm, so its per-step cost is its own body size. Linear in
fuel with a 35 µs constant is not a checker that replays programs. The same
constant sits under `code/whnf-identity-recursor` (branch instantiation) and
under every conversion that has to reduce before comparing.

## Two ways to fix it

**A. Change-tracking traversal** (preferred; no representation change). Let the
traversal report "unchanged" so a parent reuses the child's existing `Rc`
instead of allocating a copy. The entry points already return `self.clone()`
when the whole operation is trivial; this extends the same idea to subtrees.

The design constraint to respect: "unchanged" must propagate up from *leaves*,
never be decided by comparing subterms. A node is unchanged iff every child
came back unchanged and its own mapper case produced the same leaf — so the
only equality tests are on variables, levels and tails, all O(1)-ish. Comparing
`Term`s to detect no-ops would reintroduce the cost it removes, and worse,
would make it look fixed on the bench while `PartialEq` did the walking.

Mechanically: `sub_tm`/`sub_ty` return something like `Option<Rc<_>>` (`None` =
unchanged), the `Mapper` leaf hooks gain the same convention, and the node
constructors run only when some child changed. It is a mechanical refactor of
one file, which keeps the binder bookkeeping in the one place it lives now.

Cost: still visits every node (O(size)), just does not allocate. Given that the
profile is allocator-dominated, that alone should be most of the win — but it
does *not* make substituting into a large closed annotation free, only cheap.

**B. Free-variable metadata on nodes** (skips subtrees without visiting them).
Cache per node whether it mentions any local/global/universe variable at all —
or the tighter "loose de Bruijn range" — and let the traversal return a closed
subtree untouched in O(1). This is the standard trick in production kernels and
it is the asymptotically better answer: cost becomes proportional to the *paths
to the affected variables* rather than the tree.

Cost: a field on every `Term`/`Type` node, an invariant that every constructor
must maintain, and that invariant becomes part of the trusted base — a wrong
cached flag is a silently wrong substitution, which is a soundness bug, not a
slow path. That is a real bar. It also touches every construction site in the
kernel *and* the elaborator.

**Recommendation: do A, re-measure, and only then decide whether B is
justified.** A is contained and its failure mode is an unnecessary copy; B's
failure mode is unsoundness. If A brings a β-step's cost near the number of
nodes it actually rewrites, B buys little on real recursor arms.

Explicitly not in scope, again: hash-consing and conversion caching
([[dependency-policy]] records why those are separate decisions).

## Verification

- The laws in `tests/subst_laws.rs` are the safety net and already cover the
  interesting failure: if "unchanged" is ever reported wrongly, identity and
  composition break on generated terms.
- Extend `shifting_by_zero_preserves_sharing` with the subtree case:
  `Rc::ptr_eq` on a closed annotation before and after a *nonzero*
  substitution elsewhere in the term. Sharing, not equality — equality passes
  against the copying traversal too.
- Mutation-test the propagation: report "unchanged" when a child did change,
  and confirm the laws fail. A change-tracking traversal whose flag is wrong is
  exactly the bug worth proving the tests catch.
- `nat/step-into-closed-body`'s band becomes `(-0.15, 0.15)` under B, and
  something well under 1 under A (it still visits, so expect a much smaller
  constant rather than a flat line). `wf/mirror-involution` is the end-to-end
  number; `scripts/bench --save` after.

## What it assumes from elsewhere

- **[[kernel-substitutions]]** owns the substitution algebra and its laws.
  Assumed here: only that the laws are stated over generated terms, so they
  catch a wrongly-reported no-op.
- **[[kernel-benchmarks]]** owns the bench suite. Assumed here: only that
  `nat/step-into-closed-body` and `wf/mirror-involution` exist, so a fix has a
  proof and an end-to-end number.

## Log
