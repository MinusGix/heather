---
title: The showcases' five spec-relation wrappers can go, but only under a measured cold check
status: open
labels: [showcase,ergonomics,perf,stdlib]
created: 2026-09-19
updated: 2026-09-19
---

[[record-type-partial-application]] landed the language half on 2026-09-19: a
record type can be partially applied, so `Certified<Char, Expr>(source, begin,
GrammarSpec(level))` can be written `…, Grammar(level))` and the wrapper
deleted. This issue is the showcase half, which that round deliberately did not
do, and it has two parts that want to land together.

**The edits.** Delete the three do-nothing `fn` wrappers (`GrammarSpec` in both
calculator showcases, `RunSpec` and `OpRun` in `docs/showcase/calc_text.hthr`)
by making `RunSpec` and `OpRun` **records with named fields** instead of ∧
towers over `Certified`'s relation slot. That is the large half of
[[record-type-partial-application]]'s 09-19 count: 29 positional projections
into anonymous conjunctions — 4 `op.evidence.left.left`, 4
`close.evidence.left.right`, 7 bare `.left`, 14 bare `.right` — become named
projections, the way `Grammar`'s consumers already read `l.span`,
`inner.yields`, `atom.at_level`.

**Why it is a measurement and not an edit.** Two costs pull the same way and
neither is visible from the diff:

- A record adds Σ layers to exactly the term family measured at 27× in
  [[elaborator-canonical-type-spelling]], on the file whose semantic image is
  483 M nodes against a 256 M budget — so it is never stored, `--only` has
  nothing to replay ([[check-only-no-stored-image]]), a recheck is ~95 s
  however small the edit, and a cold check already needs more than 8 GiB.
- Deleting a wrapper is not free either, and this is the part
  [[record-type-partial-application]] found while implementing it.
  `GrammarSpec(level)` needs no η-expansion at all: a global's term is a
  reference, so the partial application is a **δ-stuck neutral spine** whose
  head conversion compares before it unfolds. `Grammar(level)` is a **λ over
  the inlined record lowering**, and two of those compare structurally, Σ tower
  and all. So the ergonomic win trades a cheap head comparison for a
  structural one, at every relation slot in the file.

So: batch every edit into one round, measure the cold check before and after,
and if the wrapper-free spelling costs, say so — the honest outcome may be
"named records yes, wrapper deletion no", or a kernel-side round on the
comparison itself, and either is a better finding than the edit.

Do **not** bundle this with the `⟨⟩`/`calc` conversions
([[showcases-predate-their-ergonomics]] says so from its side): those are pure
surface with no term growth, and a cold-check regression should have one
candidate cause. `scripts/perf ab` cannot measure a `.hthr` change today —
it compares two binaries and would refuse this as one binary against itself
([[perf-ab-source-patch]]) — so the before/after here is two cold
`heather check` runs, wrapped per CLAUDE.md.
