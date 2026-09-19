---
title: The showcases' five spec-relation wrappers can go, and RunSpec/OpRun become records
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

**What it may cost, and why that does not gate it.** Two costs pull the same
way and neither is visible from the diff:

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

**This is a readability round, not a perf round** (user verdict, 2026-09-19).
The nicer spelling is the deliverable and it lands on its own merits; if the
resulting form is worse, that is a **sign the language needs another round**,
filed as its own issue, and not a reason to keep the ∧ towers. Same doctrine as
"never distort the design for perf — a surprise is a pathology to file", and the
same call this tracker already makes for `lib/`: a row stalls on the missing
language feature rather than being written the ugly way that happens to be
cheap.

So the cold check before and after is worth *recording* — a diary entry, and a
good candidate for the first consumer of [[perf-ab-source-patch]] once that
exists — but it is not a gate, and this round does not wait on it. Concretely:
if the wrapper-free spelling costs, the finding is a kernel-side one about
comparing a λ over an inlined Σ tower where a δ-stuck spine used to stand, and
it belongs in the kernel-side structural pass that is the next perf move, not
in this round.

Do **not** bundle this with the `⟨⟩`/`calc` conversions
([[showcases-predate-their-ergonomics]] says so from its side): those carry no
term growth, and keeping them separate means a recorded cold-check change has
one candidate cause.
