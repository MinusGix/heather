---
title: omega certificates spell their atom list at every use; bind it once
status: open
labels: [omega,performance,proofs]
created: 2026-09-26
updated: 2026-09-26
---

`omega`'s certificate for a small goal (five Nat facts, six atoms) is 203 KB
of source. It spells its atom list, `[OfNat(sv), OfNat(r), …, OfNat(b)]`, 177
times: inside every `omega::basis(i, atoms)`, `zeros(atoms)`, `dot(row,
atoms)` and lemma argument. Measured 2026-09-26 at width 1:

- per kernel check, `Nil` costs ~43 steps, each `Cons` ~85, an Int literal
  ~44, so this list costs ~820 steps per copy;
- 177 copies are ~145k of the item's 152k kernel steps;
- the certificate has 4,199 `list::Cons` and 868 lists in all, and the
  elaborator parses and elaborates all 203 KB.

An identity lemma applied to *variable* lists costs 0 kernel steps; applied to
literal ones, ~3k.

## Proposed shape

Bind the atoms once, as a variable. The certificate becomes
`(λ (A: List<Int>) (e₀: nth0(0, A) = OfNat(x₀)) … => cert)(atoms, refl, …)`,
so the literal list is checked once and each `eᵢ` by one computation. Inside,
rows are spelled as literal coefficient lists (not `basis(i, A)` or
`zeros(A)`, which would be stuck on a variable `A`), `dot(row, A)` stays
symbolic, and an atom enters only through `normalize_atom(i, A)` transported
along `eᵢ`. Combinations still compute on literal rows. Expected: kernel cost
per certificate proportional to its steps, not to steps × atoms; source a
fraction of the size.

## Acceptance

- The measurements above drop by an order of magnitude on the same goal, and
  `scripts/perf ab` over the omega-heavy corpus shows the whole-workload total
  moving.
- Every omega suite member passes unchanged (splits, cutsat, division atoms,
  wide constants).

## What it assumes from elsewhere

- **[[bv-omega-check-cost]]** found this. `bv_omega`'s per-call overhead is
  mostly `omega` certificates.

## Log

- 2026-09-26: Premise revised before implementation. Binding the atom list once does not pay
  by itself. With `A` a variable, `basis(i, A)` and `zeros(A)` are stuck, so the
  rows must be literal coefficient lists, and a literal row of m Int
  coefficients costs the kernel about what the atom list does. That would trade
  177 copies of the atom list for 126 rows.

  What a list costs, traced with `HEATHER_CONV_MISS_TRACE` (value-metrics
  build): each `Cons` misses three conversions. `El(List#tycode(A))` against
  `Wf`: the tail's type code, unfolded and decoded. `Vec` against `Σ`: the
  children type, with the arity's `case` evaluated on the label. `Vec` against
  `Unit`. The kernel has a memo for exactly these cross-head queries
  (`Tc::conv_ty`, keyed by the `Rc` identity of an anchor sub-term), but it hits
  0 times on a `Cons` chain (`cons3`: 22 misses, 0 hits). Every constructor
  value gets freshly allocated annotations from `build_ctor`, so the anchors
  never match. A monomorphic `inductive NatList` (named `Wf` slots) is somewhat
  cheaper per node, and still 22 misses and 0 hits.

  So the lever is the emission of constructor values: share each
  instantiation's annotation allocations within a declaration, so repeated
  nodes hit the memo or `Rc` pointer equality. That would help omega's
  certificates and every list-heavy term. It belongs to the emission-cost line
  (`docs/wf-shape-code-design.md`, `docs/annotation-component-respell-design.md`)
  rather than to omega.
- 2026-09-26: Annotation-interning round (uncommitted). A constructor value's children
  annotation and its `sup_f` shape and arity slots are built once per
  declaration (`DeclAttempt`) and shared. In the kernel memo's bucket hint
  (`type_anchor`), an `El` headed by a global anchors on the global's index,
  since its local weakening is rewritten by every substitution, so no two
  occurrences ever share an allocation; a `Vec` or `Σ` anchors on its element.
  Hits are still confirmed by full equality.

  Result: `cons3` 298 → 173 steps (0 → 5 memo hits). Across the `bv_omega`
  fixture and omega's own lemmas, conversion misses fall 8–15%, queries are
  unchanged, seconds fall 10–20% on one noisy pair (not an ab).

  The premise this chain started from does not hold. An `omega` item's kernel
  steps barely move (152.6k → 151.6k). The value-metrics miss table puts its
  conversion misses at ~0.16 s of ~0.56 s, the largest share 13 `El`/`El`
  misses (64 ms): certificate-level comparisons that evaluate `dot` and Int
  arithmetic, not constructor typing. The ~145k-steps-from-lists figure was an
  estimate (per-literal cost × copies), never measured against `omega` itself.
  Omega's certificate cost needs its own attribution before another round.
