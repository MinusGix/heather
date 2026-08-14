# Syntactic reflexivity for conversion on large canonical values

Round of `issues/conversion-cost-at-large-values.md` (2026-08-14). The issue
asked one question first: take the reproducer's handful of individually
expensive conversions (`k_bind_mono`, lib/ir_v1.hthr) and say what each one
is comparing. This doc records the answer, the lever it justified, and what
was rejected. Numbers live in the issue log, per the standing policy; this
file carries shape claims only.

## 1. Attribution: what the expensive conversions are

Instrumenting the public `conv_type` (site-tagged from `typing.rs`, with a
deep `==` control per call) on the reproducer showed:

- Every expensive conversion enters from **one seam**: `Tc::tm_check`'s
  fallback — infer the type, then convert expected against inferred. None
  came from the Lam-domain premise, none from the elaborator's unification
  side.
- The inputs are `Id`-types whose endpoint terms are the workload's large
  canonical values — Wf-encoded constructor trees (`supf`/`pair`/`inl`/`inr`
  over Σ-tuple children) under a long application spine of library globals.
- The dominant class is **syntactically equal pairs**: the expected type and
  the inferred type are two separately built copies of one tree — deep
  `==`-equal, never pointer-equal, so every landed shortcut of the closed
  `conv-pointer-equality-reflexivity` round missed them. On this seam the
  overwhelming majority of *all* `conv_type` calls (not only the expensive
  ones) compare equal syntax; the structural walk over the value domain paid
  orders of magnitude per node over what `==` pays (the per-node gap is
  `value-domain-allocation-constant`'s constant, multiplied by the whnf,
  view, and closure allocations of a full judgmental descent).
- The residual class is **genuinely different pairs** — same giant equal
  prefix, a real difference deep inside (not a level spelling:
  `normalize_levels` equality was tested per call and never held) — whose
  cost is real reduction plus comparison. That part decomposes into the
  known constant and stays.

So the verdict on the issue's own question: the cost was NOT its own defect
in the sense of re-forcing or quadratic unfolding — it was reflexivity paid
at full structural price, plus the accepted value-domain constant on the
genuinely-different remainder.

## 2. The lever: syntactic reflexivity, two seams

α-equality is `==` under de Bruijn, and `==`-equal level annotations are
trivially `equiv`, so equal syntax in one scope is convertible by
reflexivity — the same argument the pointer round recorded in kernel
DESIGN.md, with object identity relaxed to syntactic equality.

1. **Root types** (`Conv::ty_root`): after the existing borrowed-object
   check, `a == b` settles before whnf. A failed `==` stops at the first
   difference in depth-first order, so its cost is bounded by a prefix of
   the walk the structural comparison performs anyway; the pathological
   shape (a huge equal prefix that whnf would have collapsed early) is a
   tree conversion already walks structurally today.
2. **Value-domain children** (`Values::ty_eq_fast`,
   `Values::tm_identity_fast`): a hit no longer requires the same closure
   pointer — two *syntactic* closures over the same environment spine
   (head-pointer identity, `value::Env::ptr_eq`) with `==`-equal bodies
   denote the same object, because evaluation is a function of the
   (environment, body) pair. The `home`/`sat` scope gate is unchanged and
   still load-bearing. This catches the equal endpoint/spine-argument
   subtrees inside root-unequal comparisons, where both sides were read
   from one ambient ρ.

Fuel policy follows the landed precedent: every hit spends the comparison
node's one unit. `Conv::ctx`'s syntactic-equality check and the □ code
comparison were already deep `==`; nothing there changes. Raw term roots
(`tm_root`) stay untouched: the re-measurement again found zero root
`conv_term` calls on the workload, matching the closed round's finding.

## 3. Rejected alternatives, in order

- **Memoizing conversion verdicts on (value, value) pairs.** The measured
  workload has no repeated expensive pair — each slow conversion is a fresh
  expected/inferred pair — so a verdict table would hit nothing the
  reflexivity check doesn't already settle, and it adds a cache keyed on
  values, whose identity is exactly the hard part.
- **Entry-wise environment comparison in the fast path** (walking both
  spines comparing entry pointers, not just the head). Implemented and
  measured: zero additional wins on the reproducer — by the time
  environments diverge structurally the sides have genuinely diverged — so
  the simpler head-pointer test stays.
- **Sharing-aware readback / making the elaborator hand conversion shared
  `Rc`s.** Attacks the same waste from the producer side, but the seam is
  many (every route that builds an inferred type), and the kernel must not
  depend on callers sharing; the kernel-side check is one seam and caller
  independent.
- **Budget-bounded structural equality** (bail after N nodes). Insurance
  against an adversarial deep-equal-prefix pair, but it adds a hand-written
  traversal over two large enums for a shape no measured workload exhibits,
  and the bench families that exercise near-equal pairs
  (`conv/perturbed-pairs`) gate the risk. Revisit only if a bench or a real
  workload shows a failed-`==` pathology.
- **Doing nothing (architecture verdict).** Wrong, by measurement: the cost
  did not decompose into `value-domain-allocation-constant` alone — most of
  it was reflexivity paid structurally, which is a missed short-circuit,
  not a constant.

## 4. Acceptance criteria

- The reproducer (`k_bind_mono` and its file) and the whole `lib/ir_v1.hthr`
  check materially faster; the certgen family's per-binary walls move on the
  `_gen_conv`-dominated binaries. Numbers in the issue log.
- Full `scripts/test` green, including the updated fuel pins: a
  syntactically equal (non-shared) root type now converts in one unit, and
  the one-unit OutOfFuel control moved to a convertible-but-unequal pair;
  scoped unit tests pin the closure fast path's env/body/scope gating.
- `scripts/bench --check` within thresholds on all comparisons — notably
  the `conv/*` families, whose perturbed corpus exercises the failed-`==`
  path.
- Kernel DESIGN.md's reflexivity boundary paragraph updated in place; the
  differential oracle untouched (the syntax domain keeps its own
  pointer-identity shortcuts; verdict agreement is unaffected because the
  new hits are conversions that succeed either way).
