---
title: "Inductive declaration compiler: tiered encodings"
status: open
labels: [frontend,elaboration,inductives,design]
created: 2026-07-23
updated: 2026-07-24
---

Mechanize the encoding doctrine of [[kernel-v1-extensions]]: surface
`inductive` declarations compile to the fixed-former kernel. This is the
load-bearing design object of the frontend — needed identically by the
stress proofs, the IR, and everything after — and the one frontend
component whose bugs prove theorems about the *wrong type* rather than
producing rejected terms. Hence the hard rule: **each tier's lowering is a
written mechanical scheme** (like the recursor telescopes), reviewable
against the kernel. The compiler stays untrusted (kernel checks its
output), but "user proved a theorem about an encoding that isn't what they
meant" is a failure the kernel cannot catch.

Pipeline: parse decl → positivity check → tier classification → generate
(type encoding, constructors, eliminator, no-confusion) → emit core.

## Tier 0 — non-recursive (Bool, Option, most IR node shapes)

Plain sums-of-Σs: tags are nested `A + (B + …)`, fields are right-nested Σ.
`match` = nested `case`; no-confusion (constructor injectivity +
disjointness), disjointness by large elimination into `Unit`/`Empty` — the
Tarski setup gives large elim since motives land in `Ty l` encodings.
Entirely mechanical; do first.

**Done, 2026-07-24.** The mechanical scheme is
`docs/inductive-tier0-lowering.md` (written first, then mechanized in
`crates/elab/src/inductive.rs` section by section); see the Log for the two
places implementing it corrected the scheme.

## Tier 1 — recursive finitary (List, the IR expression knot)

Nat-fording. **The one research-adjacent spot in the frontend plan.** The
dragon: a naive depth-*bound* encoding (`Σ n. Approx n`) has equality finer
than the intended type — `nil` at bound 3 vs bound 5 are distinct pairs;
that reinvents the setoid problem and would drag [[setoid-auto-lifting]] in
early. Committed fix: **exact-height fording** — constructors compute their
precise height (length for List, max+1 for trees; always computable in the
finitary tier), so canonical forms are unique and definitional equality is
the intended one. Eliminator by `elim_Nat` on the height, `elim_Empty`
discharging impossible cases; β on canonical constructors is definitional
(heights are concrete numerals there); open scrutinees are neutral, as
they should be.

**Hand-prototype List before writing the generator** — it is the
acceptance test of the whole tier ([[stress-proof-suite]] item 2).

## Tier 2 — infinitary (Acc, inductive families)

W + Id + funext-as-axiom via the standard indexed-containers reduction
(argued in [[kernel-v1-extensions]]; first-order data never lands here).
Generator support can lag; a hand-built `Acc` exercises the synthesized-ih
β rule ([[stress-proof-suite]] item 3).

## Scope notes

- Parameters: straightforward (prenex, substituted through the scheme).
- Indices: via fording (Id equations on constructor results) — design the
  tier-1 scheme so indexed finitary types are the same machinery, not a
  fourth tier.
- Derived per-inductive artifacts (recursor, no-confusion, later:
  size/height lemmas) are generated *terms* checked by the kernel —
  auditable, never trusted.

## Log

- 2026-07-23: Opened; tiers, exact-height decision, and the
  List-prototype-first discipline from the frontend-first route discussion.
- 2026-07-24: Tier-0 lowering scheme written down before code: docs/inductive-tier0-lowering.md — sum spine over constructors, Unit-terminated Sigma spine per constructor (uniform field offsets; the trailing Unit is free by Unit-eta), injection paths, field projection as fst(snd^j) aliased into arm bodies, match as nested Case with the motive composed with the injection at each depth (the one place a bug would hide), and no-confusion split into disjointness (tag predicate by large elim into Ty 0 — any levels) and injectivity (code-valued family + cong — level-0 fields only, non-cumulativity blocks the Unit default at l>0). Verified against the kernel rather than assumed: Sigma-eta (conv.rs:668), Unit-eta (conv.rs:696), El decoding of every extension code (reduce.rs:93). Open decision blocking implementation: nominal collapse — structurally identical declarations share a kernel type, so 'True = Left' would check; recommendation is a per-declaration Id(Nat;k;k) tag prefix. Blocked-by elaborator-design dropped (stages 1-2 landed).
- 2026-07-24: Tier 0 IMPLEMENTED (crates/elab/src/inductive.rs, 24 acceptance tests in crates/elab/tests/inductive_tier0.rs, all kernel-checked). Surface: 'inductive D<p> { c(f: T, ...) }' declarations, named/applied types in type position, n-ary match arms (Nat's Zero/Succ now go through the same arm grammar), constructors in checking and inference position, 'absurd(p)' and 'inj(k, p)' for no-confusion. Two places where writing the code corrected the written scheme, both now in the doc: (1) the nominal tag cannot be Id(Nat;k;k) — a dependent motive forces 'inl x' to convert with 'inl (pair tag <>)', which Sigma-eta reduces to 'fst x = tag', and Id has no eta, so 'neg(neg(b)) = b' by match was rejected; the tag is now a binary Sigma-of-Units tree, which is proof-irrelevant (eta) yet structurally distinct (type conversion is structural). (2) injectivity needs no codes and no large elim: using the lhs's own field value as the default in the other branches keeps the motive constant, which also drops the level-0 restriction the doc had; the remaining exclusion is a field whose type depends on an earlier field, diagnosed rather than mis-derived. Deferred: tier 1 (recursive) is classified and rejected with a pointer; type-argument inference is narrow (parameter-as-whole-field-type only); phantom parameters still collapse.
