---
title: "Inductive declaration compiler: tiered encodings"
status: open
labels: [frontend,elaboration,inductives,design]
area: language
milestone: [it-function-fields]
created: 2026-07-23
updated: 2026-10-20
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

**Scheme written and prototyped, 2026-07-24**, for the **linear fragment**
(≤ 1 recursive field per constructor): `docs/inductive-tier1-lowering.md`,
validated by `crates/elab/tests/tier1_fording.rs` (`List<Nat>` and `Bits`,
15 kernel-checked tests incl. append/assoc/flip-flip by induction and both
no-confusion regimes). Generator not written yet. Branching constructors
(≥ 2 recursive fields — the IR expression knot) do **not** lower by this
scheme and are split out to [[tier1-branching-constructors]]: exact height
is computable, but assembling a branching payload needs the children's
heights *compared*, so a node with an open child is not in constructor form
and `match` on it stops reducing.

## Tier 2 — infinitary (Acc, inductive families)

W + Id + funext-as-axiom via the standard indexed-containers reduction
(argued in [[kernel-v1-extensions]]; first-order data never lands here).
Generator support can lag; a hand-built `Acc` exercises the synthesized-ih
β rule ([[stress-proof-suite]] item 3).

**Generator for the first fragment, 2026-10-20:**
`docs/inductive-tier2-w-lowering.md` — a recursive function field, at most
one recursive field per constructor, unindexed. W + Id with **no** funext
axiom: a leaf predicate beside the tree does the work funext would have done
at the leaves. The rest of the tier is [[tier2-fragment-extensions]].

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
- 2026-07-24: Tier 1 SCHEME + HAND PROTOTYPE for the linear fragment (<=1 recursive field per constructor): docs/inductive-tier1-lowering.md, validated by crates/elab/tests/tier1_fording.rs (15 kernel-checked tests). Exact-height fording: D_ex : Nat -> Ty l by elim_Nat with motive Ty l (large elim), the recursive occurrence spliced in as the recursion variable's own code (no El/quote round trip), and the type is Sigma(h:Nat). El (D_ex h). Findings while writing it: (1) the two height classes PARTITION the constructors -- non-recursive ctors live only at height 0, recursive ones only above it -- so neither spine needs Empty padding and match splits on the height before touching the payload, which an earlier draft got wrong by insisting on one uniform spine; (2) the height being Succ-headed whatever the child is, is exactly what makes beta fire on open subterms (append (cons a l) ys == cons a (append l ys) with all three variables) -- pinned as a test because it is the property branching loses; (3) Unit-eta is load-bearing in the base case, which is what lets a bare refl discharge the nil case of an Id motive; (4) no-confusion splits into two regimes -- different height classes need only a zero/succ predicate on fst (one J, no payload analysis), same class needs the tag predicate as a FUNCTION OF THE HEIGHT (elim_Nat into Pi(v : El (D_ex h)). Ty 0), with a negative control that the cheap argument does not fire within a class; (5) injectivity is tier 0's constant-motive trick, with the recursive field's projection repackaging pair(m; payload). Prototyped on List<Nat> (append/append_nil/append_assoc) and Bits (flip-flip, sum spine, same-height disjointness) since List alone has one constructor per height class and so never exercises a sum. Branching (2+ recursive fields, the IR knot) split out to tier1-branching-constructors: it does not lower this way, and the reason is beta on open children, not effort.
- 2026-07-26: Tier-0 defect found 2026-07-26, split out as [[tyvar-scoping-in-lowered-fields]]: a type parameter instantiated at a CONTEXT-DEPENDENT type (the surface's only such form is `=`, whose endpoints are terms) is returned unshifted by lower_named, while lower_ctor has pushed the nominal tag and the earlier fields. So a parameter used in field j is under-shifted by 1+j and its free variables re-point at the tag and the preceding fields. It fails SILENTLY whenever the collision is type-correct — `Box2<A> { Mk(x: Nat, y: A) }` at `Box2<n = n>` lowers y's type to `x = x`, `Mk(3, refl)` is accepted, and the declaration states something the user did not write. That is precisely the hazard class docs/inductive-tier0-lowering.md opens by naming. It fails loudly only when the collision is ill-typed (a one-field constructor collides with the tag's Unit). Survived because every declaration in the suite instantiates its parameters at closed types, so every shift in the lowering is a no-op — the missing-observer pattern of [[unit-level-and-vec-preservation]], now at tier 0 rather than in the kernel.
- 2026-07-26: Tier 0's deferred 'dependent-field injectivity' item is promoted to its own issue, [[dependent-field-injectivity]], because container fields produced a second instance of the same restriction: a container's type '[D; len]' depends on the length field before it, so inj's constant motive would need both sides' lengths definitionally equal. Two instances of one restriction want a shared fix rather than a paragraph in each tier's scheme — and the container case is the more likely one to be hit, since a dependent payload field is unusual while a container field is dependent by construction.
- 2026-07-26: Tier 2 has its hand-built instance: Acc via W is kernel-checked (docs/acc-via-w.md, crates/kernel/tests/acc.rs, 13 tests), which is what the tier-2 section said a hand-built Acc would do -- it exercises the synthesized-ih beta rule at an abstract position, and it does so with Psi empty (no funext; see [[kernel-v1-extensions]]). What a tier-2 GENERATOR would now have to emit, from the construction: (1) the code-valued coherence predicate coh by elim_W at the large motive Ty 0, per declaration; (2) the four-argument ih spine -- ih is Pi(y : positions). M[f y/z], so a recursor case applies it to the position FIRST and only then to the index, the index proof and the coherence proof, which is the one place a bug hides; (3) index-fording via Id on the label, with the disjointness/injectivity story unchanged from tiers 0-1. Two surface blockers stay ahead of any of that: a function-typed inductive field (reject_function_fields) and the fact that Acc's positions are a Sigma over the carrier, so the surface would need to write R at all. Not scheduled.
- 2026-10-20: Tier 2 has a generator for its first fragment: a recursive function field (k: A -> D), at most one recursive field per constructor, unindexed (docs/inductive-tier2-w-lowering.md, crates/elab/src/infinitary.rs, [[recursive-function-fields]]). It is not the funext route this issue's tier-2 section planned: a leaf predicate carried beside the W tree (an Id from the leaf's children to the canonical elim_Empty function, proved by refl and eliminated by J in match) replaces the Empty-domain eta the kernel lacks, so Psi stays empty and constructors stay definitional at open payloads. Index-fording for tier 2 and the rest of the fragment are [[tier2-fragment-extensions]].
- 2026-11-05: gardener: cites a file it shares with [[parametric-type-families]] (`docs/inductive-tier0-lowering.md`).
