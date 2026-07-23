# Kernel v0 design

Scope and representation decisions for the first Rust kernel. Source of truth
for the theory is `docs/delam/04–06` (see `docs/delam/README.md`; chapters
01–03 are a simplified warm-up system we do *not* implement).

## Fragment

v0 implements the **full 4-layer DeLaM of chapter 04**, not a reduced modal
fragment — the layering is load-bearing for everything Heather cares about
(intensional analysis with decidable conversion), and the parts interlock too
tightly to stage: Tarski universes force the type/term split, code promotion
forces layer p, the recursors force universe polymorphism and annotated
applications. Concretely:

- Layers `v < c < p < m` with `typeof` as in ch. 04; layer v admits only the
  variable/global-variable/conversion rules (ch. 04 "Note on Layer v Rules").
- Tarski-style universes: types and terms are separate sorts; encodings
  (`Nat`, `Π`, `Ty l` as terms) decode via `El`. Non-cumulative; explicit
  levels on Π, λ, app.
- Universe levels with variables, `⊔`, `ω`; equivalence decided by the
  count/adjust map normalization (ch. 04 §universe-levels). `ω` is
  checker-internal: never written in programs, only the type level of `ΠΠ`.
- Universe polymorphism: `ΠΠ ℓ⃗. T` / `Λ ℓ⃗. t` / `t $ l⃗`, non-empty level
  vectors, layer m only.
- Nat with its recursor; fully-annotated dependent functions
  (`app(t; l,l'; x:S.T; s)` keeps S and T as sub-structures — required by the
  code recursors).
- The modal part: global contexts with three binding forms
  (`g : Ctx`, `U : Typ_i(Δ, l)` for i ∈ {c,p}, `u : Trm_i(Δ ⊢ T @ l)` for
  i ∈ {v,c}); local substitutions `·^k_{g?}`, `wk^k_g`, `δ,t/x`; global
  variables `U^δ`, `u^δ`; meta-functions over contexts (`CtxPi/CtxLam/CtxApp`)
  and over types (`TyPi/TyLam/TyApp`); contextual types `□(Δ ⊢ Ty l)` and
  `□(Δ ⊢ T @ l)` (both at universe 0); `box`; `letbox` for both kinds; and the
  two mutual recursive principles over code (4 type branches, 9 term
  branches).

Explicitly out of v0: coinduction/effects, typeclasses, compiler machinery,
inductive types beyond Nat, the type lifter (omitted by the paper too).

## Algorithms

- **Conversion is ch. 06 verbatim**: untyped weak-head reduction to
  WHNF/neutral, then structural comparison. Not NbE, not typed reduction.
  Function-type comparison is η-directed (compare applications to a fresh
  variable); boxed types/terms compare by **syntactic equality**; recursors
  block on neutral scrutinees *and* on boxed global variables `□(U^δ)` /
  `□(u^δ)`; neutral comparison is an inference step that returns a type.
- **Level equivalence**: normalize to `adjust(count(l))` maps and compare;
  `ω` compares only to itself.
- **Conversion presupposes well-typed inputs.** The algorithm is only
  sound/complete on well-typed terms (ch. 08); on garbage it may return a
  meaningless `NotConvertible`, burn fuel, or panic in substitution's
  scope-invariant assertions. It therefore skips premises that
  well-typedness makes redundant (e.g. it does not re-check that an
  `elim_Nat` scrutinee's inferred type is `Nat`). The type checker must
  call it only on already-checked inputs — this is a kernel trust-boundary
  invariant, not a robustness bug.
- **Conversion's judgment-level inputs are inert.** Every universe level
  the ch. 06 rules actually compare is an *annotation* on the terms (or
  inferred from a binding); the `l` in `T ≈ T' : l` never branches the
  algorithm. It is threaded anyway so the functions match the paper's
  judgments. Fuel is a single shared budget (reduction steps + comparison
  nodes); the fuel *policy* is the caller's, to be fixed by the type
  checker.
- **Type checking** is syntax-directed on fully explicit core terms — the
  kernel does no inference, no implicit insertion, no elaboration. The
  conversion rule fires exactly where the bidirectional structure demands a
  check against an expected type.

## Representation

- **de Bruijn indices, three independent namespaces**: local variables
  (into Γ), global variables (into Ψ — one index space covering all three
  binding forms), universe variables (into L). A binder never shifts the
  other two namespaces' indices. All names in the tex are display-only.
- **Separate `Type` and `Term` enums**, mutually recursive, mirroring the
  Tarski split. Judgment functions will be similarly mutual.
- `Rc` for sub-terms (substitution clones aggressively; sharing keeps that
  cheap; no interior mutability anywhere).
- Local contexts are `(base, entries)` where base is `·` or a context
  variable `g`; entries carry `(T, l)`.
- Local substitutions mirror the paper's three-form syntax including the
  `·^k_{g?}` / `wk^k_g` tails and the query operations δ̂ (length) and δ̌
  (base) used by composition.
- Recursor motives/branches are **fixed-shape structs**, one field per branch,
  each field a term under a documented telescope of binders (the ch. 04 branch
  telescopes) — not a list, so exhaustiveness is structural.

## Discipline

Mirror the Coq formalization's structure: same judgments, same rule names in
comments, so divergences are auditable. Correctness over performance
throughout; no `unsafe` (enforced workspace-wide).
