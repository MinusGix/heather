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
  branches in the paper; see the extension below).

**Extension beyond the paper** (issues/kernel-v1-extensions.md): the identity
type — `Id^l(S; t; u)` with its encoding `Id^l(s; t; u) : Ty l` (decoded by
`El (Id …) ⇝ Id (El …)`), intro `refl^l(S; t)`, and Paulin-Mohring based
path induction `J^{l,l'}(S; a; y p. M; c; u; e)` with β `J … refl ⇝ c`.
DeLaM has no Id; every rule here is ours, flagged `(extension)` in comments,
and follows the paper's discipline: fully annotated so everything but `box`
infers, and the sub-structures are recursor-reachable. The code recursors
gain four branches (`ty_id`, `tm_id`, `tm_refl`, `tm_j`; 17 total). No K —
UIP, where wanted, is Hedberg's theorem territory, and a strict-Prop-style
alternative stays open (see the issue).

Second extension: **Σ-types** — `Σ^{l,l'}(x:S). T` with encoding
`Σ^{l,l'}(s; t) : Ty (l⊔l')` (decoded by `El (Σ …) ⇝ Σ (El …)`, mirroring
Π), intro `pair^{l,l'}(x:S.T; a; b)`, and **projections** `fst`/`snd` (not a
single match/split eliminator) with β `fst (pair a b) ⇝ a`, `snd … ⇝ b`.
The key design choice — projections **with η for pairs** rather than split —
follows the ch. 06 conversion structure consciously: `tm_nf` is
type-directed, so a `Type::Sigma` arm comparing `fst a ≈ fst b` and
`snd a ≈ snd b` mirrors the existing Π η arm exactly, giving definitional
surjective pairing (`p ≈ (fst p, snd p)`); a match eliminator is not
η-compatible and would diverge from Π's treatment. `fst`/`snd` are neutral
when their pair is (like `app`/`elim_Nat`/`J`), and compared structurally at
neutral result types. Fully annotated (like `App`) so they infer. The code
recursors gain five branches (`ty_sigma`, `tm_sigma`, `tm_pair`, `tm_fst`,
`tm_snd`; 22 total).

Explicitly out of v0: coinduction/effects, typeclasses, compiler machinery,
inductive types beyond Nat and Id, the type lifter (omitted by the paper
too).

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
  kernel does no implicit insertion and no elaboration. Every form except
  `box` synthesizes its canonical type/level from its annotations; checking
  = synthesize + conversion at `typeof(i)` + level `≈`, which is exactly
  where the two conversion rules fire. `box` (no Δ/l in the term, per the
  paper's syntax) is checking-only; checking descends structurally through
  the four function intro forms so boxed bodies still check. Known
  incompleteness, documented in `typing.rs`: a `box` in the body of an
  *immediately β-reduced* meta-function (e.g. `(Λ g. box Nat) @ Δ`) cannot
  be synthesized — elaborators must bind such code with `letbox` instead.
  The recursor telescopes live once in `rec.rs`, shared by conversion and
  typing. Fuel is granted per conversion call / per weak-head normalization
  (the checker's own recursion is structural, hence total without fuel).

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
