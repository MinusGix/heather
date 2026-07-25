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

Third extension: **Unit and Empty** — the two degenerate finite types.
`Unit` with encoding `Unit : Ty 0` (decoded by `El (Unit) ⇝ Unit`) and the
single intro `⟨⟩` (`Term::Triv`); **no eliminator** — instead `Unit` carries
definitional **η (proof irrelevance)**: a `Type::Unit` arm in `tm_nf` accepts
*any* two terms at `Unit` type, exactly mirroring the Σ-η choice (type-
directed, no new neutral head). `Empty` with encoding `Empty : Ty 0`
(`El (Empty) ⇝ Empty`), no intro, and a dependent eliminator
`elim_Empty^l(x. M; t) : M[t/x]` modeled on `elim_Nat` minus the base/step
branches: no β rule (no constructors), always neutral on a neutral
scrutinee, fully annotated so it infers. The code recursors gain six
branches (`ty_unit`, `ty_empty`, `tm_unit`, `tm_empty`, `tm_triv`,
`tm_elim_empty`; 28 total).

Fourth extension: **binary sums** — `A +^{l,l'} B` with encoding
`s +^{l,l'} t : Ty (l⊔l')` (decoded by `El (s + t) ⇝ El s + El t`, mirroring
Π/Σ), the two intros `inl^{l,l'}(A; B; a)` / `inr^{l,l'}(A; B; b)`, and a
**dependent** eliminator `case^{l,l',l''}(z. M; A; B; x. c_l; y. c_r; t) :
M[t/z]` with β `case (inl a) ⇝ c_l[a/x]`, `case (inr b) ⇝ c_r[b/y]`. Unlike
the negative Σ (projections + η), a sum is **positive**: `case` is neutral on
a neutral scrutinee (like `elim_Nat`), and conversion at `Type::Sum` matches
the two constructors like `Zero`/`Succ` at `Nat` (comparing the injected
value, tag mismatch = `NotConvertible`), *not* by η. `inl`/`inr` are fully
annotated (both summands + levels) so they synthesize, and `case` is
annotated like `elim_Nat` so it infers. The former is non-dependent — both
summands live in Γ, so the `Sum`/`TmSum`/`ty_sum`/`tm_sum` shapes drop the
Σ binder extension. The code recursors gain five branches (`ty_sum`,
`tm_sum`, `tm_inl`, `tm_inr`, `tm_case`; 33 total); `tm_case` is the widest
telescope (3 univs, 7 globals, 6 recursive calls).

Fifth extension: **W-types** — `W^{l,l'}(x : S). T` (shapes `S`, positions
`T`; `pos` binds one local, structurally ≡ Σ/Π) with encoding
`W (x : s). t : Ty (l⊔l')` (decoded by `El (W s t) ⇝ W (El s) (El t)`),
intro `sup^{l,l'}(x:S. T; a; f)` where `f : Π^{l',l⊔l'}(y : T[a/x]). W`
(fully annotated, synthesizes), and the dependent eliminator
`elim_W^{l,l',l''}(x:S. T; z. M; a f ih. s; t) : M[t/z]` where the step
binds three locals (`a : S`, `f : Π(y:T[a/x]). W`,
`ih : Π(y:T[a/x]). M[f y/z]`). **Positive** like sums: no η, `elim_W`
neutral on a neutral scrutinee, conversion at `Type::W` compares `sup`
labels and subtree functions (annotations forced by the type). The β rule
is the first whose right-hand side **synthesizes a λ**: `elim_W (sup a f) ⇝
s[a, f, (λy. elim_W … (f y))/ih]` — reduction builds the ih function around
the recursive call from the eliminator's own annotations. Motivation
(kernel-v1-extensions): general well-founded recursion (`Acc` via
`W (x:A) (Σ y, R y x)` + Id, funext discharging the indexed-containers
obligations) — the one thing the finitary encodings provably cannot reach.
The code recursors gain four branches (`ty_w`, `tm_w`, `tm_sup`,
`tm_elim_w`; 37 at the time, 45 today); `tm_elim_w`'s telescope
(3 univs, 6 globals, 5 recursive calls) nests Π types inside its global
bindings (the step's `f` and `ih` binders), the deepest binding-type
construction yet.

`Vec^l(T; k)` and `Fin(k)` (2026-07-25) are index-computing wrappers, not
new definitional power: `Vec(T;0) ⇝ Unit`, `Vec(T;S k) ⇝ Σ(_:T). Vec(T;k)`,
`Fin(0) ⇝ Empty`, `Fin(S k) ⇝ Unit + Fin(k)`, each **neutral at a neutral
length** and carrying no introduction/elimination forms of its own — every
η they appear to have (componentwise comparison, proof irrelevance at
length 0) is inherited through the reduction from `Σ`/`Unit`. The length is
a *term* at the same depth as the element, with no binder anywhere, which is
what lets a tuple's arity be computed from a datatype's tag. They are
phase-1 of the `Wf` former (`docs/wf-former-design.md`).

`Wf^l(x:S). n` (2026-07-25) is the finitary branching fixed point: shapes
`S`, arity a `Nat` **term** with the shape free, children a
`Vec^l(Wf; n[a/x])` — a tuple, not a function. `sup_f` introduces,
`elim_Wf` eliminates dependently with the step binding
`(a : S, cs : Vec(Wf; n[a/x]), ih : Π(i : Fin n[a/x]). M[nth … i/z])`, and β
synthesizes the ih λ around the recursive call like `elim_W`'s — but over a
`Fin` index, so the ih is *transient*: applied at literal indices after the
generated recursor cases on the tag, never stored and never compared. `nth`
is not a former; it is a fixed `elim_Nat` schema materialized by the rules
(`term::nth`), and the step telescope is built once in
`term::wf_step_telescope` and shared verbatim by `typing.rs` and `conv.rs`
so the two cannot drift. Positive, no η: conversion at `Wf` compares label
and children, and the children comparison happens *at a `Vec`*, so it
descends through Σ-η and bottoms out in `Unit`'s proof irrelevance. That is
the entire reason the former exists — the abstract constructor
`sup_f(tag; cs)` at a neutral `cs` is **convertible** with the concrete
`node (nth 2 cs 0) (nth 2 cs 1)`, which is the equation route A pays funext
for in every arm (`crates/kernel/tests/wf.rs`,
`crates/elab/tests/branching_route_a.rs`).

The **codes** for the group (2026-07-25, phase 3) are `TmVec`, `TmFin`,
`TmWf`, decoding as `El (Vec^l(s;k)) ⇝ Vec^l(El s; k)`,
`El (Fin k) ⇝ Fin k`, `El (Wf^l(x:s). n) ⇝ Wf^l(x : El s). n` — in each
case only the element/shape decodes, since the length and the arity are
`Nat` *terms* and ride across unchanged. With them the phase-1/2 layer-c
gate is gone: all three formers, `sup_f` and `elim_Wf` are code, and the
code recursors gain eight branches (`ty_vec`/`tm_vec`, `ty_fin`/`tm_fin`,
`ty_wf`/`tm_wf`, `tm_supf`, `tm_elim_wf`; **45 total**). Two asymmetries
with the `W` group are worth remembering: the `Vec`/`Wf` branches bind one
universe, not two (an arity term contributes no level), and their length /
arity recursive calls go at the **term** motive — so `ty_vec`/`ty_fin`/
`ty_wf` are type-motive branches whose innermost recursive-call entry is a
term-motive one. `tm_elim_wf`'s step binding reuses `term::wf_step_telescope`
verbatim, which is why the rec.rs, typing.rs and reduce.rs transcriptions of
it cannot drift.

Explicitly out of v0: coinduction/effects, typeclasses, compiler machinery,
inductive types beyond Nat, Id, Σ, Unit, Empty, binary sums, W, and the
`Vec`/`Fin`/`Wf` finitary-branching group, the type lifter (omitted by the
paper too).

## Algorithms

- **Conversion is ch. 06 verbatim**: untyped weak-head reduction to
  WHNF/neutral, then structural comparison. Not NbE, not typed reduction.
  Function-type comparison is η-directed (compare applications to a fresh
  variable); boxed types/terms compare by **syntactic equality**; recursors
  block on neutral scrutinees *and* on boxed global variables `□(U^δ)` /
  `□(u^δ)`; neutral comparison is an inference step that returns a type.
- **Level equivalence**: normalize to `adjust(count(l))` maps and compare;
  `ω` compares only to itself.
- **Propositional equality at `□` is exactly the recursor's observation.**
  `refl` *synthesizes* `Id(S; t; t)`, so checking it against `Id(S; a; b)`
  goes through conversion on the endpoints — and conversion at `□` types is
  syntactic equality. Hence `Id(□(Δ ⊢ T @ l); box t; box t')` is inhabited
  iff `t ≡ t'` as syntax, the same equality the code recursors dispatch on.
  This coincidence is what makes intensional code observation consistent
  with a propositional equality over code types (the ch. 07 argument in
  `docs/metatheory-ch07-extensions.md` §6); relaxing *either* half — a
  conversion that identifies β-convertible code, or an `Id` rule that
  bypasses endpoint conversion — breaks it. Treat both as invariants.
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
