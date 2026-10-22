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

Third extension: **Unit and Empty** — the two degenerate finite types,
**level-indexed**: `Unit^l : Type @ l` with encoding `Unit^l : Ty l` (decoded
by `El^l (Unit^l) ⇝ Unit^l`) and the single intro `⟨⟩^l` (`Term::Triv`);
**no eliminator** — instead `Unit^l` carries definitional **η (proof
irrelevance)**: a `Type::Unit` arm in `tm_nf` accepts *any* two terms at
`Unit^l` type, exactly mirroring the Σ-η choice (type-directed, no new
neutral head). `Empty^l` with encoding `Empty^l : Ty l`
(`El^l (Empty^l) ⇝ Empty^l`), no intro, and a dependent eliminator
`elim_Empty^{l,l'}(x. M; t) : M[t/x]` (two levels: the motive's and the
scrutinee's `Empty`) modeled on `elim_Nat` minus the base/step
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
new definitional power: `Vec^l(T;0) ⇝ Unit^l`, `Vec^l(T;S k) ⇝ Σ(_:T). Vec^l(T;k)`,
`Fin(0) ⇝ Empty^0`, `Fin(S k) ⇝ Unit^0 + Fin(k)`, each **neutral at a neutral
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
generated recursor cases on the tag, never stored and never compared. The
evaluator exploits exactly that (2026-09-26,
`issues/wf-ih-rebuilt-per-node.md`): it holds the ih as `Val::WfIh` — the
eliminator and the children it fired on — and applying it at a canonical
index over a canonical tuple fires the eliminator on the selected child
directly. Building the λ as syntax shifted the whole motive and step under
three binders, and the next β shifted that copy again, so each node of a
structural recursion allocated a fresh copy of the recursor and no memo keyed
on syntax identity hit twice; that was most of the gate time of list-heavy
proofs. A neutral index, a stuck tuple, or any reader that inspects the
function instead of applying it gets the λ built as before, so this is a
strategy change with no semantic content (tests/wf.rs pins both fallbacks). `nth`
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

`DVec^l(k; i. F)` (2026-10-17, `docs/iwf-former-design.md` §13 step 2) is
`Vec` with a per-position element type, the children substrate of `IWf`:
`DVec(0; i. F) ⇝ Unit^l`, `DVec(S k; i. F) ⇝ Σ(_ : F[inl ⟨⟩/i]).
DVec(k; j. F[inr j/i])`, the injections annotated by `Fin(S k)`'s reduct so
each instance is typed at the family's domain without a conversion. It
takes a binder (`i : Fin k`) rather than a family argument, since there are
no type-valued functions; that binder is the one new thing in the value
domain, where the head is the family's closure with `i` bound to `inl ⟨⟩`
(one environment cell) and the tail is `DVec` syntax over the family
rewritten at `inr j` (`Type::inst_top`), with the predecessor pushed onto
the environment because the `inr` annotation has to name it. It is neutral
at a neutral length and compared there structurally, the family under
`i : Fin k` at the left length. `Vec(T; k)` and `DVec(k; _. T)` agree reduct
for reduct at a canonical length and are distinct neutral types at a neutral
one: the two are siblings, not spellings of one type (design §10, option 1).
Its projection `dnth` is not a former: `term::dnth` materializes design §3's
`elim_Nat` schema over an embedding `Fin k̂ → Fin n`, transcribed binder by
binder from the Coq formalization (heather-coq `Term.v`), whose `V_dnth`
checked that the schema's β-annotated applications type (`tests/dvec.rs`
checks them here, at an open length). `DVec` has **no code yet**: it is
admitted at layers p and m only (`Tc::computing_layer`) until the rec.rs
round gives it `TmDVec` and its branches, as `Vec` was before its phase 3.

`IWf^{l,li}(I; x:S. n; x. o; x i. c)(m)` (2026-10-20,
`docs/iwf-former-design.md` §13 step 3) is `Wf` with an index: `sup_i(a;
cs)` is at its output index `o[a/x]`, its children a `DVec^{l ⊔ li}(n[a];
k. IWf(…)(c[a, k]))`, and nothing else is stored, so there is no equation,
no `transp` and no irrelevance arm. The family level is `l ⊔ li`.
`elim_IWf`'s motive binds the index and the scrutinee, its step `a, cs, ih`
with `ih : Π(i : Fin n[a]). M[c[a,i], dnth(…; cs; i)]`, and β fires at a
`sup_i` whatever the index (heather-coq `red_elimIWf_supi`): the headline,
β on open data at a computed index, is `tests/iwf.rs`. Every schema is
built once in `term.rs` around `IWfSig` (`iwf_children_ty`,
`iwf_step_telescope`, `iwf_ih`), which typing, both reducers and conversion
share. The signature is also how the six variants (`Type::IWf`,
`Term::Supi`, `Term::ElimIWf` and their values) carry it, behind one
pointer: flat, its two levels and five components made `Type` and `VTy` a
third larger and `Term` and `Elim` larger too, and since the checker's
recursion holds them in every frame, a 1000-deep constructor value
overflowed the 8 MiB stack (`size_tests`, and the value-size test, now pin
the four). The one new substitution operation is `inst_top_above`
(`t[s/x]` under the position binder that the child index keeps). The
evaluator's β takes the closures' syntax apart, as `DVec`'s tail does,
and builds the ih as a `Val::Lam` whose body is the eliminator at
`dnth(…; cs; i)`. Two values compare by their label (at the shape) and
their children (at the children's `DVec`, so Σ- and Unit-η come through
its reduct); the annotations are the type's. The neutral `elim_IWf` arm is
typed from the start: the motive's level, the motive in `(Γ, j : I, z :
IWf(…)(j))` and the step in the left telescope, then the scrutinees as
neutrals, whose inferred `IWf` forces the signature and the index.
It does not compare the ih types either: equal signatures and motives
force them (heather-coq `ELIM_CONGRUENCE.md`, `Validity/IWfIhEq.v`,
MinusGix/heather-coq#24). Like `DVec`, `IWf` has **no code yet** and is
admitted at layers p and m only until the rec.rs round.

`M^{l,l',li}(I; i. S; i s. P; i s p. o)(j)` (2026-10-21,
`docs/kernel-coinduction-design.md` §10 step 3) is the indexed
**coinductive** former, in Petersson–Synek form: a node at index `j` has a
shape `s : S[j]` and, for each position `p : P[j, s]`, a child at the
computed index `o[j, s, p]`. Nothing is stored and the family level is
`l ⊔ l' ⊔ li`. Its only eliminator is `out(…; j; m) : Σ(s : S[j]). Π(p).
M(o[j, s, p])`, neutral on a neutral `m`; its only introduction is
`corec^{k}(…; i. X; i x. c; j; x)`, an apomorphism: the step returns at
each position `X[o] + M(o)`, a new seed or an existing tree, so a
constructor is a `corec` at carrier `Unit` whose children all exit and
`out(in(s, f)) ≡ (s, f)` exactly (`tests/m.rs`). β is one step and only
under `out` (`out(corec) ⇝ (fst r, λp. case(snd r p; y. corec(…; o; y);
t. t))`, `r := c[j, x]`); there is **no η** and no rule unfolds a `corec`
anywhere else, so two `corec`s describing one tree, a `corec` and a
neutral, and `t` and `in(out t)` are all distinct. Every schema
(`m_out_ty`, `m_step_ty`, `m_out_corec`) is built once in `term.rs` around
`MSig`, which the six variants carry behind one pointer, as `IWf`'s do.
The rewriter duplicates `r` in the reduct; the evaluator's β rebuilds the
reduct as syntax in `(Γ, j, x)` and evaluates it in the coalgebra's own
environment (`VCorec`, which a `Val::Corec` carries so the step's syntax
can be read back) extended by the index and the seed, so `r` is one
closure the two projections share. Conversion compares `M` types
structurally, two `corec`s by their coalgebras (the carrier's level, the
carrier in `(Γ, i)`, the step in `(Γ, i, x)` at the left one's step type,
the seed at `X[j]`; the signature and index are the type's), a `corec`
against anything else as not convertible, and two `out`s by their
scrutinees alone, whose inferred `M` forces the rest. `M` has **no code
yet** and is admitted at layers p and m only. Its metatheory
(heather-coq, design §9 Q1–Q3) has not been checked yet.

`sEq^l(I; a; b)` (2026-07-28) is **strict equality** — `Id` minus proof
relevance plus strictness, the SProp round's customer former
(`docs/sprop-design.md`; the sort itself dissolved into per-former
irrelevance arms, design doc §1). Three conversion behaviours are its
whole content: an irrelevance arm at `Type::SEq` in `tm_nf` (`Unit`'s
audited pattern — any two proofs convertible, so UIP is definitional and
`sJ` is derivable rather than primitive); the **strip rule** in `Conv::tm`'s
term-whnf stage (`Conv::strip`) — a stuck `transp^{l,l'}(I; x.P; a; b; e; t)`
whose endpoints convert is replaced by its payload, which is what makes
casts invisible on *open* data (`plus0(n) ≡ n` under a neutral proof) and
is term-head-keyed, unlike the type-keyed η family, hence its placement;
and an endpoint-keyed congruence in `tm_ne` that compares `I, P, a, b, t`
typed and deliberately skips the proofs — the inversion of `J`'s
discipline (J's proof is its scrutinee; transp's stuckness is keyed on the
endpoints). Reduction gets ordinary β only (`transp(…; srefl; t) ⇝ t`,
J's shape; canonicity makes it sufficient closed) — the strip is
conversion's, preserving the reduce/conv separation. Guard semantics
(settled against `Conv`'s fuel-only state): catch `NotConvertible`,
propagate `OutOfFuel`, no refund, each strip pays `spend()`. The hot-path
discriminant check lives inline in `tm` because a whnf-wrapping helper
cost 1.35× on `conv/computed-numeral` (caught by `scripts/bench --check`).
The codes landed same-day (`TmSEq`/`TmSEmpty`, decoding as
`El (sEq^l(s;t;u)) ⇝ sEq^l(El s; t; u)` and `El (sEmpty^l) ⇝ sEmpty^l`),
and the code recursors gained seven branches (`ty_seq`/`tm_seq` mirror
`ty_id`/`tm_id`; `ty_sempty`/`tm_sempty`/`tm_elim_sempty` mirror the
Empty trio; `tm_srefl` mirrors `tm_refl`; `tm_transp` is `tm_j` with the
motive over one binder, globals in `Transp` field order, and the proof
recursed like any subterm — irrelevance is a conversion fact, code is
syntax; **52 total**), so the phase gate is gone. A stuck transp inside a
box round-trips the identity recursor *as syntax*: neither the strip nor
irrelevance reaches through `□`, the same firewall as ever. Independent
implementation evidence for the strip-in-conversion placement: the TYPES
2024 CCobs implementation (design doc §1 note). Its companion `sEmpty^l` (same day) is `Empty` made irrelevant as a
*separate* former — `Empty`'s structural-neutral comparison is unchanged,
and the contrast is pinned in tests — with `elim_sEmpty` eliminating
anywhere (no β, neutral congruence skips the scrutinees) and the same
layer gate.

One invariant carries both equality observers over codes (2026-08-03, the
ch. 07 FT pass, `docs/metatheory-ch07-extensions.md` §20.6): **endpoints
are checked by conversion, and conversion at `□` is syntactic `==` modulo
level equivalence.** `Id` at `Ty l` (propositional) and `sEq(Ty l)`
(definitional, irrelevant) both observe exactly what that comparison
distinguishes — irrelevance collapses *proofs*, never endpoints — so
neither can widen type equality, and a change to boxed-code comparison is
a change to both observers at once, not a local tweak.

**Global definitions with layer-indexed transparency** (2026-07-31,
issues/simulate-conversion-cost.md) are the only extension so far that is not
a type former. A `u : Trm_i(Δ ⊢ T @ l)` binding may carry a **body**
(`GlobalBinding::Tm`'s `body: Option<Rc<Term>>`), making it a definition
`u := t`. DeLaM has no definitional bindings to extend — ch. 04's global
grammar is declarations only, and `letbox` is code *composition* that
substitutes eagerly and leaves nothing resident — so every rule here is ours.

Three choices carry the design:

- **A field, not a fourth binding form.** A definition is a declaration that
  additionally knows its term, so every ch. 04 rule mentioning `u : Trm_i(…)`
  stays valid verbatim and no existing match arm changes meaning; only δ
  consults `body`.
- **Transparency is indexed by the layer, not by the binding.** The body
  unfolds during whnf/conversion at the computing layers p/m
  (`reduce::Defs::transparent`) and never at c (`Defs::opaque`), where a
  global is *syntax*: ch. 06 blocks the code-recursion principles on global
  variables and compares boxed globals syntactically, so a conversion that
  identified `box(u)` with `box(t)` while the recursor distinguished them
  would break coherence. Structurally this holds because reduction never
  enters a `box` and boxed code compares with `==`; `tests/definitions.rs`
  pins it anyway, in both directions.
- **The body is checked at the binding's own layer** (`i ∈ {c, p}`; a
  definition at layer v is rejected, since v admits no term but a variable).
  That is what makes δ layer-preserving: unfolding `u` at any layer `j ≥ i`
  can only produce a term that was already legal at `j`.
- **Term bindings at p** (2026-10-22, `docs/codata-elaborator-design.md`
  §6), past ch. 04's `{v, c}`: the program-only formers (`M`, `IWf`, `DVec`)
  have no codes, so a definition over them can only be stated and checked at
  p. A reference already requires `i ≤` the use site's layer, so a p binding
  never appears at c: not in a box, and not in a scrutinee of the code
  recursor. δ inlines it away, so the extension is conservative. The
  elaborator binds at p only the declarations that need it.

Conversion is **δ-lazy**: weak-head-reduce without δ first, and when both
sides stop at the same defined head, compare their spines before unfolding
anything — `f a⃗ ≈ f a⃗` never materializes `f`. A failed attempt falls
through to unfolding, with `Conv::strip`'s guard semantics (catch
`NotConvertible`, propagate `OutOfFuel`, no refund). The whole stage is
gated on Ψ actually holding a definition, because paying for its second
whnf pass unconditionally cost 1.35–1.43× on the conversion fixtures. The
value domain implements this order with glued neutrals rather than by
walking syntax for the head — see the conversion bullets under *Algorithms*.

Three refinements (2026-09-07, `issues/bitvec-ofnat-large-literals.md`).
When both sides stop at the *same* defined head as **bare applications**
`f a⃗`, `f b⃗` and the spine comparison fails, both are unfolded to their
δ-heads before comparing again: the meet at this head has already failed,
and single-stepping one side re-evaluates the exposed body on every round
with every closure beneath it fresh, so nothing below is ever shared — two
`ofNat(8, k)` at different `k` exhausted the budget that way. A meet at a
sub-term is still found by the lazy comparison of the canonical forms'
components. When either side is instead an *elimination* stuck on a glued
scrutinee, `E[f a⃗]`, the shared head is only what that scrutinee computes
with and the failed meet may be `E`'s against the other side's, which says
nothing about where the terms meet; both sides then take one δ-step and the
loop looks again (2026-09-18, `issues/utf8-decode-conversion-blowup.md`:
normalizing both there unrolled `nat::leb(0x800, code)` at a stuck `code`
into a 2048-deep closure chain on each side, past the native depth budget,
where the lockstep meets at the glued `leb` spine). `Conv::tm` memoizes its
verdicts per closure pair (address, scope, Ψ length, layer): convertible or
definitely not, never exhaustion; it carries the repeated sub-comparisons
of the same closures (~30% of the x86 model's load). And the evaluator's
run-accelerated Nat folds — every fold whose step classifies as an affine
or synchronous algebra (the policy paragraph below) — unfold a *glued*
scrutinee (or right-hand counter) themselves instead of stalling as a
spine for conversion to δ-step from outside, which replays the pending
spine each time. General
matches do not, under opaque evaluation: the x86 decoder's open-argument
unfolding theorems meet at a folded `match decode_opcode_direct(…)`, and
unfolding it eagerly exhausts fuel on the dispatch it hides.

A fourth (2026-09-07, `issues/bitvec-closed-reduction-cost.md`): **a side
with no defined head to meet unfolds transparently.** When one side of a
term comparison is δ-stuck and the other has no defined head (a canonical
form, or a neutral at a variable), no rendezvous at a definition is
possible, and the stuck side's single steps continue until it has no
defined head either — the same unfoldings, in the same order, charged the
same fuel. They now run as one `Eval::delta_whnf` in **transparent** mode:
while it is set, an eliminator stuck on a glued scrutinee unfolds the
scrutinee in place instead of stalling as a spine. Applications still
extend the spine, so `f a⃗` keeps its glued shape and the outer loop
unfolds it. Driving the same unfoldings from outside had replayed the
whole pending spine per step — a structural consumer (`sign_bit`,
`toNat`, a second ripple) over a computed width-64 producer was cubic in
the width, then exponential once the replays' throwaway memos evicted the
shared ones from the bounded cache: 3.8M closures and 2.1 GB for one
`sign_bit` of a ripple sum, against 34K and the module baseline now.
Same-head spine comparison and the newer-head single step are unchanged,
so the decoder rendezvous is untouched; a memo written transparently can
later answer an opaque single step with more than one step, which can
only cost a rendezvous, never a verdict.

**Acceleration policy** (`issues/kernel-acceleration-policy.md`). Three
kinds of acceleration are distinguished, and only the first two grow:
*representation changes with an adequacy argument* (saturated runs — the
same values, the same relation up to bisimulation, generic over the type)
and *strategy changes with no semantic content* (everything in the δ-lazy
paragraphs above — the same unfoldings, the same fuel, checked by the
differential oracle). The third, *pattern-matching on a definition's
spelling*, was retired on 2026-09-09
(`issues/nat-run-algebra-primitives.md`): a `Nat` fold's step is now
**classified by evaluating it** on fresh neutral variables (`eval/probe.rs`)
into an affine tree of successors and projections, a synchronous
two-counter algebra, or opaque, and the first two are iterated over the
run's program by the arithmetic in `value/algebra.rs` (`eval/runs.rs`).
The class is a fact about the algebra as a function on runs — the
substitution property of reduction is the adequacy argument: a probe value
with no case split on the probe variables was reached by a reduction that
holds at every instantiation — so `mul` of two runs is one multiplication,
`sub`/`leb`/`min`/`max` cancel run against run however they are spelled,
and `half`'s course-of-values window is a permutation iterated by
exponentiation. A cost the calculus itself charges that no class covers
(`div`'s state machine, an `Int`-valued fold) is answered in the library
by a definition whose reduction cost matches its meaning, or by
reflection, never by a kernel case for that definition — and what is not
accelerated is refused with `OutOfFuel`, never a process abort.

**Numerals of any size** (2026-09-26, `docs/wide-numerals-design.md`).
`Term::NatLit` is a compact spelling of `Succ^n(Zero)` whose one-step view
is `Succ(NatLit(n - 1))`; it carries a `heather_numeral::Numeral`, an
arbitrary-precision natural, rather than a `u64`. Evaluation builds a
literal past `u64::MAX` as a shared run program from its bits
(`ContextProgram::of_count`), the shape arithmetic that overflows a run
already produces. A composed program carries its length as a `Numeral` and
the one context it repeats, when it repeats one (2026-10-22,
`issues/kernel-wide-run-comparison.md`): two numbers cancel by subtracting
lengths and cutting the longer along one path, `O(bits)` however each was
built, and an iterated fold's result is rebuilt in the literal shape when
its graph outgrows two nodes per bit. The numeral crate is first-party,
dependency-free and `unsafe`-free; what the kernel's judgments rely on from
it is `is_zero`, `pred`, `limbs`, its order, and the limb arithmetic
`value/program.rs` does over `limbs` (`issues/dependency-policy.md`).

**Native bitvector values** (`issues/kernel-native-bitvector-values.md`,
`docs/native-bitvector-values-design.md`). The second representation change
of the runs kind. A `Vec^l(T; n)` whose element type `T` has exactly two
canonical inhabitants with proof-irrelevant payloads — which is what a
tier-0 two-constructor nullary inductive lowers to; a payload is `Unit`,
an `sEq` at one closed literal on both sides (the nominal tag,
`docs/inductive-tier0-lowering.md` §3.3), or a Σ of those — has canonical values
that are right-nested Σ-pairs of injections, one pair node and one injection
per bit. `Val::BitRun` holds a closed prefix of such a chain as a machine
word: an element type, a width, `u64` bits, and a tail, standing for the
Σ-chain that unpacks from it one bit at a time with the annotations the
`Vec` type rule itself produces. It is `Val::NatRun` for a different former:
the same closed-prefix-over-a-tail shape, the same virtual predecessor on
the way out, and the same generality — nothing in it names a library type or
definition.

Adequacy is bisimulation, in two parts. *Values mean the same*: a word
unpacks to the pair the `Vec` rule builds, with the element type's own
injections and their canonical payloads, so every consumer that matched on
`Pair` sees what it saw before; a bit whose payload is not canonical does not
pack. *Reduction is unchanged*: a fold over a **width** — which is what every
bitvector operation is, `elim_Nat` whose motive at `Succ k` is a function
type over vectors — is classified (`eval/transduce.rs`) as a **bit
transducer** when, at every combination of closed head bits and of a finitely
enumerable state, one application of its step reduces to `cons(closed bit,
ih(tails, closed state))` with the tails reached by projection paths of
neutral probe variables. Such a fold is iterated over the word instead of
being taken one bit at a time. The neutral tails are the substitution
property, as in the `Nat` classes: a probe value with no stuck case split on
them was reached by a reduction that holds at every instantiation. The bits
and the state are not an argument at all but a truth table, exhaustive
because both types are finite. Consumers into `Nat`/`Bool` are the same
machine with a different output algebra — a finite value, or a run
endomorphism `ih ↦ q·ih + r`, which is the affine tree with a scale. The
argument modes come from the eliminator's **motive**, never from a
definition's spelling; the library's vectors sit inside a record, so a
peeled argument is a `Vec` in a unit-like Σ-context and the class carries the
projection path to it.

Conversion compares two vectors over such an element type by their words,
before Σ-η, packing a structural side by the `fst`/`snd` η would have taken;
a side that is two stuck spines is left to the neutral-first guard, and a
difference settles the comparison at the bit it appears on. Native steps
charge one fuel unit per bit, which is strictly less than the structural path
spent, so no verdict that fuel allowed becomes a refusal. What does not
classify — an open `Fin` index, a recursion on a shift count, a state type
above the cap — folds exactly as it does today, and what does not meet the
criterion — an element type with a payload of its own, an open width, a chain
that stops being a Σ — is compared exactly as it is today.

Owed to ch. 07: the logical relation interprets a bodied `u` at p by its
body (definitional glueing) and at c as a neutral, and the fundamental
theorem's `u`-cases redo under that split — see
`docs/metatheory-ch07-extensions.md` §11.

**Every type has exactly one level, and this is load-bearing** (2026-07-25,
phase 4). Not tidiness: DeLaM ch. 04 §Non-cumulativity turns on it, because
the code eliminator must reconstruct code from its components per branch,
which is only expressible when each term has a unique type. `box T` is
checking-only and checks `T` at the level in its `□`-type, so **a type
checking at two levels is a term with two types**, and `rec.rs`'s branch
telescopes are built against uniqueness (`ty_ty` binds a universe because
`Ty ℓ`'s level varies; `ty_nat`/`ty_unit` bind none because theirs do not).

The live consequence: **`Vec^l(T; 0) ⇝ Unit` drops the level**, so type-level
preservation (ch. 06's *Preservation* lemma, at the same `l`) fails for
`l ≠ 0` — a well-formed `Π^{1,0}(_ : Vec^1(T;0)). Nat` steps to an ill-formed
`Π^{1,0}(_ : Unit). Nat`. `Vec` is the first type former whose whnf is chosen
by a *term*; `El` is chosen by a term too, but its term is a code carrying
its own level, so `El` cannot drop one, while `Vec`'s bare `Nat` length can.

Making `Unit`/`Empty` level-polymorphic fixes that in one line and is
**wrong** — it was landed and reverted the same day, because it gives
`box Unit` a type at every level and breaks the code recursor's preservation.
The favoured repair is level-*indexed* `Unit^l`/`Empty^l`, turning
`ty_unit`/`ty_empty` into copies of `ty_ty`. Open, with measurements and
three costed candidates: `issues/unit-level-and-vec-preservation.md`;
LR consequences in `docs/metatheory-ch07-extensions.md` §10.3.

Explicitly out of v0: coinduction/effects, typeclasses, compiler machinery,
inductive types beyond Nat, Id, Σ, Unit, Empty, binary sums, W, and the
`Vec`/`Fin`/`Wf` finitary-branching group, the type lifter (omitted by the
paper too).

## Algorithms

- **Conversion decides ch. 06's relation** *plus δ*: weak-head reduction to
  WHNF/neutral, then structural comparison, still untyped and still not
  typed reduction. The one addition is definition unfolding, which is
  layer-indexed and δ-lazy — see the global-definitions extension above.
  Function-type comparison is η-directed (compare applications to a fresh
  variable); boxed types/terms compare by **syntactic equality**; recursors
  block on neutral scrutinees *and* on boxed global variables `□(U^δ)` /
  `□(u^δ)`; neutral comparison is an inference step that returns a type.
  **Application and projection are typed** (2026-09-06): two neutral
  `app`s / `fst`s / `snd`s compare their heads, read the Π / Σ the heads
  *infer* (fully δ-reduced, then driven to its former through
  `Conv::delta_to_head_ty`), and compare the argument at that domain; the
  stored `x:S.T` / Σ annotations are never related to each other. This is
  the mirror image of ch. 06's own note, which compares the annotations and
  ignores the inferred type "because ν, ν' are well-typed so the annotations
  must be equivalent" — on the well-typed inputs conversion presupposes the
  two are interderivable, and the paper's choice costs the size of the
  remaining Π/Σ at every node of a spine (a 15-ary theorem application
  compared 15 codomain suffixes, each recursing into its own neutral
  domains; a Wf record's children tuple did the same through its `snd`
  chain). At Σ types, two neutrals try their spines before η-expanding
  (`Conv::tm_nf`'s Σ arm): η on two neutral 64-bit vectors was quadratic
  in the length, and a failed spine attempt still falls through to η.
  **The eliminators are typed too** (2026-10-20,
  `issues/conversion-typed-eliminator-congruence.md`): two neutral `case`s,
  `elim_W`s, `elim_Wf`s and `J`s compare the motive's level, the motive,
  the branches and then their scrutinees (last, as before: comparing the
  scrutinees first ran a function_ir certificate out of fuel), and
  never what the
  scrutinee's type forces — `case`'s and `elim_W`'s `A`/`B`, `elim_Wf`'s
  shape and arity, `J`'s `A`/`a`/`u`, their levels included. The motive and
  branches are compared in the *left* elimination's stored telescope, which
  converts with the scrutinee's inferred one, so no type is read off the
  scrutinee. heather-coq checked exactly this rule (`ELIM_CONGRUENCE.md`:
  soundness, completeness and decidability of the algorithm with these
  premises, no axioms). On a Wf-lowered inductive the skipped shape is the
  sum-of-Σs, the size of the declaration, at every meeting of two matches.
  `elim_IWf`'s arm was written the same way when it landed, its induction
  hypotheses' types skipped as well (heather-coq#24). `elim_Nat` had
  nothing forced to drop; `transp` has no scrutinee (its proof is
  irrelevant), so it still compares every annotation.
- **Typing a spine is one walk** (2026-09-26,
  `issues/application-spine-substitution-cost.md`): `app@(…app@(f; a₁)…; aₖ)`
  holds the arguments while `f`'s type stays a syntactic Π telescope, checks
  each `aᵢ` at its domain under `a₁…aᵢ₋₁` substituted at once, and
  instantiates the codomain once (`Tc::app_at_spine`). Node by node, each
  `T[a/x]` copied the rest of the telescope with every earlier argument in
  it, once per mention — quadratic in a many-argument lemma's arguments.
  Simultaneous and one-at-a-time substitution spell the same syntax, so the
  inferred type is the rule's own; a Π that needs reduction, and every node
  while checked spellings are recorded, is typed alone as before. The
  elaborator's `apply_explicit` walks the same way. Likewise **an identity
  reference into its own context** (`Tc::subst_ck`): `u^{id_Γ}` checked in
  Γ, where `u`'s context *is* Γ, holds for a well-formed Γ without
  instantiating each entry by a prefix of the identity — a lifted proof or
  named value referenced where it was made had paid that, quadratic in the
  context, per reference. Both are strategies, deciding the same judgement.
- **Its reduction engine is an environment machine over a value domain**
  (`src/value.rs`, `src/eval.rs`; `docs/nbe-conversion-design.md`), not a
  term rewriter — adopted 2026-07-31 to kill the exponential of
  `issues/whnf-sharing-term-growth.md`, where an eliminator's β materialized
  a physical copy of its branch bundle and nesting multiplied the copies.
  β now extends an environment. Still not NbE: there is **no readback** and
  no normal form, because comparison is all the kernel ever wanted from
  reduction.

  Read the previous bullet and this one together: **"verbatim" has moved
  from the algorithm to the specification.** `reduce.rs` remains ch. 06's
  relation transcribed rule for rule, it is still typing's whnf, and it is
  what the machine is measured against. That is a real weakening of the
  trusted-base story and is stated as one; the compensating controls are the
  differential oracle (`conv::oracle` — the same comparison arms
  instantiated at the rewriter, run against the machine verdict for verdict
  over `tests/conv_differential.rs` and `tests/eval_differential.rs`), the
  adequacy statement (`docs/ch05-06-lemma-audit.md`, ch. 06), and the fact
  that the declarative system did not move at all.
- **The Dom boundary.** The comparison arms never name a weak head normal
  form: they reach their inputs through the `conv::dom::Dom` accessor trait
  (head views with typed children, plus the operations with no common
  syntax — instantiation, the η arms, the synthesized formers), and the
  arms are instantiated twice, at `dom::values::Values` and at `dom::Syn`.
  This is what makes the oracle the *same algorithm* rather than a second
  one, and what made the migration an instantiation rather than a rewrite.
  Two invariants live on it: **views are total** (they inspect a form that
  is already whnf and reduce nothing), and **everything that reaches a head
  is fallible**, because at values reaching a child is a `force` and forcing
  spends fuel.
- **Sub-structures are lazy.** A value's children are closures
  (environment + syntax), forced only where a ch. 06 rule forces —
  a scrutinee, a `Vec`/`Fin` length, an `El` encoding. A strict domain would
  agree on every value and still evaluate an induction hypothesis nothing
  reads, which is precisely the workload the round exists to fix.
- **Shared syntax and scoped closure identity are reflexivity.** Before
  forcing two type or term children, conversion accepts them when they carry
  the same `home`/`sat` scope metadata and either the same closure pointer
  or — for syntactic closures — the same environment spine (head-pointer
  identity) with α-equal (`==`) bodies. In the one ambient environment
  passed to the judgment, those equalities make `open_ty` or `open_tm`
  produce identical syntax, so this is syntactic reflexivity and not a new
  conversion rule: evaluation is a function of the (environment, body) pair.
  The scope pair is load-bearing: one closure read with different pending
  binders need not denote the same object. The syntax oracle takes the
  corresponding pointer-identity shortcuts. At public roots, type conversion
  accepts the same borrowed `Type` object or a syntactically equal (`==`)
  copy before whnf — the typing seam's expected-vs-inferred query mostly
  compares two separately built copies of one type, and on large canonical
  values the structural walk paid orders of magnitude over `==`
  (issues/conversion-cost-at-large-values.md); a failed `==` stops at the
  first difference. Raw term roots deliberately take no such check, because
  measurement (re-confirmed 2026-08-14) still finds no hits there. Context
  conversion likewise accepts syntactically identical contexts before its
  judgmental walk; `CtxEntries` makes the common shared-spine test O(1).
  Every hit still spends the comparison node's one fuel unit. These shortcuts
  preserve the □ syntactic-equality rule and Id-at-□ coincidence: each hit
  implies identical syntax (directly, or via an identical environment), and
  identical syntax implies both equality-as-code and entrywise conversion.
- **δ is glued.** A `u^δ` evaluates to a neutral carrying a memoized
  `unfold` thunk, `Some` exactly when Ψ defines `u`. The δ-lazy order is
  unchanged — compare without forcing the thunks, and on `NotConvertible`
  at a shared defined head force both and retry — but the head test is now
  O(1) instead of a spine walk, and a second visit to the same unfolding is
  free. The `has_defs` gate survives. The rescoping `shift_global(v + 1)`
  that every unfold used to recompute is memoized per `GlobalVar` in a
  `reduce::GlobalCache` owned beside the Ψ it belongs to (7.8% of a routine
  `heather check lib/ir_v1.hthr`) — and on the **value** path is not
  performed at all: the machine evaluates the body *as stored*, under a
  global-index offset carried by the closure's environment, so a definition
  is read rather than copied however many gate calls unfold it
  (`docs/lazy-global-offset-design.md`, `issues/refl-theorem-step-cost.md`).
  The offset is always at cutoff 0 because a closure body under a global
  binder is built with its offset already spent, which is also what keeps
  the eager things — a `box`'s payload, a `ctx`, a recursor table, the
  rewriter's own δ — on one side of every β. The closure's identity includes
  the offset, so two readings of one body at two Ψ depths are two objects to
  every memo. The **signature** side of `u^δ` shares that cache: the
  `u^δ`/`U^δ` rules of conversion and of the syntactic checker read the
  binding's declared Δ, and at a term binding its declared type, rescoped into
  the ambient Ψ — the same `shift_global(v + 1)`, and likewise a function of
  the index alone — so `GlobalCache` memoizes it per `GlobalVar` beside the
  body. Both halves are rebuilt by `push_tele`, the one operation that makes
  an index denote a different binding; an entry that survived it would answer
  about the wrong binding, which is why the rebuild is a soundness condition
  and not a cache policy.
- **Fuel is unchanged in meaning and shared.** One budget pays for both
  reduction steps and comparison nodes, so the checker stays total on
  ill-typed input; the evaluator spends from the checker's account and hands
  back the remainder. Two consequences the machine forced. The machine's
  tail positions run in a **trampoline** (`Eval::drive`): written as native
  recursion, stack depth would be proportional to the *number of reduction
  steps* rather than the term's depth, so a divergent term would abort the
  process where the rewriter returned `OutOfFuel` — and a SIGABRT is not a
  verdict. Non-tail recursion (a scrutinee, an application's function) stays
  native, where its depth is the syntax's. And fuel thresholds are asserted
  as **invariants, never as a cost model**: a budget that answers must agree
  with the answer full budget gives.
- **A depth budget beside the fuel**, on the same policy
  (`reduce::NATIVE_DEPTH_LIMIT`, docs/native-depth-budget-design.md). "Its
  depth is the syntax's" is true of a term and false of a *value* that nests
  scrutinees: forcing the head bit of an iterated increment re-enters
  `Eval::drive` once per unit of the count, from shallow syntax, and the fuel
  is spent on the way back out — so the machine went deep first and aborted.
  Live `drive` re-entries and live `Conv::tm`/`Conv::ty` nodes are counted
  against one bound, shared the way fuel is because they interleave on one
  native stack (`Eval::reserve_depth`). Exceeding it is `OutOfFuel`; the bound
  is a fraction of what the 8 MiB rail measurably holds, so the frames the
  counter does not see have room.
- **A conversion owns one arena-backed value graph.** Rust's ordinary `Rc`
  destruction recursively follows a unique child. Evaluator thunks made that
  ownership path proportional to the forced computation even though
  `Eval::drive` keeps evaluation itself off the native stack; a closed
  machine-width carry first exposed a post-evaluation stack overflow at only
  8,496 spent fuel units. Environments and term/type closures are therefore
  allocated in a query-local `ValueArena`, and semantic edges to them are
  borrowed pointers. Releasing a query walks the arena's flat chunks instead
  of recursively following the value graph. Memo payloads remain `Rc` for
  shared values, but values point back into the arena rather than owning the
  next closure, so they no longer form the recursive destruction chain. This
  also removes the evaluator's former thread-local destruction worklist.
  Successful thunk results live in bounded FIFO caches owned by the arena
  (64K term values and 64K type values; 16K until 2026-09-07, when a
  width-64 structural consumer's working set measured ≈20K values and the
  FIFO's evictions of shared carries turned its cost from linear to
  thrashing — a cache entry retains one `Rc` value, so the bound is a
  retention bound, not a working-set claim). Consumers share a cached value, but
  eviction reclaims old forced payloads while their stable closure skeletons
  remain. (Unbounded strong memos made the first arena version exceed the
  4 GiB test cap on `lib_std_bitvec`; per-node weak memos still retained every
  dead `Rc` allocation through its control block.) Conversion and the
  definition-body cache are unchanged; a force after eviction may spend fuel
  again, which affects cost thresholds but never a verdict.
  Plain first-in first-out was wrong for two kinds of term value
  (2026-10-22, `issues/computed-argument-reevaluated-in-rounding.md`: a
  binary32 rounding of `1/3` ran its long division about ten times and out
  of fuel, where an unbounded cache checks it in a fraction of the fuel). A
  value whose force spent at least `COSTLY_FORCE` fuel goes to a **second
  tier** with its own bound, which cheap entries never push out; each entry
  there stands for that much fuel spent, so at worst the bound doubles. And
  a **glued neutral** is cheap to force but is the only path to its
  unfolding, a closure that evaluation made: once evicted (often while that
  unfolding was still being forced, its own thunks doing the pushing), the
  next force of the same closure made a fresh neutral glued to a fresh
  unfolding, and the work behind the first was unreachable. So an evicted
  glued neutral leaves its unfolding as a **tomb** keyed by its closure
  (bounded, two pointers each), and that closure's next force is glued to
  the old unfolding (`ValueArena::reglue`). This is sharing by closure
  identity, the same argument as the memo itself: a closure forced again
  denotes what it denoted, so the unfolding of its first value is the
  unfolding of its next, and the head and spine are the new force's own.
  Fuel only.
  Hot handles are kept compact: an environment closure captures only its
  persistent head and length, while whichever machine extends it supplies the
  already-owned query arena explicitly. Persistent cells remain two pointers.
  Universe levels on the uncommon synthesized `Vec`/`El` type closures live
  in the same arena rather than determining the size of every closure. On
  64-bit targets direct tests pin `Env`/`EnvNode` at 16 bytes and both term and
  type closures at 32 bytes.
- **Value-machine instrumentation is explicit and observational.** A caller
  may lend a `ValueMetrics` collector to arenas directly, or use the profiled
  typing entry points to aggregate the many conversion arenas created by one
  kernel gate. It counts region/environment/closure allocation plus cache
  lookups, hits, inserts, evictions and per-region peak residency. Ordinary
  arenas carry no collector. There is deliberately no global or thread-local
  sink: concurrent checks cannot contaminate one another's measurements, and
  enabling counters cannot change fuel, cache policy, or a verdict.
- **Level equivalence**: normalize to `adjust(count(l))` maps and compare;
  `ω` compares only to itself. `equiv`/`le` take a **reflexivity pre-check**
  first — identical syntax is equivalent because normalization is a function,
  so the pre-check can only answer sooner, never differently, and a miss
  falls through to the full decision. It is not an optimization of the
  decision procedure but a shortcut *around* it, so nothing about
  `adjust`/`count` (in particular the dominated-constant rule `n + ℓ ⊒ n`)
  may be weakened to make it fire more often.
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
  The typing seam handles syntactic reflexivity directly, preserving
  conversion's one-unit zero-fuel boundary without allocating a value arena.
  One public checking gate also retains a positive memo for repeated
  **cross-head** type-conversion judgments. A hit requires the same Ψ object,
  structurally equal Γ, layer, universe count, level, expected type, and
  inferred type; shallow allocation identities only partition candidates and
  never authorize a hit. Identity keys own the `Rc`s they identify, so an
  address cannot be reused while its key exists. The address is observed only
  transiently while hashing a live `Rc`, never stored as a bare pointer;
  failures are not cached, buckets hold at most four exact judgments, and the
  gate holds at most 4096. The restriction and bounds are performance safety
  rails: broad same-head memoization made mostly-distinct nested inference pay
  for large linear candidate scans. Fuel is constant across a gate, and only
  a judgment already proved successful at that fuel is reused, so the memo
  changes work but not the kernel verdict.

## Representation

- **de Bruijn indices, three independent namespaces**: local variables
  (into Γ), global variables (into Ψ — one index space covering all three
  binding forms), universe variables (into L). A binder never shifts the
  other two namespaces' indices. All names in the tex are display-only.
- **Separate `Type` and `Term` enums**, mutually recursive, mirroring the
  Tarski split. Judgment functions will be similarly mutual.
- `Rc` for sub-terms (substitution clones aggressively; sharing keeps that
  cheap; no interior mutability anywhere *in the terms* — which is exactly
  what makes the bounds memo below sound). **`Rc` is `std::sync::Arc` under
  an alias** since 2026-09-11: every workspace file spells
  `use std::sync::Arc as Rc;`. The serial tax was measured first, as the
  control the decision turned on (1.04× bench median, +2% at module scale,
  1.20–1.28× on the refcount-dense nat micro-steps;
  `issues/kernel-arena-terms-frozen-prefix.md`). A mechanical rename to
  `Arc` is a later diff-hygiene follow-up, not a design question.
- **Per-node free-local-variable bounds** (2026-07-31,
  issues/subst-visits-closed-subtrees.md route B): the local-namespace
  traversals skip subtrees that provably cannot change (loose de Bruijn
  bound ≤ depth, no substitution tail in scope) in O(1) instead of walking
  them. Deliberately *not* a field on the node — that would make the flag an
  invariant of every construction site in kernel and elab. Instead
  `src/bounds.rs` computes it as a memoized pure function of the immutable
  subtree, keyed by `Rc` address with a keep-alive clone (sound because
  terms are immutable and the entry pins the allocation). The one drift
  hazard — its binder counts vs. `subst.rs`'s dep table — is covered by a
  debug assertion at every skip site that re-runs the real traversal, under
  the 300-seed law suite.

  **Kept, re-measured after the value domain** (2026-07-31). The NbE round
  predicted that conversion's 21% of the deep-path profile would *leave*
  rather than shrink, taking the machinery's main customer with it, and that
  the honest outcome would then be deletion. Half the prediction held: the
  bounds machinery is now **0.16%** of a routine `heather check
  lib/ir_v1.hthr` profile. Deletion is nonetheless wrong, and the
  measurement says so plainly — disabling the two skip hooks costs
  **1.47×** on that same check and turns
  `nat/step-into-closed-body` from slope −0.01 into slope 0.99 (150× at
  1024 levels). It changes asymptotics, not a constant. The surviving
  customers are `typing.rs` (which still weak-head-reduces on syntax), the
  elaborator, and conversion's own residual syntactic operations — the
  shared `beta_elim_*` helpers' `id_Γ` application and the `W`/`Wf` step
  telescopes' `shift_local`, neither of which moved to environments.
  A machinery that is invisible in a profile and load-bearing when removed
  is exactly what a good skip test looks like.
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

**Who calls `check_term`, and on which thread.** The elaborator may now
defer a declaration's proof obligation to a pool of worker threads and join
them before the module is accepted (`docs/parallel-kernel-gate-design.md`).
**The kernel gains no judgement from this and no new rule**: `check_term` is
the same function with the same arguments, run against a Ψ that is immutable
for the duration of the call. What is new is only the caller's schedule.

What the trusted base additionally rests on is already true of the
representation and stated above: terms have no interior mutability, so a
built term is immutable and two threads reading the same subtree observe the
same tree; Ψ is persistent (sealed chunks plus a bounded tail), so a worker's
snapshot is an `Arc` clone that the elaborator's next append copies away from
rather than mutates under it. Every piece of checker state is per-call or
per-thread by construction — `Tc`, its conversion memo, the `ValueArena`,
`GlobalCache` and the diagnostic stacks are created inside `check_term`; the
bounds memo, the `fmt.rs` budget cells, the `checks.rs` sampling counter and
`stats.rs` are `thread_local!`. Nothing is shared across workers but
immutable terms behind atomic refcounts.

The kernel's own diff for this was two functions and one counter in `stats.rs`
(`Snapshot::plus` and `merge`, so a joining thread can absorb a worker's
counter delta, and `check_terms`, one bump per call of the `check_term` entry
points), which remain inert by the rule immediately below. The elaborator's
serial replay may reuse a verdict this process's kernel already gave for a
structurally identical (Ψ prefix, binding) pair rather than ask again
(`docs/parallel-kernel-gate-design.md` §5.2); that is a caller's bookkeeping
about its own calls, and the kernel is neither consulted nor changed by it.
The same schedule is applied to a stored module's recheck: `⊢_L Ψ, Ψ'` is
exposed both whole (`check_global_ctx_extension`) and as its per-binding
statement half (`check_global_binding_statement`), the body half being a
`check_term` over the same prefix; the split is a refactor of one loop into
the two calls the elaborator's replay makes, and the verdict is the same
sequence of judgements in the same order.

**Inert counters.** `stats.rs` holds thread-local `Cell<u64>` counters — how
many conversion queries each shortcut answered, how a miss failed, how many
steps and δ-unfoldings the evaluator spent — and nothing in the kernel ever
reads one. They influence no judgment, are compiled in unconditionally (the
build that ships is the build that was measured), and every bump is a
one-liner at the site it describes; deleting the module would change no
answer. Evaluator counts are plain fields on `Eval`, flushed to the
thread-local totals on drop, because the fuel decrement is the hottest line in
the kernel and must not grow a thread-local access. Anything that *formats* a
term — the conversion-miss table and its excerpts — stays behind the
`value-metrics` feature, where it always was. See
`docs/instrumentation-design.md`.
