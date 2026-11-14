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
  count/adjust map normalization (ch. 04 §universe-levels), and a `Level` *is*
  that normal form: every constructor returns the canonical representative,
  so `≈` is `==` (`level.rs`, `issues/kernel-compact-level.md`). A `Level`
  is one `Copy` word (2026-11-10, `issues/kernel-level-eight-bytes.md`): a
  constant, `n + ℓ` and `ω` are spelled in the word, and any other level is
  its index in a process-wide table of joins that holds each join once and
  only grows, so `==` is one integer comparison. An index means something
  only inside the process that made it: whatever leaves the process (the
  images, the content hashes, `Hash` itself) reads a level's spelling
  through `Level::parts`, never the word. `ω` is checker-internal: never
  written in programs, only the type level of `ΠΠ`.
- Universe polymorphism: `ΠΠ ℓ⃗. T` / `Λ ℓ⃗. t` / `t $ l⃗`, non-empty level
  vectors, layer m only.
- Nat with its recursor; fully-annotated dependent functions
  (`app(t; l,l'; x:S.T; s)` keeps S and T as sub-structures — required by the
  code recursors).
- The modal part: global contexts with three binding forms
  (`g : Ctx`, `U : Typ_i(Δ, l)` for i ∈ {c,p}, `u : Trm_i(Δ ⊢ T @ l)` for
  i ∈ {v,c}); local substitutions `·`, `wk^k_g`, `δ,t/x` (the paper's
  `·^k_{g?}` without its decoration, §Representation); global
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
the recursive call from the eliminator's own annotations. The evaluator
holds that λ as `Val::WIh` (2026-10-23,
`issues/tactic-strategy-step-cost.md`), as it holds `elim_Wf`'s (below):
applied over λ children it fires the eliminator on their body, and only a
stuck child function or a reader that inspects the ih builds its syntax,
which shifts the whole motive and step under three binders — once per
recursion depth, since each level fires on the last level's copy. A
Heather tactic's handlers recurse once per request, so that copy was most
of a request's cost. Motivation
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
checks them here, at an open length). Its code is `TmDVec` (design §13
step 4, 2026-10-22), with branches `ty_dvec`/`tm_dvec`; until then it was
admitted at layers p and m only, as `Vec` was before its phase 3.

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
MinusGix/heather-coq#24). Its code is `TmIWf`, the index inside it as in
`TmM`, and its four branches `ty_iwf`, `tm_iwf`, `tm_sup_i`,
`tm_elim_iwf` are heather-coq `RecSpec`'s 57–60 (design §13 step 4,
2026-10-22; `tests/iwf_codes.rs`): the recursor has 65 branches (66 until
`transp`'s went, §13 step 6), and
`DVec`, `IWf`, `sup_i` and `elim_IWf` are code.

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
irrelevance arms, design doc §1). Since 2026-10-22 it has **no
eliminator**: it is a type inhabited exactly when its endpoints convert,
with one proof up to conversion, and its whole content is one conversion
behaviour, the irrelevance arm at `Type::SEq` in `tm_nf` (`Unit`'s audited
pattern — any two proofs convertible, so UIP *at `sEq`* is definitional).
The nominal tag (`Tag_D = sEq(Nat; k; k)`) is all that uses it. It had an
eliminator, `transp^{l,l'}(I; x.P; a; b; e; t)`, with β on `srefl`, a
**strip rule** in `Conv::tm`'s term-whnf stage (a stuck `transp` at
convertible endpoints replaced by its payload) and an endpoint-keyed
congruence that skipped the proofs. Route 2b's fording was its only
producer; `IWf` replaced fording, and `transp`, the strip, its value
eliminator and its code-recursor branch were removed
(`docs/iwf-former-design.md` §7, §13 step 6; `tests/seq.rs` keeps what
stays). Re-adding it at strict motives only is additive and needs no strip.
The codes landed same-day (`TmSEq`/`TmSEmpty`, decoding as
`El (sEq^l(s;t;u)) ⇝ sEq^l(El s; t; u)` and `El (sEmpty^l) ⇝ sEmpty^l`),
and the code recursors gained the branches (`ty_seq`/`tm_seq` mirror
`ty_id`/`tm_id`; `ty_sempty`/`tm_sempty`/`tm_elim_sempty` mirror the
Empty trio; `tm_srefl` mirrors `tm_refl`; `tm_transp` went with `transp`),
so the phase gate is gone. A stuck `elim_sEmpty` inside a box round-trips
the identity recursor *as syntax*: irrelevance does not reach through `□`,
the same firewall as ever. Its companion `sEmpty^l` (same day) is `Empty` made irrelevant as a
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
- **The body is checked at the binding's own layer** (`i = c`; a definition
  at layer v is rejected, since v admits no term but a variable). That is
  what makes δ layer-preserving: unfolding `u` at any layer `j ≥ i` can only
  produce a term that was already legal at `j`. Codata needs nothing more:
  `M`, `corec` and `out` are admitted at c, with `TmM` their code
  (`docs/kernel-m-codes-design.md`).

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

A fifth (2026-11-06, `issues/conversion-meet-past-newer-head.md`): **a side
may arrive at a head the other side was advanced past.** The newer-head
step assumes the older side cannot reduce to the newer head, which holds of
bodies but not of arguments: `meaning(rt, world)(x⃗)` reaches the callee
`world` carries. Unfolding the callee on the other side first, and then the
callee's recursion at a closed count on both, unrolled two-armed passes
into trees no lower meet shortcuts. `Conv::tm_w` now keeps, per side, the
last few spines it stepped past a head the other did not share
(`Passed`), and compares a side against a remembered spine whenever its
head arrives at that one; a side unfolding toward a headless other side
single-steps a bounded number of heads looking for one before the
transparent run (`Conv::meet_on_the_way`). The same unfoldings and fuel
otherwise; a remembered spine is tried once.

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
holds at every instantiation (proved for ch. 06's reduction on a λ + `Nat`
fragment, `docs/kernel-model-design.md`; that iterating an affine or
synchronous class over a run is convertible with the unary fold is proved
there too, with pairs and runs in the fragment, §7) — so `mul` of two runs is one multiplication,
`sub`/`leb`/`min`/`max` cancel run against run however they are spelled,
and `half`'s course-of-values window is a permutation iterated by
exponentiation. A cost the calculus itself charges that no class covers
(`div`'s state machine, an `Int`-valued fold) is answered in the library
by a definition whose reduction cost matches its meaning, or by
reflection, never by a kernel case for that definition — and what is not
accelerated is refused with `OutOfFuel`, never a process abort.

**Numbers written a piece at a time** (2026-11-10,
`issues/succ-chain-numbers-fold-unary.md`). `Succ(t)` evaluates to a
successor over a thunk, and a number read off a call's result is the glued
call until something eliminates it, so a counter threaded through a
recursion (`next`, then `Succ(next)`) is a chain of thunks and not a run:
a classified fold over it took a step a link, where the same number as a
literal is one run. A `Sync` or `Affine` fold now reads such a chain *as
far as it is already forced* as the run it spells (`Eval::forced_run`):
through successors, through the forced tails of runs, and through the
forced unfoldings of glued calls, down to the first thunk that is not a
forced number. This is a representation change of the first kind above.
Each piece's memo is replaced by a `NatRun` over the same base thunk that
denotes the same number, so a memo stays a function of its closure. It
forces nothing (a fold that would not have looked below a predecessor
still does not, so no fuel is spent on a value the unary fold would have
left alone), it charges a unit of fuel a piece and each piece is rewritten
once, a glued call keeps its glue (it is the unfolding's memo that is
rewritten), and reading a sealed proof's memo is noted as forcing it is.
A first fold over a chain nothing has forced is still a step a link.

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

A fold whose one argument is a `Nat` is the same machine with an infinite
state (`docs/bitvector-literal-entry-design.md` §10.10). `bitvec::ofNat`
recurses on the width carrying `x`, and its step is `cons(f(x), ih(g(x)))`;
there is nothing to tabulate, so the class instead reads `f` and `g` off the
probe value as **data**: each is the state variable under a spine of
projections and `elim_Nat`s whose steps classify as affine trees (the `Nat`
classes above — `odd_bit`'s and `half`'s course-of-values windows are
permutations), with every fold's base, and a peeled fold's innermost step,
read back as a closed pair of naturals and bits. At a closed state the word
is then arithmetic — the orbit `x, g(x), g(g(x)), …` read through `f`, each
iterate computed as `eval/runs.rs` would compute that fold, here as a walk
of the tree's functional graph — and nothing is replayed. Adequacy is the
substitution property with the state as a third probe variable: the probe
value was reached with `k`, `ih` and `x` neutral and no case split stuck on
any of them, so at every instantiation the step is the same eliminations
applied to `v`; and since what was read out of them holds no closure, it is
applied to `v` without substituting into one. Whatever does not read back
closed — a base that mentions `x`, an opaque fold, an `ih` inside the bit —
declines the class, and an open state at the call declines the firing: both
fold exactly as before. The replay this replaced (run the step once per bit)
was correct and no faster than the structural fold, which is why it was
never landed.

Conversion compares two vectors over such an element type by their words,
before Σ-η, packing a structural side by the `fst`/`snd` η would have taken;
a side that is two stuck spines is left to the neutral-first guard, and a
difference settles the comparison at the bit it appears on. A native run
charges one fuel unit per word, as a literal's entry does: a run is at most
one word, so the charge stays proportional to the data, and it is strictly
less than the structural path spent, so no verdict that fuel allowed becomes
a refusal. (It was one unit per bit until 2026-11-14, which made the
accounting most of the steps of word-level code with no time behind it.) What does not
classify — an open `Fin` index, a recursion on a shift count, a state type
above the cap — folds exactly as it does today, and what does not meet the
criterion — an element type with a payload of its own, an open width, a chain
that stops being a Σ — is compared exactly as it is today.

**A vector literal is a term** (`Term::VecLit`,
`issues/packed-vector-literal-term.md`, `docs/bitvector-literal-entry-design.md`
§3, §6). `VecLit{ℓ, elem, zero, one, w, bits}` is a closed prefix of a `Vec`
all of whose elements are one of two given terms, and it is `NatLit` one
former over: notation for the right-nested Σ-chain `⟨e(b₀), ⟨e(b₁), … ⟨⟩⟩⟩`
with `e(0) = zero` and `e(1) = one`, `1 ≤ w ≤ 64`, bit `i` the `i`th
element. Its typing rule checks `elem` as a type and `zero` and `one`
against it — three judgements, independent of the width — and nothing else:
the rule contains no two-valued criterion and names no library type, so the
term means the chain whatever `elem` is. Adequacy is that unfolding
identity, and it has one owner, `term::vec_lit_unfold`: the chain's head
pair with the `Vec` rule's own annotations and a `VecLit` one element
shorter (or `⟨⟩` at width one). `reduce.rs`'s `Fst`/`Snd` arms, the
evaluator's fallback, and the full chain (`vec_lit_chain`) are all built
from it, so the literal and its chain are one step apart everywhere. What
the term buys is entry: when `elem` meets the bit criterion and `zero`/`one`
evaluate to its injections, the evaluator reads the whole literal into one
`Val::BitRun`, the eager route the value domain cannot have at `Term::Pair`,
available because the term carries the element type a pair does not. That
entry charges one fuel unit, not one per bit: the width is capped at the
word, and it is fewer than the chain's walk spent, which is the rule above.
When the criterion declines (an open element type, an element with a payload
of its own, an `elem` that is not two-valued) the literal evaluates to its
head pair with the shorter literal behind it, one node per demanded bit.
It is a compact spelling the code recursors cannot see whole, so like the
checked spellings it is refused under `box` and in layer v, and the quote
boundary and the exporter write out its chain (`RebuildChecked`). The
elaborator emits one only for a vector literal whose elements are closed and
at most two distinct terms over an element type that whnfs to a sum, packing
the last 64 and keeping any prefix as pairs (`check_vec_lit`); everything
else elaborates as before.

**A long vector literal is one node** (`Term::VecItems`,
`issues/long-string-literal-stack-overflow.md`). `VecItems{ℓ, T, items, from}`
is `VecLit`'s construction for elements of any kind: notation for the chain
`⟨items[from], ⟨…, ⟨items[n-1], ⟨⟩⟩⟩⟩`, with the one-step view
`term::vec_items_unfold` (its head pair, with the tail the same array one
element further on) as the single adequacy owner, read by the projections,
the evaluator, and the full chain (`vec_items_chain`) alike. Its typing rule
is the chain's premises — `T` a type at `ℓ` and every live item a `T` — and
returns `Vec^ℓ(T; n)`. What it buys is depth, not speed: a chain is as deep as
the literal is long, and every syntax-directed walk (typing, substitution,
`bounds`, hashing, the image writer, `Drop`) recursed once per element, so a
string literal of a couple of thousand characters overflowed the checker's
native stack. The node is one level deep at any length and each walk loops
over the array. `from` makes the tail O(1); equality, the Merkle hash and the
image encoding read only the live window, so two nodes with the same live
elements are the same term. Like `VecLit` it is a compact spelling, refused
under `box` and in layer v and written out as its chain at the quote boundary
and by the exporter. The elaborator emits it for a vector literal of more than
256 elements (`VEC_ITEMS_ABOVE`, `check_vec_lit`), and a collection literal
over one builds only a 64-element constructor spine (`LONG_SPINE`) with the
fold over the node behind it, so the term the gate sees stays shallow too.
Comparing two long vectors *by value* unfolds them into chains; conversion
walks those at constant native depth by deferring the comparisons it meets
deep (docs/deep-term-walks-design.md), in time still quadratic in the length
(`issues/vec-items-window-bounds.md`).

**A deep data value is walked by a loop, not a frame per level.** Data is
deep along one child (a list's tail, a vector chain's rest, a successor's
predecessor), and `term::spine_child` names it. Past `SPINE_ITERATE_AT`
frames, the bounds walk answers the spine bottom-up and substitution
rebuilds it in a loop over a heap path; the checker and conversion queue
the premise they meet that deep instead of descending (premises of a yes/no
judgment are a conjunction), with every later premise of the same context
queued behind it, and the frame that returns to depth zero judges the queue
as a stack in the recursive walk's own order (order changes no verdict, but
a conjunction stops at its first failure, so it changes the cost). A speculative
δ-attempt drains its own queued premises before it counts as a success and
drops them when it fails; a `true` recorded while premises are queued is
memoized provisionally and taken back with them (conversion), and a refused
check that queued anything forgets the typing memos. Below the threshold every walk is its old code.
Design and what still recurses: docs/deep-term-walks-design.md.

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
  nothing forced to drop.
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
- **Two spellings of one former are compared on the syntax** (2026-11-10,
  `Conv::lockstep`, issues/conversion-closed-pair-memo.md). A type is read
  as it is spelled: itself, or the decoding `El^l c` of a code. When two
  spellings show the same former (`Nat`, `Ty`, `Unit`, `Empty`, `sEmpty`,
  squash, `Π`, `Σ`, `W`, `+`, `Id`, `sEq`), their components are compared
  as spellings in turn, and only a pair that is not one former is given to
  the domain. This is the rule the machine applies, not a new one: each of
  these formers is weak head normal, a code's `El` decodes to it in one
  step over the `El`s of the code's components, and the normal-form arm
  compares exactly those components in exactly those scopes. What it
  saves is the domain's copy of every node the two sides agree on, which
  for a large type named on one side and written out on the other is
  nearly all of them: the cost becomes a walk of the syntax plus the
  machine's work where the spellings differ. The binders the walk passes
  are pushed onto the scope only when such a place is reached. Codes
  compared as terms at a universe are walked the same way with their
  leaves compared as codes, never through their decodings, because `El` is
  not injective (`Vec` at a canonical length and its `Σ` chain are one
  type and two codes). The rewriter does none of this (`Dom::SPELLED`), so
  the differential tests hold the walk to the specification.
- **Convertible closed pairs are kept beside Ψ** (2026-11-10,
  `ClosedPairs`, same issue). A spelling that reads no local variable is
  one type under every Γ and every environment of its Ψ, so `convertible`
  for two of them is a fact about the two nodes, the level, the layer and
  the judgment (types, or codes), and it is kept in the `GlobalCache` for
  the gate: an elaborated type is a dag, and without the table a pair of
  sub-dags is judged once per path that reaches it, in every query. The
  rules are the verdict memo's: only `convertible` is kept, never
  exhaustion; nothing is kept while a premise is queued or a provisional
  verdict could have been stood on; a refusal is not kept at all. Three
  more are its own. A decoded code is identified by the code under its
  `El`, since the `El` node is allocated at each decode. Every keyed node
  is owned by its entry, so an address names one syntax for as long as it
  is a key. And a walk that began at a root, which may be open, keeps only
  pairs whose footprint it has asked. The table is bounded and never
  evicts, so within a gate a judgment never costs more later than it did
  earlier, which the checker's own memos rely on when a debug build judges
  a kept pair again. A debug build also judges a sampled hit of this table
  again without it.
- **δ is glued.** A `u^δ` evaluates to a neutral carrying a memoized
  `unfold` thunk, `Some` exactly when Ψ defines `u`. The δ-lazy order is
  unchanged — compare without forcing the thunks, and on `NotConvertible`
  at a shared defined head force both and retry — but the head test is now
  O(1) instead of a spine walk, and a second visit to the same unfolding is
  free. The `has_defs` gate survives. The rescoping `shift_global(v + 1)`
  that every unfold used to recompute is memoized per `GlobalVar` in a
  `reduce::GlobalCache` owned beside the Ψ it belongs to (7.8% of a routine
  `heather check lib/certgen/ir_v1.hthr`) — and on the **value** path is not
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
  The arena is one region per kind of value, and a region is made at its
  first allocation (`value::Region`, 2026-11-10): most queries touch two or
  three of the ten, and a region's first chunk is an allocation. The
  evaluator's frame stack is the arena's too, lent to each `Eval` and
  returned empty, so a query's evaluations grow one stack
  (`issues/value-domain-allocation-constant.md`).
  Successful thunk results are **kept for the whole query** (2026-10-22),
  and since 2026-11-10 in the closure itself: one word of a `TmClo`/`TyClo`
  (`value::Memo`), written once
  (`issues/value-domain-allocation-constant.md`). Until then they lived in
  tables owned by the arena and keyed by the closure's address, which hashed
  at every force and grew by rehashing in every query. The arena keeps a
  closure until the query ends with its environment cells, so one value per
  forced closure is a constant factor over what the query already holds —
  the order of its work, which fuel bounds. A bound below the query's live set is not a constant factor of
  anything: what it evicts and the query reads again is forced again, and so
  are the evicted cells that force reads, back through the computation.
  History: the caches were bounded FIFOs (16K entries, then 64K from
  2026-09-07, when a width-64 structural consumer's working set measured
  ≈20K values). Unbounded strong memos had made the first arena version
  exceed the 4 GiB test cap on `lib_std_bitvec`, from when values owned the
  closures they reached and the bitvector consumers were superlinear; both
  are gone. The FIFO then grew two patches for one loss
  (`issues/computed-argument-reevaluated-in-rounding.md`: a tier protecting
  forces that spent `COSTLY_FORCE` fuel, and tombs regluing an evicted glued
  neutral's unfolding), and was still what made long evaluations by `refl`
  fragile: the effectful source's `cat` at width 64 spent nine tenths of its
  fuel copying one byte, and ran out on three, recomputing evicted
  environment cells; kept, a run takes about a tenth of the steps and grows
  linearly in its passes (`issues/kernel-value-cache-evaluation-thrash.md`). Peak
  memory on the suite's heaviest tests was unchanged or lower, since less
  recomputation allocates fewer closures. The memo changes the fuel a query
  spends, never a verdict: it is a function of the closure alone, and only
  successes are remembered.
  A closure whose body reads **no capture** is one value wherever it is
  read, so the arena also keeps closed closures' values by their body and
  global offset alone (`TmClo::closed_ident`; the environment's length too
  when the body holds a weakening `wk^k_g`, which counts it), and
  the fold-class and transducer memos key a step or motive the same way
  past its own binders (`TmClo::ident_under`). Both answer the same
  question the closure key does, for every closure over that body: a
  definition's unfolding closes its body's constants and its folds' steps
  over each call's arguments afresh, and keyed by address they were
  re-evaluated and re-probed once per call — on a native certificate piece
  that was over a third of the evaluator's steps
  (`issues/native-certificate-pieces-remaining-cost.md`). The test is the
  node's bounds (`bounds.rs`), the same reading conversion's closure identity
  makes.
  Hot handles are kept compact: an environment closure captures only its
  persistent head and length, while whichever machine extends it supplies the
  already-owned query arena explicitly. Persistent cells remain two pointers.
  Universe levels on the uncommon synthesized `Vec`/`El` type closures live
  in the same arena rather than determining the size of every closure. On
  64-bit targets direct tests pin `Env`/`EnvNode` at 16 bytes and both term and
  type closures at 40 bytes: four words of closure and the memo word.
- **A selection's term is a closure, one per node** (2026-11-10,
  `issues/projection-description-quadratic.md`). A description of a Σ's
  second component (`Sel::Snd(a)`, `docs/intro-by-type-design.md` §3.2)
  holds the term the codomain is instantiated at, and every query that reads
  the description evaluates the chain again. Evaluating `a` eagerly made the
  type of a record's `k`-th field `k²` eliminations per query: the terms are
  `fst@(p)`, `fst@(snd@(p))`, … and each walked its spine from `p`. So the
  codomain is handed `a`'s closure in the identity environment
  (`ValueArena::subject`), one per term node for the query, and the closure
  of a checked projection is the pending elimination of its receiver's
  closure. The receivers of one spine are shared nodes, so each field is one
  elimination, and a field no later type mentions is never computed. A
  variable at the head of such a spine is described in its entry's own scope
  (`ITy::At`) and never shifted into the ambient one.
- **An identity environment is a length** (2026-11-10,
  `issues/conversion-query-identity-environment.md`). A conversion starts in
  the identity environment of Γ, and reads one for a prefix of Γ wherever it
  opens a variable's type or a description that denotes at another depth.
  Built as a list it was four allocations a variable, per query and per
  such read, and two builds of one environment were different objects to
  every identity check. So an environment's list may stop short of its
  length: the entries it does not hold are the outermost ones, each the
  neutral variable at its own level, as the arena's one closure of that
  variable (`ValueArena::var`). `Env::identity(n)` allocates nothing, and
  pushing a variable's closure onto the identity environment of its level
  gives the next identity environment, never a cell, so each has one
  spelling. The conversion scope therefore carries no value environment
  (`conv::Env::rho()` is Γ's length), and a binder is opened with the same
  closure whoever opens it. More sharing is more reflexivity hits and
  nothing else: two closures of one variable denote one value.
- **A variable's type is weakened once per distance** (2026-11-10,
  `issues/binder-types-weakened-per-use.md`). Γ holds a binder's type in the
  scope it was bound in and a use reads it some binders later, so the
  variable rule used to copy every open node of the type per use. The
  checker keeps the weakened node by the entry's node and the distance
  (`Tc::weakened`, holding the entry so the address stays its node's) and
  returns it as a deferred syntactic type. Two uses of one binder at one
  distance then hand conversion one node, which its identity shortcut
  answers. A projected variable's type is not weakened at all (`ITy::At`,
  above).
- **Abstraction is one traversal that skips what it cannot change**
  (2026-11-10, `issues/abstraction-walks-the-type-twice.md`). Abstracting a
  pattern out of a type makes room for the new variable and replaces the
  occurrences. It weakened the subject first and searched the copy; now the
  search weakens as it walks, against patterns weakened once, and returns a
  subtree with no variable at or above its depth as it is. That skip needs
  every pattern to be open, since a closed pattern can occur in a closed
  subtree, so a closed pattern turns it off. `tests/subst_laws.rs` holds
  the result to the two-pass meaning, maximality included.
- **Tables keyed by the kernel's own addresses use one multiply hasher**
  (`value::PtrHasher`; 2026-11-10, `issues/conversion-memo-hash-cost.md`):
  the arena's caches, the verdict memo, the closed-pair table and the
  checker's conversion and typing memos. The keys are this process's
  allocations and small integers, never input someone chose, so SipHash
  bought nothing and was a twentieth of the kernel's instructions on the
  showcase. The hasher rotates its product before returning it: a product's
  low bits depend only on its factors' low bits, an aligned address has four
  that are zero, and the table picks a bucket by the hash's low bits.
- **Value-machine instrumentation is explicit and observational.** A caller
  may lend a `ValueMetrics` collector to arenas directly, or use the profiled
  typing entry points to aggregate the many conversion arenas created by one
  kernel gate. It counts region/environment/closure allocation plus cache
  lookups, hits, inserts and per-region peak residency. Ordinary
  arenas carry no collector. There is deliberately no global or thread-local
  sink: concurrent checks cannot contaminate one another's measurements, and
  enabling counters cannot change fuel, cache policy, or a verdict.
- **Level equivalence** is equality of words. `adjust(count(l))` runs where
  a level is built, every constructor returns the canonical representative,
  and a representative has one word (`level.rs`); `ω` is equal only to
  itself. `le` is `l' == l ⊔ l'`. Nothing about `adjust`/`count` (in
  particular the dominated-constant rule `n + ℓ ⊒ n`) may be weakened to
  make two levels meet more often: the constructors are the decision
  procedure now, and the reference model in `level.rs`'s tests is what holds
  them to it.
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
  The same gate keeps a **typing memo** on node identity
  (`issues/kernel-typing-memo-on-node-identity.md`; `typing.rs` §The typing
  memo): per term node and scope, an elimination's inferred type and the
  expected types an intro form checked against, so a node reached along two
  paths (a `let` alias used twice) is judged once per scope rather than once
  per path. The scope is identities only: the node's allocation, Ψ's and Γ's
  identity tokens, Γ's base, layer, universe count and the `box` bit, which
  are everything a rule reads besides the node; each entry owns the node and
  both tokens. A hit skips whole judgments, conversion queries and their
  fuel included, so which lookups hit must be a function of the input, and
  is by construction: entries are chosen
  by node kind, never by reference count, nothing is evicted, and failures are not cached. A
  node with no weakening tail that reads only Γ's innermost few entries, whose types stay
  among them, is keyed by those entries instead of by Γ (a *strengthened*
  scope): its judgment is the same under any Γ ending in them, which is what
  lets an indexed family's index functions be judged once rather than once
  per level of every case tree whose motive carries them
  (`issues/indexed-family-recursion-gate-cost.md`).

## Representation

- **de Bruijn indices, three independent namespaces**: local variables
  (into Γ), global variables (into Ψ — one index space covering all three
  binding forms), universe variables (into L). A binder never shifts the
  other two namespaces' indices. All names in the tex are display-only.
- **Separate `Type` and `Term` enums**, mutually recursive, mirroring the
  Tarski split. Judgment functions will be similarly mutual.
- `Rc` for sub-terms (substitution clones aggressively; sharing keeps that
  cheap; no interior mutability anywhere *in the terms*, which is exactly
  what makes the bounds below sound). **`Rc` is the kernel's own pointer**
  (`rc.rs`, 2026-11-10): `std::sync::Arc` around the value and a head, two
  words in which the kernel keeps what it has computed about the node. Every
  workspace file that holds syntax spells `use heather_kernel::rc::Rc;`
  (`crate::rc::Rc` here), and the API is `Arc`'s. An unsized payload (a
  slice, a `str`, a trait object) is a plain `Arc`, since nothing is asked
  of one. It was `Arc` under the alias `Rc` from 2026-09-11, when the gate
  went parallel; the serial tax of atomic counts was measured then, as the
  control the decision turned on (`issues/kernel-arena-terms-frozen-prefix.md`).

  What the pointer owes: the value is reached mutably only through
  `Rc::make_mut` and `Rc::get_mut`, and both empty the head before they
  hand it out, so a head describes the value beside it. The kernel has no
  `unsafe`; the head is atomics, written last-flag-first-read so a reader
  on another thread sees a whole answer or none.

  **A client's mark** (`rc::Mark`, 2026-11-10,
  `issues/emission-decode-walks-every-annotation.md`): spare bits of the
  head's flags are offered to the kernel's clients, one bit a
  property, set by `Rc::mark` and read by `Rc::marked`. The kernel reads
  none of them, so no mark is in the trusted base. The client owes what
  the kernel's own answers owe: the property is a function of the value
  under the node and of nothing else, no context and no registry, so the
  two functions that empty a head keep it true. The first is the
  elaborator's "nothing under this type decodes" (`Mark::DECODED`). A
  property that reads a table that grows (which lowerings are registered)
  is not one, however often it is asked.
- **Per-node free-local-variable bounds** (2026-07-31,
  issues/subst-visits-closed-subtrees.md route B): the local-namespace
  traversals skip subtrees that provably cannot change (loose de Bruijn
  bound ≤ depth, no weakening tail `wk^k_g` in scope; the empty tail `·` is
  changed by nothing) in O(1) instead of walking
  them. `src/bounds.rs` computes the summary as a pure function of the
  immutable subtree, on first demand, and **keeps it in the node's head**
  (2026-11-10, `issues/free-variable-bounds-in-the-node.md`). No
  construction site in kernel or elab sets it or could get it wrong: a new
  node's head is empty, and that is the objection to "a field on the node"
  answered, since the field is filled by the one function that defines it.
  The one drift hazard, its binder counts against `subst.rs`'s dep table,
  is covered by a debug assertion at every skip site that re-runs the real
  traversal, under the 300-seed law suite. The global namespace's bound
  (`1 +` the largest free global variable) is kept the same way.

  Until then the summaries were in direct-mapped tables keyed by node
  address, under weak references, filled at a node's second query: one pair
  of tables a thread for the substitutions, one for the typing memo so that
  its questions would not settle the substitutions' markers, one for the
  global namespace. The tables answered the first objection and cost three
  things. A question was a hash and a probe of memory the node is not in.
  A sixth of the walks recomputed an answer a collision had evicted, and
  every other walk was a node's first, which no table size changes. And
  which subtrees a traversal skipped depended on what had been asked before
  and on which addresses collided, so the substitution counters varied from
  run to run. In the node, a question is a read of what the caller already
  holds, a node is walked once while it lives, and the counters are
  functions of the input. The weak keys had also held every dead node's
  block until its slot was reused, which was more memory than the heads are.

  **Kept, re-measured after the value domain** (2026-07-31). The NbE round
  predicted that conversion's 21% of the deep-path profile would *leave*
  rather than shrink, taking the machinery's main customer with it, and that
  the honest outcome would then be deletion. Half the prediction held: the
  bounds machinery is now **0.16%** of a routine `heather check
  lib/certgen/ir_v1.hthr` profile. Deletion is nonetheless wrong, and the
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
- **A substituted variable is a node the substitution already had**
  (2026-11-10, `issues/subst-variable-copies-payload-root.md`). The
  traversal's variable hook answers with a node, not a value: the payload's
  own under no binder, and wherever lifting does not change it (a payload
  that reads no local variable, which its bounds answer); a shared leaf for
  a variable payload; and otherwise one lifted node per payload and depth
  within the call. So `t[s/x]` holds `s` itself, as shared as `x` was
  used, and `s` keeps what is known about it by address: its bounds, the
  typing memo's entry, conversion's shortcut against another holder of the
  same node. Until then each occurrence was a copy of the payload's root,
  equal to it and a stranger to all of those. Identity is still never part
  of an answer: the node handed out is exactly the term the walk built, so
  the laws of `tests/subst_laws.rs` are indifferent to the change, and the
  sharing itself is stated on pointers in `subst.rs`'s tests.
- Local contexts are `(base, entries)` where base is `·` or a context
  variable `g`; entries carry `(T, l)`.
- Local substitutions mirror the paper's three-form syntax, `·` / `wk^k_g`
  tails under a list of terms, with one departure.

  **The empty substitution is `·`** (2026-11-09,
  `issues/empty-substitution-tail-decoration.md`). The paper writes the
  empty tail `·^k_{g?}`, decorated with the length `k` and the base `g?` of
  the context it is read in, so that the queries δ̂ (length) and δ̌ (base) are
  total functions of the syntax. This kernel's `SubstTail::Empty` carries
  neither. Both are redundant in the paper's own system, which is why
  dropping them is a change of representation and not of theory:

  - *Nothing computes with them.* The operations that mention the
    decoration of an empty tail only produce another empty tail's: a
    weakening adds to `k`, a global substitution adds `|σ(g)|` and replaces
    the base by `σ(g)`'s, a composition `· ∘ δ` overwrites both with δ̂ and
    δ̌. The one consumer of a length is the expansion of `wk^k_g` when `g` is
    replaced by a concrete context (the variables `k + |Γ'| − 1 … k`), and
    that reads a weakening's.
  - *δ̂ is read only off weakenings.* Composition asks for δ̂ in `wk_g ∘ δ =
    wk_g^{δ̂}`. That composition is scoped only when δ targets a context
    based at `g`, and then δ's own tail is `wk^m_g`, which still carries
    `m`. (`LocalSubst::wk_len` is the partial δ̂; δ̌ has no reader left.)
  - *Typing pinned them.* The rule for `Γ ⊢ ·^k_{g?} : ·` demands `k = |Γ|`
    and the base Γ's, so among well-typed terms the decoration is a
    function of the position, and the erasure `·^k_{g?} ↦ ·` is injective
    on them. A derivation in the paper's syntax erases to one here, and one
    here decorates to exactly one there, by writing Γ's length and base at
    each empty tail. The rule here is `Γ ⊢ · : ·`, for every Γ.
  - *The value domain had already dropped them* (`value.rs`, `VTail`), for
    the reason given there: both are determined by the scope a value lives
    in. Nothing outside the kernel read them either: the exporter closes a
    global over its context and never looked at the tail.

  What the decoration cost is why it went. A reference to a top-level
  definition is `u^·`, so with `k` in it every type mentioning a definition
  was different syntax at every binder depth: no weakening or instantiation
  could share it (about a third of all substitution visits on a library
  check existed only to renumber it), `==` could not recognise the same
  closed type met under two binders, and the typing memo's closed and
  strengthened scopes applied only to types mentioning no definition at
  all. With the base in it, a closed statement read under a context
  variable was a kernel `SubstMismatch` unless every tail was rewritten.
  Each of those had grown a workaround (the closed-conversion memo's
  special cases for a bare global, the elaborator's "frame" a closed copy
  had to be re-read in); the representation removes the cause. A subtree
  with no free local variable and no `wk^k_g` is now *closed syntax*: the
  same allocation serves every context, and the bounds summary's one tail
  flag means "a weakening shows", which is rare.
- Ψ's bindings are named by `GlobalVar`, with one departure from the
  paper's single index namespace.

  **Constants are addressed from the start of Ψ** (2026-11-10,
  `issues/psi-references-by-level.md`). The paper has one global context Ψ
  and names its bindings by de Bruijn index, the distance from its end. This
  kernel reads Ψ as `Σ; Ψ′`: a **signature** Σ, the first
  `GlobalCtx::consts` bindings, and the **variables** Ψ′ after it. A
  reference (`GlobalVar`) has two spellings, and each binding exactly one:

  - a variable of Ψ′ is an index, as in the paper;
  - a constant of Σ is its position from the start of Ψ.

  With an empty signature this is the paper's syntax verbatim, and that is
  what every hand-built Ψ and every kernel test is. The rules that change:

  - *Reference.* `Σ; Ψ′ ⊢ c_p^δ` needs `p < |Σ|` and reads binding `p`;
    `u_i^δ` needs `i < |Ψ′|`. An index that reaches into Σ is refused, so two
    references read in one Ψ are the same binding exactly when they are
    equal, and no comparison ever has to resolve a spelling.
  - *Binders extend Ψ′.* `letbox`, the code recursors' branches, `Λg`, `ΛU`,
    and outside the kernel the elaborator's goals and metavariables, push
    variables. Nothing a term binds is ever a constant.
  - *Σ grows only under no variable* (`GlobalCtx::commit`). So a constant's
    context, statement and body are checked in Σ alone, and by the reference
    rule they mention no variable free. This is the formation rule for Σ,
    and like the well-formedness of Ψ it is a precondition of every
    judgement, not something a judgement re-derives; `commit` checks it in
    debug builds.

  What this buys is that the three operations on the global namespace are
  the identity on constants, by construction and not by a cache:

  - *Weakening*, by variables (`shift_global`) or by further constants (no
    operation at all): a position from the start does not move when Ψ grows
    at the end. In particular `Σ; Ψ′ ⊢ J` gives `Σ, c; Ψ′ ⊢ J` with the same
    syntax, which under indices alone renumbered every reference to Σ in `J`.
  - *Substitution* (`apply_global`). A σ in instantiation form replaces the
    innermost variables and renumbers the variables below them. Constants
    are below every variable and are not renumbered, because nothing between
    them and the start of Ψ was removed. The β-rules for `letbox` and the
    recursors are subject-reducing for the reason they were: the body was
    checked with its bound globals in Ψ′, so by the reference rule no
    constant in it names one of them.
  - *Reading a binding.* A variable's statement is scoped in its prefix of Ψ
    and is weakened by `i + 1` to be read (`u^δ`'s rule). A constant's is
    closed in the variables, and every constant it mentions is at the same
    position in every later Ψ: it is read as stored. `reduce::GlobalCache`
    holds rescoped statements and bodies of variables only.

  The identity is also cheap to recognise on a term that is not a single
  reference. Both operations act on free variables alone, so they skip a
  subtree whose largest free global variable is below their depth, a
  per-node bound memoized as the local one is (`bounds.rs`, §The global
  namespace). A committed statement or body has bound zero, and so does
  every type copied out of one, which is most of what an elaborator
  rescopes and zonks: those walks end at the root.

  *Adequacy.* Erase a derivation here to the paper's by spelling `c_p` as the
  index `|Ψ| − 1 − p` at each occurrence (the occurrence's own Ψ, binders
  crossed included). Reference, weakening and substitution above are the
  paper's rules read through that erasure, so a derivation here erases to one
  there. Conversely a derivation there, over a Ψ whose first `n` bindings are
  each well-formed in the bindings before them, is one here with `|Σ| = n`
  by respelling each index that reaches the first `n` bindings. The erasure
  is not injective on raw syntax (it forgets where Σ ends), which is why the
  split is part of the context and not of the term.

  *Why not positions for every binding.* A single "level" namespace also
  makes closed terms stable under extension, but a bound global then has to
  be renumbered whenever its term moves under a longer Ψ, every weakening
  needs the length of the Ψ its argument was scoped in, and the elaborator's
  worlds (`Σ`, then a declaration's goals, then a `meta fn`'s binders)
  commit helper definitions to Σ while goals are in scope, which would
  renumber the goals at each commit. The split is the locally nameless
  discipline: what a binder in scope introduced is relative to the end, what
  is declared is absolute.
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
`fmt.rs` budget cells, the `checks.rs` sampling counter and `stats.rs` are
`thread_local!`. Nothing is shared across workers but immutable terms behind
atomic refcounts, and each term node's head (`rc.rs`, §Representation): what
`bounds.rs` has computed about that node, a pure function of the immutable
subtree. Two workers that ask the same question of one node write the same
words, and the flag that says an answer is there is released after them, so
a worker reads a whole answer or computes its own.

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
