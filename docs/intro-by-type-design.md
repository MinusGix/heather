# Intros and projections annotated by the type they were checked at — design

Design pass on `issues/elab-emits-normal-form-of-matched-type-argument`,
the successor of `docs/name-per-value-design.md` §9 and the "structural
kernel-side design pass in a fresh session" its 2026-09-16 entry asked for.
Written per the `docs/nbe-conversion-design.md` discipline: decisions with
rationale, rejected alternatives priced, acceptance stated before the first
kernel line. Coordinator-written after discussion with the user
(2026-09-20); an implementer executes §9.

The defect, in one sentence: the elaborator normalizes a type to decide a
match and then **writes the reduct's components into the intro and
projection annotations it emits**, because the kernel's `pair`/`inl`/`inr`/
`fst`/`snd` synthesize from components; that object is ≈3.5ⁿ in the
combinator nesting as a tree and linear as a value graph, and every phase
downstream — the kernel gate's queries, resident memory, the semantic image,
the image's decode — is its size. Three rounds tried to *spell the reduct
more compactly* (candidate D, the readback, the free-variable mint); this
pass changes the question: the annotation carries **the type the elaborator
had before it normalized**, and whoever needs the components computes them
in the machine that already shares — the kernel's evaluator. The exponential
object is then never constructed in syntax, anywhere, and nothing has to see
through a name.

What the user asked this pass to optimize for, in order: **is it a
conservative addition**, and **how easy is it to get the implementation
wrong**. The Coq formalization's cost is a consideration, not a veto.
No falsifier runs before implementation: the round implements and then
analyses its own numbers (§9 stage 0 records what to compare against).

---

## 0. What this changes, in one line each

- **The declarative theory:** five term formers at the computing layers
  (`pair@`, `inl@`, `inr@`, `fst@`, `snd@`), each a *checked spelling* of an
  existing former, with a typing-preserving translation to it (§2.4). The
  layer-c code grammar, the code recursors and their 56 branches: untouched.
- **`typing.rs`:** inferred and expected types become `ITy`, syntax or an
  un-spelled *selection* of a component (§3); every existing rule stays on
  syntax, the five `@` rules and the views of a selection use the value
  domain in a per-query arena, and a `materialize_eagerly` mode is the
  differential oracle. (The first draft's migration to `Tc<D: Dom>` was
  withdrawn after stage 1b priced it: §3.7.)
- **`conv.rs`:** untouched in its arms — no conversion arm compares an
  intro's or projection's annotations today (§3.4). Gains the head views for
  the new forms.
- **`reduce.rs`, `eval.rs`, `value.rs`:** the new forms' β, neutrality,
  whnf grammar, evaluation. `fst`/`snd` fire on either pair spelling.
- **The elaborator's emission:** `build_ctor`'s injection and tuple, and
  `projection`'s emitted copy, write the un-reduced type they hold (§4).
  The mint, the readback and the counter (`mint.rs`, `rbemit.rs`,
  `rbcount.rs`) are superseded, not extended.
- **Nothing is named**: no Ψ mints, no `let`, no readback. §6 says why each
  is refused again.

---

## 1. The site, and what is written there

`docs/conversion-query-traversal-design.md` §10.2–10.3 and
`docs/projected-tuple-tower-design.md` §3 attributed the exponent to the
unit. Restated with the code positions this pass depends on:

- `Elaborator::build_ctor` (`crates/elab/src/inductive.rs`, ~2085) holds
  `pre_whnf`, the un-reduced expected type — for the `wf_branch` route the
  motive instantiated at the injected value, an `El(case(…))`-headed
  application — and two lines later `expected = self.whnf(cx, expected)`,
  the reduct. `spine` (~1746) peels the reduct's `Sum` layers into
  components; `inject` (~606) writes them into `Inl.lhs`/`Inl.rhs` and the
  `Inr` chain; `build_fields_skel` (~2300) whnfs each Σ layer and writes
  `Pair.fst_ty`/`Pair.snd_ty` from the components. **Field checking never
  reads an annotation**: `elab_check_skel(arg, &fst)` takes the inline
  component; only the emitted slot is respelled (comment at ~2374, "checked
  against the inline components above, per the line"). The split the design
  needs already exists.
- The kernel's rules (`crates/kernel/src/typing.rs` ~1705–1830,
  `Pair`/`Fst`/`Snd`/`Inl`/`Inr`) `ty_check` each component in its own
  context and rebuild the former as the synthesized type. The pre-whnf type
  cannot be written into these slots: they take a Σ's halves, not a type
  that reduces to a Σ.
- The measured site stack of `complete_post`'s queries is
  `Pair×12 < Snd < Snd < Fst < Fst < App×20` (issue log, 2026-09-17): the
  reduct sits inside **projection** annotations as well as pair annotations.
  So the eliminators `fst`/`snd` are in scope, not only the intros.
- The reduct is exponential *as a tree* and linear *as a value graph*
  (`projected-tuple-tower-design.md` §3, 196× at `t_qt5`), and the kernel's
  evaluator already builds the graph: closures over environments, one cell
  per binder (`eval.rs` `apply`, "copies nothing").

The whole design is the observation that the kernel already owns a
sharing-preserving computation of exactly the object the elaborator is
spelling, and only lacks a syntax into which "the type I had" can be written.

---

## 2. The forms

### 2.1 Syntax — revised 2026-09-20 after stage 2's stop

Five term formers. The annotation on the three intros is **optional**, and
the two projections carry none:

```
pair@(a; b)               checked:  against T with T ⇝* Σ^{l₁,l₂}(x:S). U:  a : S,  b : U[a/x]
pair@^{T}(a; b)           infers T, same premises (the annotated form; inference position only)
inl@(a) / inl@^{T}(a)     checked against / infers T,  T ⇝* A +^{l₁,l₂} B,  a : A
inr@(b) / inr@^{T}(b)     symmetric
fst@(p)                   infers S,          where p infers T and T ⇝* Σ(x:S). U
snd@(p)                   infers U[fst@(p)/x], same
```

An unannotated intro is **not inferable** (`NotInferable`, the verdict the
kernel already gives `box` forms in inference position, typing.rs ~2233);
it is checked against the expected type, which the checker holds as an
`ITy` (§3) and views in the value domain. That is what lets a constructor
value nested inside a constructor value be written with **no type at
all**: the expected type of a field is `Sel{expected, Fst}`, a description,
never a spelling. The annotated form exists for the one position the
elaborator cannot make a checking position — a constructor value at the
head of a projection or as a scrutinee — and it carries the un-reduced
type the elaborator had, as the first draft said.

**Why the first draft's annotation-everywhere failed** (stage 2, issue log
2026-09-20): `build_ctor` computes `spine(&whnf(expected))` and hands each
Σ layer of the tuple a *summand of the reduct* as its "type"; only the
outermost injection has the un-reduced `pre_whnf`. An annotated inner pair
therefore wrote a reduct component — two components of a whnf for one
parent, a factor ~2 on a 3.5ⁿ object — and the curve did not move
(×3.31 / ×3.71 on both sides). The inner layers have **no** un-reduced
spelling, and the fix is to write none.

Rust: `Term::PairAt { ty: Option<Rc<Type>>, fst, snd }`, `InlAt`/`InrAt`
likewise, `FstAt { pair }`, `SndAt { pair }` (stage 1a's `ty` on the
projections is dropped). Doc comments say "checked spelling of `Pair`" and
point here.

### 2.2 Why new forms and not a change to the existing five

The existing `pair(x:S.T; a; b)` cannot lose its components, and the
reason is not the elaborator: it is the code recursor. `tm_pair`'s branch
telescope (`crates/kernel/src/rec.rs` ~1705) is

```
(ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x:U_S), ℓ'),
 u_a : Trm_c(g ⊢ U_S), u_b : Trm_c(g ⊢ U_T[u_a/x]), x_S, x_T, x_a, x_b)
```

The **types of the field sub-structures `u_a`, `u_b` are stated in terms of
`U_S`, `U_T`**. A branch receiving one `U_Σ` cannot state the type of `u_a`
without decoding `U_Σ`, and a code variable in a telescope does not reduce
(`docs/ch05-06-lemma-audit.md`, "boxed code is exhaustively recursable is
wrong as stated"). This is the substance of `projected-tuple-tower-design.md`
§5 F's rejection — "an annotation that must be reduced before it can be read
is not recursor-reachable syntax" — and `docs/delam-extensions.md` §16.5's
warning that an annotation-free variant is conservative only where the
annotations are recoverable. Both are right about *layer c*. Neither applies
to a form that layer c never sees.

So the component-annotated forms stay exactly as they are, remain the only
pair/injection/projection spellings inside a `box`, and keep their recursor
branches unchanged. The new forms are what the elaborator writes for
programs and proofs.

### 2.3 The restriction is "not under a quotation", not a layer

The first draft said "layers p and m only". That does not transcribe: Heather
checks **every declaration body at `Layer::Code`** (`crates/elab/src/lib.rs`
~3637, `gendefs.rs` ~3473; `DESIGN.md`'s "the body is checked at the
binding's own layer, which is what makes δ layer-preserving"), and only the
statement at `Prog`. A layer predicate is constantly false at every emitter
(stage 2 measured it: `LayerMismatch` on a two-field record).

What §2.2 actually needs is that the code recursors never meet a checked
spelling, and the recursors range over exactly one thing: the payload of a
`box`. So the rule is a **side condition on the two `box` rules**: the
payload of `box` (`BoxTy`, `BoxTm`, typing.rs ~1187/1196) contains no
checked spelling. Implemented as one bit on the checker's `Env`, set when
those two rules enter their payload and read by the five rules
(`Tc::checked_spelling_admitted`, which also keeps layer v's refusal,
replacing stage 1a's `computing_layer`); the elaborator's twin is
`Elaborator::emits_at_forms`, which reads `Cx::quoted` and a quote-depth
counter held across payload elaboration (`quote.rs`), so a helper that
starts from a fresh `Cx` inside a payload cannot escape it. Consequences:

- The code grammar — what a `box` may contain, what `code_eq` compares, what
  the 56 recursor branches range over — is unchanged: no branch is added, no
  telescope changes, the surface `match code` language is untouched.
- A definition body at layer c may contain checked spellings. δ at a
  computing layer unfolds it into a term that is legal there; δ inside a box
  is opaque (`definitions.rs`, both directions), so no checked spelling ever
  appears inside code by unfolding either.
- Formally it is a decidable syntactic predicate on the payload, like
  "closed", not a new judgment index. Ch. 06 is untouched: the recursor β
  rules fire on box payloads, which the side condition keeps free of the
  forms.

**Amended in stage 2 (2026-09-22): the quote boundary.** The second
bullet's "no checked spelling ever appears inside code" was argued for δ
only, and δ is not the only way in. A payload is elaborated at the code
scope, but it also receives terms built **outside** the quotation: applying
a global inside `code { … }` copies the callee's statement into the `app`'s
`dom`/`cod` annotations, and a solution or a reduct is pasted in whole.
Stage 2 met the first at once (`ir_v1`'s `ret_cert`: `ret_conv`'s statement
holds constructor values, now emitted as `inr@`/`pair@`). Neither
`Cx::quoted` nor an elaborator-level quote-depth guard reaches a term that
arrives already built.

So every place a payload is boxed translates it first:
`typing::spell_checked_in_code` (and `_ty` for a boxed type) is `⌊·⌋` of
§2.4, computed by the eager checker — which already spells every
component — recording the former it viewed at each checked spelling and
rebuilding with the component forms, repeated until none is left (a
recorded component may carry checked spellings copied from a definition,
which the rebuilt component form then `ty_check`s). The sites are
`quote.rs`'s payload, certgen's marked body (`global_body_in_code_form`)
and the reflection API's boxed statement (`fn_type_code`). It is outside
the trusted base in effect: the `box` rule re-checks the result, so a wrong
translation is a refusal, never an acceptance. The cost — the reduct —
comes back only for terms pasted into a quotation.

Admitting the checked spellings into code instead was considered and
refused: code equality is syntactic (ch. 05, Static Code), so one term
would have two unequal codes that every `code_eq` and every user-written
`match code` must identify, and a `tm_pair`-style branch cannot state an
unannotated pair's children's types, nor observe that an annotation's code
reduces to a Σ. Code's own sharing is a separate question with its own
issue, `issues/code-payload-sharing.md`; the translator is the single place
a future code-native sharing former would be targeted from.

### 2.4 Conservativity

Define the translation `⌊·⌋` on typing **derivations** (it is
type-directed, as a bidirectional elaboration into a fully annotated syntax
always is): `⌊pair@(a; b) ⇐ T⌋ = pair(x:S. U; ⌊a⌋; ⌊b⌋)` where `T ⇝* Σ(x:S).U`
is the whnf the derivation contains (Determinacy makes it unique up to the
budget); the annotated form and the projections likewise, reading `T` from
the annotation or from `p`'s inferred type; identity elsewhere. Then:

- **Typing.** `Γ ⊢ t : A` implies `Γ ⊢ ⌊t⌋ : ⌊A⌋`, by induction on the
  derivation; the `pair@` case is the existing `pair` rule plus one
  conversion `T ≡ Σ(x:S).U` (from `T ⇝* Σ(x:S).U`, ch. 06 reduction is
  included in conversion). The inferred type `T` and the former are
  convertible, so a consumer that had `T` now has something convertible to
  what it needs.
- **Reduction.** `fst@(T; pair@(T'; a; b)) ⇝ a` and `fst(x:S.U; pair@(T';a;b))
  ⇝ a` — β on projections fires on any pair spelling and reads nothing
  from the pair's annotations (`docs/delam-extensions.md` §16.2 is already
  that statement for the existing forms). `case` on `inl@` likewise.
  Reduction commutes with `⌊·⌋`.
- **Conversion.** Σ is η (`conv.rs` ~1586, `eta_proj` at the ambient type;
  there is no `TmView::Pair`); sums compare the injected value only, "the
  annotations on inl/inr are forced by well-typedness"; neutral `fst`/`snd`
  compare heads and read the Σ the head *infers* (DESIGN.md, "application and
  projection are typed"). None of these reads an annotation, so the new
  forms need new head views and no new decisions.
- **Under a box.** Nothing. The side condition keeps the forms out of every
  payload, so the code grammar and its metatheory are the current ones.

The extension is conservative in the only sense that matters for the trusted
base: every derivation in the extended system translates to one in the
current system with the same conclusion up to conversion, and the current
system's metatheory (the ch. 05–06 audit, the ch. 07 obligations already
owed for Σ and sums) is not touched at layer c and is inherited by
translation at p and m. §7 states the ch. 07 bill precisely.

### 2.5 What the form is *not*

It is not "the annotation is a type code". `T` is a `Type`, in the type
namespace, like `Refl { ty }`, `SRefl { ty }`, `Squash { ty }` — the
kernel's three whole-type-annotated intros, which are the precedent. A
code (`⌜T⌝ : Ty`) would buy nothing at p/m and would re-open the recursor
question at c, which §2.3 closes by fiat.

It is not a `let`, not a Ψ mint, not a readback: §6.

---

## 3. The checker: deferred types, not a migration to values

**Revised 2026-09-20, after stage 1b's two stops** (issue log: the §3.7
arena at `p10` ×2.63 peak RSS at step 0 alone, with conversion's own
temporaries still freed per query; and `VTy::UPi`/`CtxPi`/`TyPi` having no
representation for a body inferred *inside* its telescope). The first
draft's §3 — `typing.rs` generic over `Dom`, `Values` in production —
is withdrawn. What replaces it is smaller, arena-free, and keeps every
existing rule on syntax. The original text's reasoning survives in §3.1;
§3.2–3.6 are the new mechanism.

### 3.1 Why syntax alone is not enough

`fst@(T; p)` infers `S`, the first component of `T`'s whnf. With the
rewriter that is a *syntax* — the substitution-expanded component, the
exponential object, built in the kernel this time
(`projected-tuple-tower-design.md` §5 F's first objection, and it is
correct). With the evaluator it is a closure, but a closure lives in an
arena, and stage 1b measured what an arena that outlives a query costs:
every binder push retained for the declaration is +9.3 GB on
`probes/str/p10.hthr` before conversion's temporaries even join it. The
checker may therefore hold neither the syntax of a component nor a value
of one. What it can hold is a **description**.

### 3.2 `ITy`: an inferred or expected type is syntax, or a selection

A checker-internal type (`crates/kernel/src/typing/ity.rs` or inside
`typing.rs`; never a `Type` variant, so no kernel walker gains an arm):

```
ITy = Syn(Rc<Type>)
    | Sel { of: Rc<ITy>, sel: Sel, at_depth: u32 }

Sel = Fst | Snd(Rc<Term>)          -- of a Σ:  S  |  U[a/x]
    | Lhs | Rhs                    -- of a sum
    | Dom | Cod                    -- of a Π:  S  |  T under one binder
```

`Syn` is what every rule produces today. `Sel` is *the first component of
whatever `of` reduces to*, un-spelled — the "reduction provenance" §10.3 of
the traversal design said the reducer would have to hand its caller,
written down as a datum instead. `at_depth` is the Γ length the description
was formed at, so it can be evaluated later under more binders (identity
environment of that length, weakened by the difference). An `ITy` is
arena-free, `Rc`-shared, and linear in the source: a `Sel` chain of length
k over a `Syn` costs k nodes.

**Where `Sel` arises, and only there:** the five `@` rules (§3.4), and the
views a *checking* position takes of a `Sel` expected type (§3.3). No
existing rule constructs a `Sel`: `app`'s result is `cod[arg/x]` from its
own annotations (`Syn`), `fst`'s is its annotation, the Λ inference arms
wrap the body's inferred type (see §3.5). So on every declaration without an
`@` form the checker's behaviour is byte-identical to today's, which is the
stage 1b gate's "counts unchanged to the unit".

### 3.3 Two consumers, and the rule about the rewriter

An `ITy` is consumed by exactly two operations, both of which already exist
in some form:

- **`conv_ty(expected: &ITy, inferred: &ITy)`.** The reflexivity shortcut
  is structural `==` on `ITy` (`Syn == Syn` is today's α-test; two equal
  `Sel` descriptions are the same type by Determinacy). The cross-head memo
  keys on `ITy` as it keyed on `Type`. A miss evaluates both sides into
  **one per-query arena** — today's `conv_type_cached` shape, unchanged in
  lifetime — with `Sel` evaluated as: `eval` the `of` in the identity
  environment of `at_depth` (weakened to the current depth), `delta_whnf`,
  take the `TyView`, force or apply the selected closure. Then
  `Conv::<Values>::ty` on the two domain types. The arena's bounded memo
  serves the query and is dropped with it, as now; there is no memo cell
  that could outlive its arena (`TmClo` has none — forced values live in
  the arena's cache, `value.rs` ~925).
- **`view(expected: &ITy) -> View`**, the operation behind the nine
  `Tc::whnf` sites and the `@` rules. For `Syn` it is today's rewriter
  `Tc::whnf`, exactly — same fuel, same δ policy, same syntax components.
  For `Sel`, and for the `@` rules' annotation `T` *even when it is `Syn`*,
  it is the value domain: evaluate in a per-query arena, `delta_whnf_ty`,
  read the head and levels, **discard the value**, and return a `View`
  whose components are new `Sel`s over the input (`Pi` → `Dom`/`Cod`,
  `Sigma` → `Fst`/`Snd(·)`, `Sum` → `Lhs`/`Rhs`). For the other formers
  (`CodeTy`, `CodeTm`, `UPi`, `CtxPi`, `TyPi`, `Vec`, `Wf`, `Id`, …) the
  view returns a **materialized** `Syn` former: the value's sub-structures
  for those are syntax already (`TyClo::as_syn`, `value.rs` ~1054 — the
  ctx/level/body slots the evaluator never opens), or, where a slot is a
  closure with a non-identity environment, the rewriter is run on the
  materialized `of` (§3.5). Correct everywhere; fast on the three formers
  the tower is made of.

**The rule, stated once:** *the rewriter never runs on a type that came
through an `@` annotation or a `Sel`.* Everything else keeps the rewriter,
which is why the migration is small and why the differential oracle is
cheap (§3.6).

### 3.4 The five rules

```
pair@(a; b) ⇐ E:     view_v(E) = Sigma  else HeadMismatch;
                     tm_check(a, Sel{E,Fst});  tm_check(b, Sel{E,Snd(a)})
pair@^{T}(a; b) ⇒:   l = ty_infer(T);  view_v(Syn T) = Sigma;  fields as above with E := Syn T;  ⇒ (Syn T, l)
inl@(a) ⇐ E:         view_v(E) = Sum;  tm_check(a, Sel{E,Lhs});     inr@ symmetric;  annotated forms as pair@^{T}
fst@(p) ⇒:           (E, l) = tm_infer(p);  view_v(E) = Sigma{l₁,l₂};  ⇒ (Sel{E,Fst}, l₁)
snd@(p) ⇒:           same;  ⇒ (Sel{E,Snd(fst@(p))}, l₂)
unannotated intro ⇒: NotInferable
```

`view_v` is the value-domain view of §3.3 (never the rewriter, even for a
`Syn` `E`). `E` is whatever the checking position holds: for a field of an
outer `pair@` a `Sel`, for a branch body the motive instance, for an
argument the `app`'s domain annotation — in every case a description or a
linear spelling, never a reduct. The `Snd(a)` argument is the *term* `a`,
evaluated per query in the identity environment, so the description stays
arena-free.

Contiguous `fst@` / `snd@` chains use `Tc::projection_at_spine`: infer the
non-projection head once, then view and select each receiver in one arena
local to that chain. Every intermediate receiver must still expose a Σ.
Only the levels and the final arena-free `Sel` description return to typing;
no value survives the call. Fuel is granted per view, as in the per-node
rules. The eager oracle and quotation translator retain those per-node rules.

### 3.5 The three Λ inference arms, and completeness

`ULam`/`CtxLam`/`TyLam` inference wraps the body's inferred type in
`Type::UPi`/`CtxPi`/`TyPi`. When the body's inferred type is `Syn`, as it
is on every declaration today, nothing changes. When it is a `Sel` — a
layer-m metaprogram whose body infers a tower component, a shape no
current file has — the arm **materializes** the `Sel` through the rewriter
(`Tc::whnf` of the `of`, then the component's syntax) and wraps that. This
is the one place the rewriter may meet an `@`-derived type, it is complete
(the rewriter's answer is the checker's current answer), it is never
silently wrong (the first draft's `Values` route was, for a body that
depends on ℓ⃗ through its captured environment), and it is exponential
exactly when today's checker is. `materialize` is also what §3.3's "other
formers" branch uses. Its call count is a counter column (`ity_materialized`)
so a workload that hits it is seen, not guessed.

### 3.6 The oracle

`Tc` gains one mode bit: `materialize_eagerly`. Under it every `Sel` is
materialized the moment it is formed, so the checker is *today's checker*
on the `@` forms (the reduct spelled by the rewriter), and `typing::oracle`
is that mode. `tests/typing_differential.rs` runs both modes over
`wt.rs`'s streams with the `@` option on, both Ψ and `opaque(Ψ)`, ≥ 4 seed
streams plus a fuel sweep, seed-only reporting, `OutOfFuel` from either
side never a disagreement. The modes implement the same typing rules;
projection spines batch their value-domain views only in deferred mode,
while the eager mode spells each selection at its original per-node boundary.
The differential tests that evaluating a description and rewriting it agree — which is
machine adequacy (`nbe-conversion-design.md` §11.2) applied at the typing
seam, and already the property `conv_differential.rs` holds conversion to.

### 3.7 Cost, and what is measured before it is optimized

Every miss and isolated `Sel` view evaluates the tower's type afresh in a
per-query arena. Per query that is the value graph, linear in the nesting
(`projected-tuple-tower-design.md` §3); across a declaration it is
`queries × depth`, against today's `3.5ⁿ` per query. Whether that
re-evaluation dominates is stage 2's first number (a `sel_evals` column
beside `queries`). If it does, the fix is a declaration-scoped memo of
forced heads — which needs an arena that outlives a query and therefore a
representation whose memoized values can never dangle — and that is a
separate design, priced against this section's number, not a thing to
slip into stage 2. The per-query arena is kept because stage 1b measured
what abandoning it costs. A contiguous projection chain is one such query:
its intermediate views reuse the preceding value instead of replaying the
selection prefix at each link. This removes quadratic prefix replay without
retaining an arena across independent typing or conversion queries. The
elaborator's checked field reads likewise return the inferred structural
type directly; emission belongs to a caller writing an annotation. Respell
each inferred suffix and recursive instance matching revisits overlapping
conjunctions at every source dot. Tail substitution still traverses the
remaining type per field; this leaves quadratic source work even with
linear kernel evaluator steps and linear instance-match calls.
[conjunction-projection-type-preparation-cost](../issues/conjunction-projection-type-preparation-cost.md)
records the attribution and the decision to retain structural substitution.

### 3.8 The value forms for the unannotated spellings

Stage 1a mapped `pair@^{T}` onto the existing `Val::Pair` by viewing `T`.
An unannotated `pair@(a;b)` has no `T` for the evaluator to view, so
`Val::Pair`/`Inl`/`Inr`'s annotation closures and `Elim::Fst`/`Snd`'s
become `Option<&TyClo>`, `None` for the unannotated forms. Stage 1a's grep
(issue log, §9.0 item 3) established that no reader of a pair or injection
value reads them, and that every reader of the projection annotations reads
them off a `VTy::Sigma` to *construct* an elimination; those constructors
wrap in `Some`. The levels on the projections' views are already `Option`.

**Withdrawn from the first draft:** `Tc<D: Dom>`, the `Env` merge, the
`Dom` widening and the six constructors (step 0 is reverted; its log entry
is the record of what it cost), one arena per gate (§3.7's sentence "the
address-space rail is the measurement" was answered: no), and §6 item 6's
refusal of a hybrid — that refusal was of a checker holding *values*; a
checker holding *descriptions* is what this section adopts, and the
distinction is the arena.

---

## 4. The elaborator's emission

### 4.1 The emitters that change

All in `crates/elab/src`, all behind `!cx.quoted` (inside a quotation
payload today's component forms continue to be written):

| site | writes | annotation |
|---|---|---|
| `inductive.rs` `inject` (~606), via `build_ctor` | `inl@`/`inr@` chain | outermost injection: `Some(emit_ty(pre_whnf))`, the un-reduced type in hand at ~2116; inner injections of the chain: `None` |
| `inductive.rs` `build_fields_skel` (~2382) | the Σ tuple | `None` at every layer — the field is in checking position by the outer rule |
| `forded.rs` `build_fields_collect` (~1050) | the forded tuple | `None` |
| `inductive.rs` `projection` (~2860–2935) | `fst@`/`snd@` with `cur_emit` | none; the receiver infers |

The emitter reads **nothing** out of the reduct for an annotation any more.
`spine` and the whnf that feed field *checking* stay exactly as they are:
the elaborator still computes the reduct to decide the constructor and to
check the fields against inline components. That transient is stage 3 (§5),
and it is now genuinely independent — stage 2 alone makes the emitted term,
the image and the kernel's work linear.

The outermost `Some` is there for the one kernel position that infers a
constructor value (a projection head, a scrutinee); if `NotInferable` shows
up on the corpus the answer is `Some` at that emitter, never a component.

*Stage 2 found two such emitters (2026-09-22), both on the x86 model:*
a **single-constructor** declaration has no injection layer, so its tuple
is the outermost value and takes `pre_whnf` itself (`inject_at`); and the
container-length projection in `build_ctor` reads the freshly built tuple
as a receiver, so that copy's root takes the component type it was checked
at.

`wf.rs` `fin_index` (~1762) already annotates a tail "with `Fin` itself
rather than its unfolded sum"; the same rationale.

### 4.2 The readers, and the principle that makes them safe

The mint failed its readers audit three ways (`mint.rs` ~12–71): a name hid
a record from `record_of_at`, a threshold change stopped a conversion, a
kernel `NotConvertible` from a statement `infer_term` chose. This design's
readers see something different in kind: **the annotation is the type the
source had**, a spelling every reader already accepts from a user-written
annotation. `record_of_at` (~2957) is "structural read first, whnf paid only
when it fails" — an un-reduced type is its designed fallback, not a new
case. The audit list, all of which must be walked and each of which gets a
one-line answer in the implementation log:

- `display.rs` ~443: reads `Inl.lhs` and calls `display_tag_of` on it; under
  `inl@` it must whnf `T` first (through `Elaborator::whnf`, which already
  does `unspell_here` → oracle → `unspell_sum_components`).
- `inductive.rs` `projection`'s `cur_emit` and `matching.rs` `field_rewrap`
  (~664): read `fst_ty`/`snd_ty` off `Fst`/`Snd` to rebuild a projection
  chain; under `fst@` they carry `T` forward instead of components — a
  smaller invariant. *Amended in stage 2 (2026-09-22):* with the
  projections unannotated there is no `T` to carry. `field_rewrap`'s
  η-expansion writes its inner `pair@`s unannotated (each is a field of the
  one above) and gives the **root** the type of the chain's base, because the
  root replaces the base wherever the goal mentions it — including as a
  projection's receiver, which must infer. That type is at hand only when
  the base is a local (the field-match case); any other base declines and
  motive synthesis falls to its later strategies.
- `lgg.rs` ~670–686: anti-unification requires equal annotations on both
  sides; two `pair@`s compare `T`s, which are structurally smaller and more
  often identical than two reducts.
- `emission_walk.rs` ~243: the exhaustive, wildcard-free slot walker; five
  new arms, each `ty @ d` with no binder.
- `read_ctor` (~4450), `matching.rs` ~627, `omega_cert.rs`, `certgen.rs`
  ~2312: shape-only walks over `fst`/`snd`/`val`; add the arms, read nothing.
- `module_image.rs` encode/decode: five tags; `merkle.rs`: five hashers.
  Image format version bump.

### 4.3 The image, and the decode budget

`calc_text`'s image is 483 M nodes because its declarations *are* the
reduct. After 4.1 the emitted term is source-shaped. The decode budget
(256 M nodes) and size budget (512 MiB) are not raised; the round reports
the image's node count as a result, and the closed issue
`semantic-image-over-budget-republished-every-run`'s rule — a budget that
admits an image nothing can decode is the pathology — stands. `--only`
comes back on `calc_text` when the image fits; `check-only-no-stored-image`
is the round's day-one work regardless (§9), so the inner loop is not 95 s
while stage 1 is being built.

### 4.4 What is deleted

`mint.rs`, `rbemit.rs`, `rbcount.rs`, `rbname.rs`, the `HEATHER_RB*`
environment, the `mint_ctor_reduct` call on the default path, the five
`global_padding()` Ψ-renumbering sites if nothing else uses them, and the
`wip/mint-readers-audit` branch. Not in stage 1 — in stage 2, after the
emitters switch, so the deletion is measured (the readback ran at every
`build_ctor` to learn there was nothing to name: `elab_whnf_ns` ×3.5–4 on
fired items). Stage 2 measured the deletion at **zero on the default
path** — the devices all return on a false `HEATHER_RB*` guard — so it is a
dead-code commit of ~6 400 lines, separate, with that number in its message. `emission_walk.rs` stays: it is the auditor.

---

## 5. Stage 3: the elaborator's own reduct (deferred, with candidates)

After stages 1–2 the only exponential object left is the elaborator's
*transient* reduct — `Elaborator::whnf` (`lib.rs` ~7533) spells the head
former through the rewriter (`SemanticOracle::whnf_type`, `oracle.rs` ~80,
consults the value machine only to decide *whether* to rewrite, then
rewrites), `spine` reads its components, `elab_check_skel` checks fields
against them. It costs `elab_whnf_ns` (2.2 s at `t_qt3`) and the
elaborator's peak RSS, and it is freed per declaration.

This is not designed here, on purpose: it is the intricate half, its
mechanism depends on what stage 2's numbers say is left, and it has no
customer until the image and the gate are linear. Candidates, for the
record, in the order the coordinator would try them:

1. **Head-only spelling with lazy components.** The oracle returns a
   `Type` whose head former is spelled and whose component slots are
   `Type::El(u^δ)`-style references to *evaluator-owned* thunks — no: the
   elaborator's `Type` is the kernel's, and a value cannot live in it. So:
2. **A value-carrying `elab_check` for the constructor-field path only.**
   `build_fields_skel` receives `TyClo` components and checks each field
   against a value; the unifier is entered only when the field has metas,
   and then a bounded readback of *that component* (`rbemit.rs`'s faithful
   arms, resurrected for one caller) spells what unification needs. This is
   the mint's readback with the naming removed and the scope shrunk to the
   one site whose sharing matters.
3. **Deciding the constructor without spelling.** `spine` needs only the
   `Sum` depth and the `Wf` shape to pick a constructor; the value machine
   answers that from `VTy` heads with no rewriter. Combine with 2.

The bar for stage 3 is the elaborator's RSS and `elab_whnf_ns` on the
controlled curve, measured after stage 2, before its design is written.

---

## 6. Rejected shapes, with reasons

1. **Changing `pair`/`inl`/`inr`/`fst`/`snd` in place** to carry `T`. §2.2:
   `tm_pair`'s telescope types `u_a` by `U_S`; a collapsed annotation
   leaves the field sub-structures untypable in the branch. Every metaprogram
   over code would change. Refused on the recursor, independently of Coq.
2. **A kernel `let`.** Priced and refused in `nbe-conversion-design.md` §14
   and `projected-tuple-tower-design.md` §5 F; re-refused here on the user's
   two criteria rather than on Coq: the former is conservative and trivial,
   but the *device that places the binders* is the mint's — the same
   free-variable scoping, the same top-down choice over multiplicity, the
   same three readers — and the object still exists as a DAG and is still
   serialized. A `let` lowers the formalization cost of a route whose cost
   was never the formalization.
3. **The Ψ mint, resumed.** `name-per-value-design.md` §9: it reaches the
   numbers (`complete_post` queries 3.70 M → 0.78 M at T = 64) and fails the
   readers audit three ways, with `HEATHER_RB_MINT=1` measured a zero on the
   current tree at its default threshold (issue, 2026-09-17). The object is
   still built; every reader must see through a name. Superseded.
4. **"Typing memoized on node identity per context"** (the 09-16 phrasing).
   A memo over the exponential object: cheaper walk, same image, same RSS.
   `conversion-query-traversal-design.md` §5's memo refusal applies.
5. **Keep one `pair` and have the recursor's β decode `T` at firing time**,
   handing `U_S`, `U_T` to the unchanged branch. Preservation fails at c:
   `box(pair@(T;…))` and `box(pair(S.U;…))` are distinct codes under
   `code_eq` (syntactic payload), but the rule would give them one reduct
   whose type mentions the latter. §2.3's layer restriction is what makes
   this question not arise.
6. **A hybrid checker whose inferred types are `Syn | Val`** — values in
   the checker, hence an arena that outlives a query. Refused, and stage 1b
   measured why (×2.63 RSS at `p10` for the cheap half). The adopted
   `Syn | Sel` (§3.2) holds descriptions, not values, and is arena-free.
7. **Annotation as a type code** (`⌜T⌝`). §2.5.
8. **Whole-type `case` / `elim_W` / `elim_Wf`.** Their motives are forced
   sub-structures (§16.5, "cannot be recovered from anything else"); their
   summand/shape annotations could take the `@` treatment later if the
   attribution names them. `close_body`'s `App/Pair/Fst` shape does not.
   Not in this round.
9. **The typed `app` rule** (36 %). Left where it is,
   `conversion-typed-eliminator-congruence`, with its own before/after;
   after this round it is a constant over a linear term and may not be
   worth its rule change.

---

## 7. Cost, and the boundaries not moved

**Metatheory bill.**

- **Ch. 04:** five term rules at layers p, m; a layer restriction stated
  like the "Note on Layer v Rules". `docs/delam-extensions.md` §6 gains a
  §6.7 "checked spellings" with the rules and the translation of §2.4;
  §16.5 gains one sentence saying the opposite choice was taken *for the
  computing layers* and why the code grammar was left alone.
- **Ch. 06:** β for the projections on either pair, `case` on either
  injection; neutrality; whnf grammar. Determinacy and Preservation cases
  are the existing ones under `⌊·⌋`. `docs/ch05-06-lemma-audit.md` gains
  the five rows and inherits their verdicts by translation; the recursor
  coverage section is explicitly unchanged.
- **Ch. 07:** five cases in the logical relation at p/m, each "the case for
  the translated form". `docs/metatheory-ch07-extensions.md`'s per-former
  table gains five rows citing §2.4. No new obligation at c.
- **Machine adequacy** (`nbe-conversion-design.md` §11.2): the value of a
  `pair@` relates to the whnf of its translation; one new case in the
  mechanical "arms respect ⊩" argument per form.
- **`DESIGN.md` Fragment ledger:** one paragraph, the five forms, "checked
  spellings, computing layers only, zero recursor branches"; the "fully
  annotated so everything but `box` infers" sentence gains "— and the
  checked spellings infer their annotation" ; the Algorithms bullet on
  typing gains the §3.2 sentence, in the shape of §11.3 there.

**Kernel cost.** Stage 1b changes the *type* of what the checker passes
between its rules (`Type` → `ITy`) and adds two evaluators of a
description (§3.3); no existing rule's logic moves. The containment is
that a mistake is a *disagreement with the eager mode* on a generated
well-typed term, reported by seed, and not a silent acceptance; and that
on a declaration with no `@` form the counters must not move at all.

**Boundaries not moved.** `reduce.rs` stays ch. 06's transcription and the
specification. The trust story of DESIGN.md's "verbatim has moved from the
algorithm to the specification" extends from conversion to typing, and
should be written as the same weakening with the same compensating
controls. No definition-shape acceleration, no new conversion rule, no
budget raised.

---

## 8. Measurement

`scripts/perf ab --marker <column>` for every binary comparison, with a new
counter column that the after binary emits and the before does not — e.g.
`intro_at_nodes`, the count of `@` forms checked. Per `CLAUDE.md`: counters
and seconds apart; a moved counter on an unchanged tree is a behaviour
change.

The corpus, in the main checkout's untracked `probes/` (not in the
worktree; copy the files the round uses into its tree under `probes/` and
list them in the log): the controlled curve `t_qt2`, `t_qt1`, `t_cp9`,
`t_qt3`, `t_qt5` (component byte-identical, reply varied — the exponent's
own instrument), `probes/str/p10.hthr` (the 27× record axis, 90 lines, both
sides in one process), `docs/showcase/calc_parser.hthr` (`complete_post`,
`close_body`, `expr_body`, `factor_body`) through
`heather check --cache --only`, and `docs/showcase/calc_text.hthr` through
`scripts/showcase check calc_text` (the image size, the decode, and whether
`--only` comes back).

Baselines on the current tree (`5cf63f2`), all recorded on the issue and
in the two prior designs, restated so the round does not re-measure them:
queries across the curve 6 495 / 390 503 / 2 395 753 / 7 928 179 /
29 447 197; `complete_post` 3 681 039 queries, 246 634 steps, 9.6–9.8 s at
width one; `calc_text` 334 CPU-s, 9.8 GiB, image 762 MB / 483 M nodes;
warm replay of that image killed at 23.7 GiB.

---

## 9. Stages, gates, kill criteria

**Day one, before stage 0:** `check-only-no-stored-image` — `--only`
distinguishes "never checked" from "image refused as over budget" and says
the node count. Small, independent, and it is the inner loop's difference
between 5 s and 95 s on the module this round is about.

### Stage 0 — instrument and bar (0.2)

The `intro_at_nodes` counter (zero on the current tree, by construction);
the corpus copied and listed; one `scripts/perf ab --replay`-able record of
the before side. Nothing else. No falsifier: the user's instruction is to
implement and then analyse.

### Stage 1 — the kernel (the irreducible core)

1a. The five forms through the mechanical transcription (§3.4): `term.rs`,
`subst.rs`, `bounds.rs`, `fmt.rs`, `reduce.rs` (β, neutrality, grammar,
layer guard), `eval.rs`/`value.rs` (§3.5 decided and logged), `conv/dom.rs`
views, `merkle.rs`, `module_image.rs`. The rewriter checker `typing.rs`
gains the five rules *on syntax* — which builds the reduct, and is
acceptable because it is about to become the oracle.

1b. `ITy` and `Sel` (§3.2); `tm_check`/`tm_infer`/`conv_ty`/the nine
`whnf` sites take and return `ITy`; `view` per §3.3 with the value-domain
path for `Sel` and for the `@` annotations; the five rules per §3.4; the
Λ arms and `materialize` per §3.5 with the `ity_materialized` and
`sel_evals` counter columns; the `materialize_eagerly` mode and
`typing::oracle` per §3.6; `tests/typing_differential.rs`. No arena
outlives a query. On a declaration without `@` forms the checker must be
byte-identical in verdicts and counters.

*Gate:* full `scripts/test` green including `tests/typing.rs`'s golden
suite, `ch05_06_lemmas.rs` (the identity-recursor proxy must be unchanged —
it never sees an `@`), `conv_differential.rs`, `eval_differential.rs`;
`typing_differential.rs` green; `scripts/bench --check` against a control freshly saved on the parent
commit on a quiet box (the committed baseline is stale and the box's
noise floor was ≳1.5× at load 12.8 in stage 1a — the
`desktop-bench-gate-for-constants` protocol); the `wt.rs` generation of
`@` forms is **off by default** and on only for the differential and
golden tests, so the bench fixtures measure the workload the baseline
measured, and a `check/at-forms` fixture with its own baseline is added
only once `Tc<Values>` is the gate; re-save with the verdict recorded;
`lib/ir_v1.hthr` and the routine corpus not regressed in seconds or peak
RSS (§3.6); the x86 certificate gates green under their existing fuel.

*Kill criterion:* a typing-vs-typing disagreement not traced to a
*rewriter* bug within one session → revert 1b, keep 1a (the forms are
inert without an emitter and the syntax checker accepts them), re-scope.
This is `nbe-conversion-design.md` stage 2b's criterion, verbatim.

### Stage 2 — the emitters (0.5), resumed after the 2026-09-20 stop

Step 0: replace stage 1a's `computing_layer` and the `HEATHER_AT_SPIKE`
instrument (committed with the readers audit) by the box side condition of
§2.3 — one `Env` bit set by the two `box` rules, the five rules refuse
under it, a golden test that `box(pair@(…))` is rejected and a body at
layer c with a `pair@` is accepted; make the intro annotation `Option`, drop
the projections' annotation, and `Option` the value closures (§3.8) — the
transcription of stage 1a, revisited at the same sites; `typing_differential`
extended with unannotated forms in checking position and `wt.rs` generating
them. Then §4.1's four sites behind `!cx.quoted`; §4.2's readers re-walked
for `ty: None` (the `spelling.rs` views); `emission_walk.rs` arms.

*Gate:* full `scripts/test`; `showcase_gate` (`calc_text`) green; the
curve re-measured through `scripts/perf ab --marker intro_at_nodes` — the
**per-layer query ratio on `t_cp9 → t_qt3 → t_qt5` is a small constant**,
the value graph's ×1.3 being the reference, against ×3.5 today;
`complete_post`'s queries and `decl_emit` nodes an order of magnitude down
with no name introduced (the mint's 0.78 M / 90 k are the numbers to beat,
and this round should beat them because it writes no mint bodies);
`calc_text`'s image stored under the unchanged budgets and `--only` working
on it; kernel peak RSS on `calc_text` reported.

*Kill criterion:* the curve's ratio does not fall — i.e. the exponent has
another carrier. Then the round has produced the instrument that finds it
(the emitted term is linear and the counters say where the queries are),
and it stops and reports, keeping stages 1a–1b, which are correct and
independently valuable.

### Stage 3 — the elaborator's transient reduct

§5. Designed after stage 2's numbers, in its own pass.

### Stage 4 — the record (0.3)

§7's document edits; the issue closed or re-scoped with the three tables;
`emit-ty-rewalks-normalized-type` closed into this; the mint's branch
deleted; `docs/nbe-conversion-design.md` §7's "if a metaprogram-heavy
workload ever makes `typing.rs`'s whnf hot, the fix is to move typing to
values too" annotated with the date it happened.

---

## 9.0 Verification items for the implementer's first hour

1. Read `typing.rs`'s `Pair`/`Fst` rules (~1705–1760) and `conv.rs`'s Σ arm
   (~1586) side by side and confirm §3.4's claim on this tree: no
   conversion arm reads `fst_ty`/`snd_ty`. If one does, it is the first
   thing this design got wrong and it changes §2.4's conversion paragraph.
2. Read `rec.rs` ~1705 (`tm_pair`) and confirm `u_a`'s telescope type is
   stated by `U_S`. That is §2.2's whole argument.
3. `grep -n 'fst_ty\|snd_ty\|lhs\b\|rhs\b' crates/kernel/src/eval/*.rs
   crates/kernel/src/conv/dom/values.rs crates/kernel/src/value/*.rs` — who
   reads the annotation closures on `Val::Pair`/`Elim::Fst`. Decides §3.5.
4. Confirm `Tc::whnf` is δ-transparent at every layer (`typing.rs` ~882) —
   the premise `T ⇝* former` relies on it inside a boxed *type*.
5. Count the `Dom` methods `typing.rs` will call that `Values` implements
   non-mechanically (`values.rs` ~23–35) and check each against what the
   nine whnf sites and the 29 `apply_local`s need. If a needed operation is
   missing from `Dom`, the design's "nothing structural" in §3.2 is wrong
   and the addition is the first log entry.
6. Build the before binary now, before any edit, and record it
   (`before-after-binary-provenance`); the worktree has no `probes/`.

---

## 10. Status

Design written 2026-09-20; no code. Owning issue
`elab-emits-normal-form-of-matched-type-argument`; the round's implementer
logs there, per stage, with the §9 gates as the headings.
