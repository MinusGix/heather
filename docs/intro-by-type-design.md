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
- **`typing.rs`:** becomes generic over the `Dom` boundary the way `conv.rs`
  is; `Values` is the production instantiation, `Syn` is the differential
  oracle. Inferred types become domain objects (§3). This is the stage
  `docs/nbe-conversion-design.md` §7 deferred as "cold"; it is 57 % of the
  gate now.
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

### 2.1 Syntax

Five term formers, valid at layers p and m only (§2.3):

```
pair@^{l}(T; a; b)        infer: T,    where  T ⇝* Σ^{l₁,l₂}(x:S). U,  a : S,  b : U[a/x]
inl@^{l}(T; a)            infer: T,    where  T ⇝* A +^{l₁,l₂} B,        a : A
inr@^{l}(T; b)            infer: T,    where  T ⇝* A +^{l₁,l₂} B,        b : B
fst@^{l}(T; p)            infer: S,    where  T ⇝* Σ^{l₁,l₂}(x:S). U,  p : T
snd@^{l}(T; p)            infer: U[fst@(T;p)/x],  same premises
```

`T : Ty l` is the one annotation; `l` is `T`'s level and is what `ty_infer`
returns for it, so the form carries no level field of its own. The premise
`T ⇝* former` is the checker's whnf (δ-transparent for types at every layer,
as `Tc::whnf` already is — "a type lives at `typeof(i)`, which is always a
computing layer"). The inferred type of `pair@`/`inl@`/`inr@` is **`T`
itself, un-reduced**, not the former: that is what keeps every consumer of
the inferred type lazy in δ, which the kernel's conversion already is.
`fst@`'s inferred type is the component `S` and `snd@`'s is `U` at
`fst@(T;p)` — these have **no syntax spelling**, and §3 follows from that.

Rust: `Term::PairAt { ty: Rc<Type>, fst, snd }`, `InlAt`, `InrAt`,
`FstAt { ty, pair }`, `SndAt { ty, pair }`. Names are the implementer's;
the doc comments should say "checked spelling of `Pair`" and point here.

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

### 2.3 Layer restriction, and why it costs nothing

`pair@` and its siblings are refused at layer c and v (a `computing_layer`
guard beside `not_var_layer`). Consequences:

- The code grammar — what a `box` may contain and what the 56 recursor
  branches range over — is unchanged. No branch is added, no telescope
  changes, `BRANCH_NAMES` is untouched, the surface `match code` language
  (`crates/elab/src/quote.rs`, `crates/syntax/src/ast.rs`) is untouched.
- `code_eq` never meets the new forms. Preservation for the code recursors'
  β (`reduce.rs` ~1571) is untouched, which is what refuses the alternative
  in §6 item 5.
- The elaborator already knows the layer at every emission site (`cx.layer`);
  the switch is one predicate at each of the ~4 emitters in §4.1. Inside a
  quotation the component forms continue to be written, with whatever
  reduct that costs — quoted code is the x86 line's IR terms, not the
  parser tower, and if a tower ever appears under a `box` it is a separate
  finding.

### 2.4 Conservativity

Define the translation `⌊·⌋` on well-typed computing-layer terms:
`⌊pair@(T; a; b)⌋ = pair(x:S. U; ⌊a⌋; ⌊b⌋)` where `T ⇝* Σ(x:S).U` is the
whnf the typing derivation contains (Determinacy makes it unique up to the
budget), and likewise for the other four; identity elsewhere. Then:

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
- **Layer c.** Nothing. The formers do not exist there.

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

## 3. The checker moves to values

### 3.1 Why this is forced, not chosen

`fst@(T; p)` infers `S`, the first component of `T`'s whnf. With the
rewriter that is a *syntax* — the substitution-expanded component, i.e. the
exponential object, built in the kernel this time, which is
`projected-tuple-tower-design.md` §5 F's first objection ("the kernel would
then build the same reduct in *its* rewriter") and it is correct. With the
evaluator it is a `TyClo` — one closure, no copy. But the checker's
`tm_infer` returns `(Type, Level)` today, so a value-typed inferred type has
nowhere to go. A hybrid (`enum { Syn(Type), Val(VTy) }` threaded through
51 arms) is the single most error-prone shape available and is refused
(§6 item 6). The uniform migration is the safe one, and it has a template.

### 3.2 The template: `conv.rs`'s `Dom`

`conv.rs` is one text over `trait Dom` with two instantiations —
`dom::values::Values` (production) and `dom::Syn` (the rewriter, the
oracle) — and `tests/conv_differential.rs` runs both over six seeded
streams of `tests/common/wt.rs`'s well-typed generator, reporting seeds only
(`OutOfFuel` from either side is "no answer", never a disagreement).

`typing.rs` becomes `Tc<D: Dom>`: inferred types are `D::Ty`, Γ carries
entry types as `D::Ty` past the syntactic prefix (conv's `Env` already has
exactly this — `rho`, `vtys`, `vbase`), the nine `Tc::whnf` sites become
`D::whnf_ty_root` + `TyView`, the 29 `apply_local` and 21 `shift_local`
become `D::inst_ty` and free weakening, and `Tc::conv_ty` compares two
`D::Ty` in one arena instead of re-entering the value domain from syntax
per query with a fresh arena (`conv.rs` ~209–243 — the per-query arena
`docs/conversion-query-arena-pooling-design.md` §3 already names as the
structural cost). `Tc<Syn>` is the current checker up to refactor, and it is
the oracle.

What `Dom` lacks that typing needs, and must gain: nothing structural. The
operations are a subset of conversion's — evaluate a syntax type in the
current ρ, view its head, instantiate a closure at a value, push a binder
with a domain object, compare two domain types. `values.rs` ~23–35 lists
where its instantiation "stops being mechanical" (`var_type`, `inst_ty`,
`under_tele_*`, `wf_step_telescope`, the two motive instantiators); typing
reuses those, it does not add to them.

### 3.3 Rules under values, the four that matter

- **`pair@(T; a; b)`:** `ty_infer(T) = l`; `v = D::whnf_ty_root(T)`;
  `TyView::Sigma { fst, snd }` else `HeadMismatch`; `tm_check(a, fst)`;
  `tm_check(b, D::inst_ty(snd, [eval a]))`; return `(eval T, l)` — the
  *un-reduced* `T` as a value, i.e. a glued neutral whose unfold is memoized
  (`VNeutral.unfold`), so a consumer that converts it against a former pays
  one δ step and a consumer that converts it against another `T` pays a
  head comparison.
- **`fst@(T; p)`:** as above to the view; `tm_check(p, v)`; return `(fst, l₁)`.
  Note `tm_check(p, v)` converts `p`'s inferred type — for a `pair@` that is
  its own `T'` — against `v`, the *former*; δ-lazy conversion unfolds `T'`
  one step. That is the one place per node where the tower's type is
  computed, and it is computed once per closure by the memo.
- **`snd@(T; p)`:** return `(D::inst_ty(snd, [eval(fst@(T;p))]), l₂)`.
- **`app`** (unchanged rule, changed cost): `tm_infer(fun)` → `TyView::Pi`;
  the annotations `dom`/`cod` are `ty_check`ed and the rebuilt Π converted
  against the inferred one as today. This is the 36 % constant factor of
  `conversion-typed-eliminator-congruence`; it stays a constant factor over
  a term that is now linear, and it is **not** taken here, for the reason
  that issue records.

### 3.4 What does not move

- **`conv.rs`'s arms.** None reads an intro's or a projection's annotation.
  The new forms add `TmView` variants (or reuse: a `pair@` value *is* a pair,
  see 3.5) and `Elim` variants for the neutral projections; the typed
  projection arm (`conv.rs` ~2179) reads the head's inferred Σ, so
  `fst@`-on-a-neutral converts exactly as `fst` does.
- **`reduce.rs`.** Gains the β arms (`fst@`/`snd@` on either pair; `case` on
  `inl@`/`inr@`), the neutrality predicate, the whnf grammar lines, and —
  since it is ch. 06's transcription and the oracle — the same layer guard.
  The code-recursor β at ~1571 is untouched: it never meets a `pair@`.
- **`rec.rs`.** Untouched. Zero new branches.
- **`subst.rs`, `bounds.rs`, `fmt.rs`, `merkle.rs`, `module_image.rs`**:
  the mechanical transcription for five new variants, one annotation slot
  each, no binder in the slot (`snd_ty` bound one; `T` binds none — this is
  a simplification everywhere the walkers used `under(1)`).

### 3.5 The value representation — an implementer's decision, flagged

`Val::Pair` / `Val::Inl` / `Val::Inr` and `Elim::Fst` / `Elim::Snd` carry
the *annotation closures* (`value.rs` ~1441, ~1710). The evaluator maps a
`pair@` onto a pair value; the question is what goes in `fst_ty`/`snd_ty`.
Options: (a) a `TyClo::Syn { env, T }` for the whole type in a new
`annot` field with the component slots absent; (b) a separate
`Val::PairAt`. The decision turns on **who reads those closures**: the
first-hour item §9.0.3 is the grep. If conversion and the native fast paths
(`eval/bits.rs`, `eval/transduce.rs` pattern-match `Val::Pair`) read only
`fst`/`snd`, (a) with the slots as an enum is the smaller change; if the
readback devices are the only readers, they are being deleted (§4.4) and
the slots can go.

### 3.6 Fuel, depth, and the arena

Eval's fuel and `NATIVE_DEPTH_LIMIT` apply unchanged. One `ValueArena` per
gate call (per declaration), not per query: the arena's lifetime becomes
the checker's, and the memo caches persist across the declaration. The
address-space rail (`ulimit -v`) is the measurement of whether that
retention is acceptable; §9 stage 1's gate includes peak RSS on the routine
corpus, and the pooling design's numbers are the comparison.

---

## 4. The elaborator's emission

### 4.1 The emitters that change

All in `crates/elab/src`, all with the un-reduced type in hand (the
2026-09-20 survey, on the issue):

| site | writes | un-reduced type available as |
|---|---|---|
| `inductive.rs` `inject` (~606), via `build_ctor` | `Inl`/`Inr` chain | `pre_whnf` (~2116), live through the function |
| `inductive.rs` `build_fields_skel` (~2382) | the Σ tuple | `ctor_ty`, the argument, whnf'd at ~2310 |
| `forded.rs` `build_fields_collect` (~1050) | the forded tuple | `ctor_ty`, same shape |
| `inductive.rs` `projection` (~2860–2935) | `Fst`/`Snd` with `cur_emit` | the receiver's inferred type, which the `behind_a_name` branch already threads |

Each gains `if cx.layer.computes() { …At { ty: emit_ty(pre_whnf) … } } else
{ today's form }`. `emit_ty` still runs on `T` — it is the chokepoint that
respells a registered lowering as its reference, and `T` is small — but it
no longer walks a reduct (`emit-ty-rewalks-normalized-type` closes into
this as a consequence, not a fix). `spine` and the whnf that feed field
*checking* stay exactly as they are in this stage: the elaborator still
computes the reduct to decide the constructor and to check the fields
against inline components. That is stage 3's subject (§5).

`wf.rs` `fin_index` (~1762) already annotates a tail "with `Fin` itself
rather than its unfolded sum"; it is the closest existing precedent and its
comment is the rationale to reuse.

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
  smaller invariant.
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
fired items). `emission_walk.rs` stays: it is the auditor.

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
6. **A hybrid checker** whose inferred types are `Syn | Val`. 51 arms each
   handling two cases, no oracle instantiation for free, and the failure
   mode is a soundness hole in the trusted core rather than a mismatch. The
   generic `Tc<D>` has the oracle built in.
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

**Kernel cost.** Stage 1 is the migration of a 2770-line trusted file to
the `Dom` boundary. It is the exact shape of `nbe-conversion-design.md`'s
stage 2b, which was 1852 lines and landed. It is mechanical in the same
way (arms rewritten one-for-one, inputs become domain objects) and
differential-tested in the same way. Nothing can make it small; the
containment is that a mistake is a *disagreement with `Tc<Syn>`* on a
generated well-typed term, reported by seed, and not a silent acceptance.

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

1b. `typing.rs` → `Tc<D: Dom>`; `Tc<Values>` wired as the gate;
`typing::oracle::{check_term, infer_term, check_type}` = `Tc<Syn>`;
`tests/typing_differential.rs` over `wt.rs`'s streams, both Ψ and
`opaque(Ψ)`, ≥ 4 seed streams, seed-only reporting, `OutOfFuel` not a
verdict. `wt.rs` gains generators for the five forms (an `@` form is
generated from a generated component form by wrapping its former).

*Gate:* full `scripts/test` green including `tests/typing.rs`'s golden
suite, `ch05_06_lemmas.rs` (the identity-recursor proxy must be unchanged —
it never sees an `@`), `conv_differential.rs`, `eval_differential.rs`;
`typing_differential.rs` green; `scripts/bench --check` (expect movement:
the per-query arena is gone; re-save with the verdict recorded);
`lib/ir_v1.hthr` and the routine corpus not regressed in seconds or peak
RSS (§3.6); the x86 certificate gates green under their existing fuel.

*Kill criterion:* a typing-vs-typing disagreement not traced to a
*rewriter* bug within one session → revert 1b, keep 1a (the forms are
inert without an emitter and the syntax checker accepts them), re-scope.
This is `nbe-conversion-design.md` stage 2b's criterion, verbatim.

### Stage 2 — the emitters (0.5)

§4.1's four sites behind the layer predicate; §4.2's readers walked, each
answered in the log; §4.4's deletions; `emission_walk.rs` arms.

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
