# Family types as code definitions — design

Design round for `issues/family-types-as-code-defs.md`, 2026-08-05. The
predecessor (`issues/generated-term-defs.md`, closed 2026-08-04) routed the
generators' *terms* through Ψ definitions and cut the constants 4–7×; what
survived is the emitted **types** — a forded family's `⟦Skel⟧` and its index
type `I` are `Type::Wf`s of Θ(constructors) nodes written out afresh at
Θ(constructors) occurrences (fording doc §14.11, and the before/after table in
`docs/frontend-benchmarking.md`). `GlobalBinding::Ty` has no body
(`crates/kernel/src/term.rs`, the enum near line 1005), so the same lever does
not reach them. This document designs the recorded fix shape — a **code
definition** `D#code : Trm_c(· ⊢ Ty l)` consumed as `El (D#code^δ)` — checks
that spelling against DeLaM ch. 06/07, and draws the reader-migration line.

The headline findings, argued below:

1. **The spelling needs no new kernel machinery at all.** `GlobalBinding::Tm`
   with `ty = Ty l` *is* the code definition; `Type::El` of a `Term::GlobalTm`
   *is* the occurrence. The kernel's conversion was built anticipating exactly
   this ("a type reaches a definition only through `El ν`" —
   `crates/kernel/src/conv.rs`, `delta_head_ty` at line 456 and the doc
   comment on `Conv::ty` above line 604), and the `ElimWf` ι-rule never
   destructures its `shape` annotation (`crates/kernel/src/reduce.rs:567`), so
   an `El`-headed annotation blocks nothing. The issue's "scheme change" is
   real but it is **elaborator-side only** — see §7 for the correction to the
   recorded shape.
2. **The book supports the spelling, and supports *only* this spelling.**
   `El l ν` with `ν = u^δ` is a neutral type form in ch. 06's own WHNF
   grammar; a type-level global `U^δ` has no reduction rule at any layer, so
   an unfoldable type abbreviation *cannot* be spelled any other way. §2 has
   the citations.
3. **The family type itself is not a def.** Only the two Θ(n) components —
   `⟦Skel⟧` and `I` — get codes. The `Σ`/`sEq` shell stays inline: it is O(1)
   once its components are references, it carries the use-site index `m`, and
   keeping it inline is what preserves `forded_of`'s shell fingerprint.

## 1. The spelling

### 1.1 What gets registered, per declaration

Two new `GenDef` variants in `crates/elab/src/gendefs.rs`, registered by
`register_gen_defs` at declaration time exactly as `Mu`/`IdxTag`/`IdxChild`
are today (best-effort, kernel-gated, fallback to inlining):

- **`IdxCode(tag)`** — the index type's code, keyed by the *index* type's
  nominal tag and therefore shared by every family over that index (the
  `IdxTag`/`IdxChild` precedent, §14.9). Statement `Trm_c(· ⊢ Ty l_I @
  1+l_I)`; body `code_of(⟦I⟧)`. Registered **before** the other devices of
  its index type, so their statements can reference it (§1.4).
- **`SkelCode(tag)`** — the skeleton type's code, keyed by the forded
  declaration's tag. Statement `Trm_c(· ⊢ Ty l @ 1+l)`; body
  `code_of(⟦Skel⟧)`. Exists only for an unparameterized declaration — the
  same boundary as `Mu`, §5 below.

**Not registered: the family type `⟦D(m)⟧ = Σ(s : ⟦Skel⟧). sEq(I; μ s; m)`.**
Its two Θ(n) sub-terms are the components; with those spelled as references
the shell is a constant-size wrapper that additionally depends on the
use-site index `m`, so naming it would buy nothing and cost the shell
fingerprint (`forded_of` reads the `Σ`-over-`sEq` shape and the μ name out of
it; a named family type would put an opaque head over the very shape the
recognizer anchors on). This is a deliberate narrowing of the issue's "the
family type itself?" question.

### 1.2 The statement, in the kernel's terms

`Trm_c(· ⊢ Ty l)` is not a new judgment. It is the existing bodied binding

```rust
GlobalBinding::Tm {
    ctx:   LocalCtx::empty(),      // ·
    layer: Layer::Code,            // the c in Trm_c
    ty:    Rc::new(Type::Ty(l)),   // Ty l — the Tarski universe as a Type
    level: Level::succ(l),         // a term of type Ty l lives at 1 + l
    body:  Some(Rc::new(code)),    // code_of(⟦Skel⟧) resp. code_of(⟦I⟧)
}
```

pushed through the existing gate (`gendefs.rs::push_gen_def`: statement
checked at layer p, body checked at layer c, empty local context — the same
two calls a user `fn` passes). Nothing about the gate changes; the only new
thing about these definitions is that their *type* is `Ty l` rather than a
`Π`. Well-formedness is `docs/metatheory-ch07-extensions.md` §23's `(wf-def)`
verbatim, with `T = Ty l` — the rule quantifies over any `T`, so no rule is
added.

The body is `code_of` (`crates/elab/src/code.rs`), which already covers every
former the lowered types use — `TmWf`, `TmSigma`, `TmSum`, `TmSEq`, `TmUnit`,
`TmEmpty`, `TmVec`, `TmFin`, `TmPi`, `TmId` — each arm mirroring one decode
line of `reduce.rs`, so the round trip `El ⌜T⌝ ⇝ T` is checkable by reading
the two side by side. `code_of` is partial; a `None` (it cannot happen for a
lowered skeleton today, but the rule is the same as every `gendefs` piece) is
the cue to skip registration and inline, not an error.

### 1.3 The occurrence

```rust
Type::El { level: l, tm: Rc::new(/* Term::GlobalTm for the def, via gen_ref */) }
```

— composition of two existing constructors (`term.rs:54` for `El`,
`gendefs.rs::gen_ref` for `u^δ`). **No new former.** At layer c the kernel
treats this as a neutral type (it is one — §2); at the computing layers
`whnf_type_delta` δ-unfolds under the `El` (`reduce.rs`, the doc comment "δ
reaches types only through `El`" at ~line 215) and the decode arm at
`reduce.rs:283` turns `El (TmWf …)` back into `Type::Wf` — **lazily**, one
level per step, children still `El`-wrapped, which is the existing decode
discipline `decoded` documents (`crates/elab/src/inductive.rs:320`).

Conservativity is structural: δ of the def followed by full decode yields
*exactly* the inline type the generator builds today, because `code_of` is
`decode`'s syntactic inverse arm-by-arm. Same suite green, same negatives
negative, is therefore the acceptance shape, as in the term round.

### 1.4 Where the occurrence is emitted

The Θ(n)-copies sites, from §14.11's list, all of which are annotation slots
in emitted terms or component slots in emitted types:

- `FordedFam::ty_at`/`eq_at` (`forded.rs:84–115`): the `Σ`'s `fst` and the
  `sEq`'s `ty` become the two references. This is the family type at every
  occurrence — field types, motive instantiations, `forded/occurrences`' 28
  ms per use.
- `Lam` domains and `Pi` domains/codomains the generator writes over `⟦Skel⟧`
  or `I` (eliminator arms, inversion binders).
- `Transp` annotations and motive instantiations in form A/B arms.
- `Supf`/`ElimWf` **annotation slots** (`shape: Rc<Type>` in both,
  `term.rs:514` and the `ElimWf` fields following it): the shape written into
  every constructor value and every eliminator instance. This is safe because
  the kernel never pattern-matches these slots — typing *builds* a `Type::Wf`
  from them and hands the comparison to conversion (`typing.rs`, the
  `Supf`/`ElimWf` cases near 1406), and the ι-rule only clones them
  (`reduce.rs:567–621`).
- The **statements and bodies of the other `GenDef`s**: `μ_D : ⟦Skel⟧ → I`,
  `is_k : I → Ty⁰`, `proj_{k,t} : I → I → I` currently inline both types in
  their own `Pi`s and in their `elim_Wf` bodies. Registering `IdxCode` first
  and `SkelCode` before `Mu` lets those statements shrink too (Ψ is a
  telescope; a later binding may reference an earlier one). This is optional
  per-piece — each is one registration-order constraint, not a coupling.

What is **not** re-spelled: types the elaborator holds for its own structural
reads. That line is §3.

## 2. The book check (ch. 06/07 verdict)

The question the issue posed: is `El (D#code^δ)` — a layer-c code global,
syntactic at c, consumed via `El` at p — a spelling the book's rules already
cover? **Yes, and it is the only one they cover.** The chapters name rules by
display rather than number; citations below are by grammar/rule shape and
source line in the `.tex`.

**The grammar.** Ch. 06 §"Weak Head Normal Forms"
(`06_reduction_and_convertibility.tex:20–38`):

```text
V := U^δ | El_l ν          (neutral form for types)
ν := x | u^δ | …           (neutral form for terms)
```

`El l (u^δ)` is *literally a production of the neutral-type grammar*. Nothing
is being stretched: a type whose head is `El` of a global term variable is a
form the book's algorithm is defined on.

**Reduction.** The type reduction relation (06:55–65) consists of exactly the
`El`-computation rules — `El 0 Nat ⇝ Nat`, `El (1+l) (Ty l) ⇝ Ty l`, the `Π`
rule, and the congruence `t ⇝ t' ⊢ El l t ⇝ El l t'`. Two consequences:

1. A type-level global `U^δ` has **no reduction rule at all** — not at c, not
   at p. The book's types unfold only through `El` of a term. So
   `GlobalBinding::Ty` having no `body` field is not a gap in the kernel; it
   is fidelity to the theory, and "give `Ty` bindings a body" — the naive
   alternative — would be a deviation with no ch. 06 rule to compute it.
   `docs/metatheory-ch07-extensions.md` §24 already states this as an
   invariant: "Type-level bindings stay opaque at every layer … a type
   reaches δ only through `El ν`."
2. The δ-step of a *bodied* term global (Heather's extension, Part IV §24's
   (δ) rule) composes with the book's `El` congruence: at a computing layer,
   `El l (D#code^δ) ⇝ El l (body[δ]) ⇝* W` by rules that are each either
   book-verbatim or already-owed. No new reduction rule is introduced by this
   round.

**Conversion.** For the blocked side (layer c, and the δ-lazy fast path at
p): the neutral-type `El` congruence (06:418–420)

```text
l ≈ l'    ν ≈ ν' : Ty l @ 1+l
──────────────────────────────
El l ν ≈ El l' ν'   (neutral)
```

with its `ν ≈ ν'` premise discharged by the neutral-term global rule
(06:558–560):

```text
u : Trm_{i'}(Δ ⊢ T @ l) ∈ Ψ    i' ∈ {v, c}    i' ≤ i    δ ≈ δ'
────────────────────────────────────────────────────────────────
u^δ ≈ u^{δ'} : T[δ] @ l   (neutral)
```

Note the side condition: the neutral-term rule admits **only layers v and
c** — a layer-c code global is precisely what may stand syntactic at any
layer `i ≥ c`. `D#code` is layer c. The spelling sits squarely inside the
rule.

**Blocking.** The WHNF grammar blocks the code recursors on global variables
(06:35–37: `elim^Typ … (box (U^δ))` and `elim^Trm … (box (u^δ))` are
neutral, "following hu2024layered"), and Part IV §24 keeps bodied globals
blocked there too (δ never enters a `box`; `box(u^δ)` compares
syntactically). A `D#code` that a meta-program boxes and inspects therefore
stays a name at layer m's recursors — the coherence argument of Part I §6
run one level down, which is exactly bill item 2 of
`issues/metatheory-ch07-definitions.md`. Nothing new.

**What ch. 07 is owed.** The obligation this round adds to
`issues/metatheory-ch07-definitions.md` is one *case site*, not one *kind*:
the LR's type interpretation at `El l ν` gains the same defined/undefined
split on `ν`'s head that bill item 1 ("definitional glueing at p") already
prescribes for term-level neutrals — at p/m the interpretation of
`El l (u^δ)` for bodied `u` goes through the body via the `El` congruence
reduction; at c it is the neutral interpretation, unchanged. Items 2–4 of
the bill (coherence across `□`, the FT `u`-cases, termination of δ) cover
the new definitions verbatim, because a `D#code` is checked and registered
exactly as any bodied global (§1.2). The issue's log line for this round
should say: *El-of-defined-global is glueing item 1 instantiated at the
type interpretation's `El` case; no new obligation kind.*

**Verdict**: the recorded spelling is what the book supports, and the design
adopts it unchanged. The one place the issue's text needs correction is not
the spelling but the migration surface — §7.

## 3. The reader migration

The crux the charter asks for: the line between "built inline, then
registered" and "read back later". First, a correction of scope: the four
named readers — `spine`, `build_elim_wf`, `const_elim_wf`, `tag_of` — live in
the **elaborator** (`crates/elab/src/inductive.rs:1152/1185`,
`crates/elab/src/wf.rs:291/805`), not the kernel. The kernel's own
`Type::Wf` consumers are total walks and post-whnf view code that need no
migration at all (§3.3). The migration is an elaborator concern.

### 3.1 The line

**Generator-side (sees inline types, unchanged):** `lower_instance` keeps
building the inline `Type::Wf`; `FordedFam` keeps carrying the inline
`skel_ty`/`ity` (and `Tel::d_ty` likewise); every structural read the
generator does against its *own* freshly-built types — `spine` at
declaration time (`inductive.rs:1022`, `gendefs.rs:301`, the
`forded.rs`/`indexed.rs` lowering calls), `build_elim_wf`'s and
`const_elim_wf`'s `let Type::Wf { … } = …` destructurings, the four inline
rebuild sites (`forded.rs:635/941/1583`, `indexed.rs:1174`) — operates on
the inline copy and does not change. The rule: **structure is read from the
inline type; the reference spelling exists only in what gets *emitted*.**
Concretely `FordedFam` grows a pair of optional reference spellings
(`skel_ref`, `ity_ref`, populated from the registry when the defs exist),
and the emission helpers (`ty_at`, `eq_at`, the `Lam`/`Transp`/motive
builders) use the reference when present, the inline type otherwise —
`gen_ref`'s `None`-means-inline contract, extended to types.

**Consumer-side (reads back a type that may now be a reference):** the
recognizers and any reader of a use-site type.

- `forded_of` (`forded.rs:202`): the shell read is untouched (the `Σ`/`sEq`
  arrive inline by §1.1). Its **components** change: `fst` is now
  `El (SkelCode^δ)` where it used to be a `Wf`, so the `tag_of(&fst)` hop
  fails. The repair is the term round's, verbatim: a **nominal branch** —
  `El` whose code is a `GlobalTm` resolving through `gen_def_of` to
  `SkelCode(tag)` identifies the declaration by tag, and *nothing else
  does* (an `El` of any other global, or of a hand-assembled look-alike
  code, is `None`). Where no def exists (parameterized family), the
  structural read stands, name check skipped — the §14.12 coexistence rule,
  extended.
- `tag_of`/`spine` at use sites (`elab_match` at `lib.rs:2076`, `infer_ctor`
  at `inductive.rs:1317`, `equation`, `record_of`): these already whnf first
  through the δ-transparent `Elaborator::whnf` (`lib.rs:4142`), so they
  keep working with **no code change** — the unfold+decode re-materializes
  the inline type. Two costs to record: (a) the elaborate-phase pays a
  decode per read (bounded; the gate is 94–99% of the time, the elaborate
  phase 1–6%); (b) a whnf'd copy re-embedded into emitted annotations
  **re-inlines the Θ(n) type into the output** — the re-spell question,
  §3.2.
- `decoded` (`inductive.rs:337`) is deliberately **not** taught to δ-unfold.
  Its contract ("an `El` of a neutral code is left exactly as it is —
  unfolding that is conversion's job") is what keeps it context-free and
  cheap; the nominal branch in the recognizers is the designed path for
  def-headed `El`s, and `decoded` growing δ would silently reintroduce the
  credulous structural read the fingerprint round closed.
- `code_of` (`code.rs:32`) already treats `El` as the identity on codes, so
  a reference-spelled type *quotes back to the reference* — a type argument
  mentioning `⟦D(m)⟧` gets the small code for free. No change.
- `unify_ty` (`lib.rs:4627`) matches `Wf` against `Wf` syntactically and
  only "learns"; a reference-spelled side simply teaches nothing, which is
  the status quo for route 1's `El (elim …)` domains already (fording doc
  §14.7's note). Not a regression; recorded, not repaired.

### 3.2 The re-spell question (open decision)

`elab_match` whnfs the scrutinee's type and hands the result to
`build_elim_wf`, which writes annotation types into the emitted `ElimWf`. If
the whnf'd (hence re-inlined) `Wf` flows into those slots, a `match` at a
use site still emits Θ(n) annotations and the win shrinks to the
declaration-side sites. The fix is a `respell` step: after whnf, if
`tag_of` identifies the type and the registry holds its `SkelCode`, swap the
annotation copy for the `El`-reference before emission (a lookup, not a
search — tag → def → `gen_ref`). Whether phase 2 needs it, or whether the
declaration-side sites already move the slopes, is a **measure-first**
question; the phasing (§8) puts it behind its own measurement. What is not
optional: `FordedFam`-mediated emission (the majority of sites) uses the
reference natively and needs no respell.

### 3.3 The kernel: no migration

Verified against the source rather than assumed:

- **Typing** never pattern-matches a `Wf` read back from elsewhere. The
  `Supf`/`ElimWf` rules build `Type::Wf` from the term's own annotation
  slots and hand scrutinee agreement to conversion (`typing.rs` near 1406);
  `El`-headed annotation slots check by the `El` formation rule and convert
  by δ.
- **Reduction**: the ι-rule fires on the *scrutinee* being `Supf` and only
  clones `shape`/`arity` (`reduce.rs:567–621`); `step_type_delta` is the
  decode engine itself. Nothing blocks.
- **Conversion** was built for this: `delta_head_ty` (conv.rs:456) — "a
  type is δ-stuck only under `El`" — feeds the δ-lazy same-head fast path
  (`Conv::ty_w`, conv.rs:626–637), so two occurrences of the same family
  compare **without unfolding** (spines first, unfold only on failure —
  Part IV §25's order). Occurrence-vs-inline (the declaration's own gate)
  unfolds once per comparison, which is the bounded case. The
  `has_defs` gate (conv.rs) already exempts def-free programs from paying
  anything.

## 4. The §14.3 seam after this change

§14.3 today: "a `μ` that arrived reduced at a literal index is
unrecognizable and takes the same re-synthesis fix if something hits it" —
pre-*reduced* family types are diagnosed, not handled. After this round the
seam has a second axis: a family type can arrive pre-**unfolded** (something
whnf'd the `El`-reference back to the inline `Wf`) or partially decoded
(`Wf` with `El`-wrapped children mid-decode, the lazy-decode shape).

The design makes the first case *free*: because unfolding is conservative
(§1.3), a pre-unfolded occurrence is exactly today's inline type, and the
structural read — which stays in place as the no-def fallback — recognizes
it. That is the two-sided coexistence the term round already ships for `μ`.
The partially-decoded case is `decoded`'s bread and butter for canonical
formers and remains diagnosed for neutral heads, unchanged.

What the diagnosis surface *becomes*: the failure mode "not a forded
family" can now additionally mean "an `El` of a global that is not the
registered code" — including the look-alike direction (§6.3's discipline: a
different declaration's `SkelCode`, or a user-written global whose body
happens to equal the code, must **not** read back as `D`). The negatives in
`forded.rs mod fingerprint` grow the El-headed analogues of
`a_structural_look_alike_is_not_the_family` (§7). The error message for a
stuck read at a forded family should name the possibility, per §14.5's
precedent on conversion errors.

## 5. The parameterization boundary (§14.12)

The rule extends verbatim, because it is the same rule: **a definition is
registered at declaration time and must be closed.** `⟦Skel⟧` of a
parameterized family is monomorphized per instantiation (`Cx::tyvars`), so
`SkelCode` is not one code but one per instantiation — `Tree<A>`'s skeleton
type is *not* a code def, exactly as its `μ` is not a term def. Abstracting
over the parameter would put a `Π` over `Ty` in the statement and a spine at
every occurrence; that stays out of scope for the same reason §14.12 gives,
and the measured proportion (one parameterized forded family in the suite
against twenty not, and it is small) still says the boundary is cheap.

`IdxCode` has **no** such boundary: index types are unparameterized by
`inductive.rs`'s own rule (the same fact that makes `IdxTag`/`IdxChild`
closed for every family), so every declared index gets its code. This
matters for `forded/declared-index-tags`, whose swept quantity is the index
type's constructor count — the family that owns the residual 2.61 needs only
`IdxCode`, which has no exclusions.

Coexistence is the existing mechanism extended: `forded_of` skips the
`SkelCode` nominal check where no def exists and falls back to the
structural read, exactly as it skips the `μ_D` name check today
(`forded.rs:222–228`). One new fingerprint concern, inherited from the term
round's second direction: a parameterized family's *structural* read must
not accept another family's `El`-reference components — pinned by a negative
(§7).

## 6. Route 1 (§10.3)

Route 1's family is `El (elim_Nat/Case/elim_Wf(_. Ty l; …) i)` — the family
*is* a type-valued eliminator, and the term round recorded that no
per-declaration term existed to name. The code-def scheme names one: the
**family function**

```text
D#fam : Trm_c(· ⊢ Π(i : I). Ty l @ l_I ⊔ (1+l))  :=  λ(i : I). elim(… ; i)
```

— again the existing `GlobalBinding::Tm` form, registered through the same
gate, with the occurrence spelled `El l (D#fam^δ @ i)`. `delta_head_ty`
reaches it (its `El` arm delegates to `delta_head`, whose `App` arm walks to
the head — conv.rs:446–449), so the same-head fast path covers
occurrence-vs-occurrence; unfold + β + decode recovers today's inline type.
The boundary is §5's: unparameterized indexed families only (`len<A>`'s
family stays inline), and route 1's families are *rebuilt from
`Inductive::index_ty` at every use* (route-1 doc §10.6), which the def makes
cheaper but does not restructure.

`indexed_of` **must** be re-keyed in the same motion, and the issue is
explicit that route-1 §10.1's recognizer needs the look-alike negative
discipline: today it is a large structural fingerprint over three head
shapes with a fueled tag *search*, exactly the "any normalizing pass breaks
it silently" seam its own entry records — and this round is that pass. The
re-key is the `forded_of` template: where `D#fam` exists, the family form is
`El` of *that global* applied to the index, and nothing else; where it does
not, the structural search stands. `forded.rs mod fingerprint` is the
template for the negatives, including the second direction (nominal identity
alone is insufficient — a term round's lesson: the look-alike test builds
the forgery out of two real declarations differing only in tags).

Whether route 1 lands in the same implementing round or a successor is a
coordinator decision (§9); the design covers both, and nothing in §1–§5
depends on it.

### Landed 2026-08-06 (phase 5)

Everything above is what shipped, with three corrections and one finding.

- **`GenDef::Fam(tag)`**, `D#fam := λ(i : I). elim(…; i)` at
  `Trm_c(· ⊢ Π(i : I). Ty l)`, registered through the unchanged gate for an
  unparameterized route-1 declaration at all three head shapes (`elim_Nat`,
  a `Case` tree, `elim_Wf`). The two-pass level computation runs **once, at
  declaration time**, and the pair `(l, l_I)` is kept in the registry
  because an occurrence needs `l` to spell its `El` — sound only because a
  definition exists only where `args` is empty, so the declaration has one
  answer forever (§5). Route-1 declarations at a *declared* index also get
  that index type's `IdxCode`, which the `Π`'s domain annotation then takes
  by reference (§1.4); the index type's tag predicates and child
  projections are **not** registered for them, being route-2b inversion
  machinery route 1 never emits.
- **Emission** is one site — `lower_indexed_instance` returns
  `El l (D#fam^δ i)` where the definition exists and falls through to the
  two passes where it does not.
- **`indexed_of`** gained the nominal branch *in the same commit*, and the
  fueled structural search stayed, because two things still arrive in the
  old spelling: a parameterized family and a pre-unfolded occurrence.
  Negatives in `crates/elab/src/indexed.rs`'s `mod fingerprint`.

**Correction 1 — §9's numbers were reading the wrong family.**
`forded/declared-index-tags`, the row §9 called "the pure measurement of
this design" and whose immovable 2.61 the 2026-08-05 round attributed to a
third defect in the `Supf` shape slots, is **not a forded family**. `Tw`'s
constructors state pattern indices, and `classify_indexed_route` tries route
1 first, so it has never had a skeleton, a `μ` or a form-A inversion. It is
route 1 at a declared index. That is why two rounds of forded levers left it
flat, and why this round moved it at once: **2.79 → 2.22, and 2.5× off the
constant at 6 index constructors.** The design's own claim ("slope below
2.0… if the slope does not move, the residual is a *third* defect and this
round's job is to say so") was therefore right about the method and wrong
about the subject — the honest reading is that the third defect was never
demonstrated by this family at all, and
`issues/wf-shape-annotation-slots.md` now rests on
`forded/declared-index-branching` alone.

**Correction 2 — the route-1 win is a constant, not an exponent.** The new
`indexed/arms` fixture, measured against its own registration-only build:
**2.20 → 2.25** with the constant ~1.10× better. §6's "the def makes that
cheaper but does not restructure it" is exactly what happened. What stays
Θ(n) per arm is the *class* type, which no definition names — the route-1
analogue of the shape-slot residual, recorded at route-1 doc §10.3.

**Correction 3 — the baseline was not re-recorded.** `--check` was already
red on master before this round (prelude 2×, `declared-index-branching`
1.3–2.1×, `meta` 1.3×, all from commits after the baseline's), and the
machine was not quiet (load 5–7, 95 °C, untouchable families drifting
1.5–2× between runs an hour apart). Bands were tightened in the fixture
sources around the measured exponents; the baseline file is untouched and
`indexed/arms` stays `untracked` until a quiet-machine re-record.
`docs/frontend-benchmarking.md` has the tables and the reasoning.

**Finding, unrelated to this round's lever but found by its fixture.** A
route-1 family whose index classes do not all reach the family's join level
is rejected by the kernel (`LevelMismatch`) at every use, on master and
after. Every nonzero-level fixture in the tree hid it by giving *every*
constructor a `Type`-valued field. Written up with the reproducer at
route-1 doc §10.5; it needs its own round.

## 7. What this amends elsewhere

Contradictions with the recorded fix shape, flagged per the round's rules:

1. **Issue text and §14.11: "every structural reader of `Type::Wf`
   (`spine`, `build_elim_wf`, `const_elim_wf`, `tag_of`) would have to go
   through `decoded`/whnf first" — overstated, and mislocated.** Those four
   readers are elaborator code, not kernel code; the kernel needs no
   migration at all (§3.3 — verified against `typing.rs`, `reduce.rs`,
   `conv.rs`, which were built annotation-oblivious and δ-aware
   respectively). And the elaborator migration is not "everything whnfs":
   the generator-side readers keep their inline types (§3.1's line), the
   whnf-first consumers already work unchanged, and only the recognizers
   gain a *nominal branch* — a lookup, not a reduction. The scheme change
   the issue predicted is real but its surface is roughly `forded_of` +
   `tag_of`'s El case + `indexed_of`, not the four-reader list.
2. **§14.11's "the family type itself?" — answered no** (§1.1): components
   only. The fording doc's §14.11 entry should be updated at landing to
   record the narrowing and the reason (shell fingerprint preserved, O(1)
   anyway).
3. **§14.3 grows as predicted but gains a free case**: the pre-unfolded
   direction is conservative and falls back to the structural read (§4);
   the genuinely new diagnosis surface is El-of-the-wrong-global.
4. **`issues/metatheory-ch07-definitions.md`**: gains one instance-site
   note, not a new obligation kind (§2's last paragraph). The 2026-08-04
   scope note in that issue asked exactly this question; the answer is
   "glueing item 1 at the type interpretation's `El` case".
5. **Route-1 doc §10.1/§10.3**: both entries are superseded at landing —
   §10.1's "whichever round does route 1 re-keys it" is this design's §6,
   and §10.3's "a kernel `def` is the eventual fix" resolves to the family
   function def.

## 8. Phasing

Each phase is independently checkable and independently abandonable; the
best-effort discipline (a failed registration inlines as before) holds
throughout, so no phase can regress correctness — only fail to improve.

1. **Registration only.** Add `GenDef::{IdxCode, SkelCode}`, build bodies
   via `code_of`, push through the existing gate; ordering: `IdxCode`
   before the index devices, `SkelCode` before `Mu`. No emission change.
   *Checkable:* suite green unchanged (931), defs visible in Ψ, `--check`
   green — a pure no-op measurement point that proves the gate accepts the
   statements.
2. **Forded emission.** `FordedFam` carries `skel_ref`/`ity_ref`; `ty_at`,
   `eq_at`, and the annotation builders emit references where defs exist.
   Simultaneously the recognizer re-key (`forded_of`'s nominal component
   branch) — these cannot be split, because the moment emission changes,
   the old component read fails, which is the term round's lesson about
   landing the pass and the re-key together. New fingerprint negatives
   land here (§7's list below).
   *Checkable:* suite green; `scripts/bench-frontend --check` — expect
   `forded/declared-index-tags` and `forded/computed-arms` to leave their
   bands *downward* and go red on exactly them; `--save` re-records;
   before/after table appended to `docs/frontend-benchmarking.md`.
3. **Measure the re-spell question** (§3.2): if `forded/occurrences` or the
   match-heavy fixtures did not move as predicted, add the whnf-then-respell
   step at `elab_match`'s hand-off and re-measure. If phase 2's numbers
   already answer, record that and skip.
4. **Retro-spell the term defs' own statements** (§1.4 last bullet):
   `μ_D`/`is_k`/`proj` statements and bodies reference the codes. Small,
   separable, same conservativity argument.
5. **Route 1** (§6): `D#fam` defs, `indexed_of` re-key with its own
   negatives, ideally its own bench row (route 1 currently has no swept
   family in the suite — adding one is part of this phase's acceptance, or
   an explicit decision not to).
   **Landed 2026-08-06** — defs, re-key, five negatives/positives in
   `indexed.rs`'s `mod fingerprint`, and the bench row (`indexed/arms`).
   Measured: `indexed/arms` 2.20 → 2.25 with ~1.10× on the constant, and
   `forded/declared-index-tags` — which turns out to be route 1, §6's
   landing note — 2.79 → 2.22 with 2.5× at the wide end. Suite green, whole
   `scripts/test`, no baseline re-record (§6's correction 3).

No kernel flag is needed at any phase — phase 1 having no emission is the
"scheme first, behind nothing" step, and the kernel is unchanged throughout.

## 9. Acceptance criteria, and open questions

### Numbers (baseline 2026-08-04, `crates/elab/benches/baseline.tsv`)

- `forded/declared-index-tags`, slope **2.61**: the swept quantity (index
  constructor count) multiplies only the emitted *type* after the term
  round, so this family is the pure measurement of this design. Predicted
  direction: toward linear; the claim worth gating is **slope below 2.0**,
  with the honest caveat that the last round's headline prediction was
  wrong in exactly this spot — if the slope does not move, the residual is
  a *third* defect and this round's job is to say so, not to absorb it.
- `forded/computed-arms`, slope **2.79**: arms multiply both the types and
  the per-arm eliminator work; removing the type factor should move the
  exponent visibly (the term round's 3.39 → 2.79 was the other factor).
  Predicted direction: down, magnitude uncommitted.
- `forded/occurrences`, **~28 ms per use**: each mention emits an O(1)
  family type instead of Θ(n); predicted direction: down severalfold, slope
  ~1.0 unchanged.
- `forded/declared-index-branching` (1.53) and `lib/ir_v1.hthr` (budget
  150 s): must not regress; no claim of improvement.
- Re-record on a quiet machine per the noise warning; slopes are the
  headline, absolutes are context.

### Tests

- Whole suite green; every existing deliberate negative stays negative.
- New negatives (the look-alike discipline, `forded.rs mod fingerprint` and
  a sibling in `indexed.rs` for phase 5):
  - `El` of the *wrong* declaration's `SkelCode` in the `Σ`'s first
    component is not family `D` (two real declarations, tags swapped — the
    existing look-alike test's construction, El-headed).
  - `El` of a user-written bodied global whose body is byte-identical to
    `D`'s code is not `D` (identity is the Ψ index, not the body).
  - A parameterized family's structural read does not accept another
    family's `El`-reference components (the §5 coexistence negative).
- New positives:
  - A pre-unfolded occurrence (whnf'd back to the inline `Wf`) still
    recognizes and checks — the §4 conservativity case.
  - The four axes of `docs/testing-generated-terms.md` on at least one
    fixture that crosses the new spelling: neutral *and* literal scrutinee,
    an open element type, a checking position, nonzero level (the
    `fields_above_level_zero` discipline — route-1 §10.5's rule, which
    already caught a bug hiding under `El` of a quoted code once).

### Seams the implementing round re-reads first

Fording doc §14.1, §14.3, §14.12; route-1 doc §10.1–§10.3;
`docs/testing-generated-terms.md`; `metatheory-ch07-extensions.md` Part IV.

### Open questions for the coordinator

1. **Re-spell on emission** (§3.2): accept the measure-first plan (phase 3
   contingent), or mandate it in phase 2?
2. **Route 1 scope**: same round or successor? If same round, does it add a
   swept route-1 bench family (there is none today, so route 1's win would
   otherwise be unmeasured)?
3. **Retro-spelling the term defs' statements** (phase 4): worth its
   registration-order coupling, or defer until a fixture shows the
   statements themselves matter? (They are Θ(n) each but appear once per
   declaration, not per occurrence — plausibly below the noise floor.)
4. **Band placement** for the re-recorded slopes: the suite's convention is
   "record the exponents that exist, not the ones the design wants" —
   proposed: tighten around whatever phase 2 measures, with
   `declared-index-tags`'s band top at 2.0 as the standing claim.
