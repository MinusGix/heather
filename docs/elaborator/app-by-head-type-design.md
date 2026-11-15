# Applications typed by their head — design

Design pass on `issues/elab-emits-normal-form-of-matched-type-argument`'s
2026-09-22 attribution, the successor of `docs/elaborator/intro-by-type-design.md`
(stages 1–2 landed). Written in that document's discipline: decisions with
rationale, rejected alternatives priced, the implementer's stages and gates
at the end (§9). Coordinator-written after discussion with the user
(2026-09-22); an implementer executes §9.

The finding, in one sentence: after stage 2, **91 % of `calc_text`'s
semantic image is application annotations** — `App.cod` 264 M and
`App.dom` 67 M nodes of a 362 M tally, measured by the image writer's own
counter (`HEATHER_IMAGE_ATTRIBUTION`, commit 0a4004c) — because every node
of an application spine `f a₁ … aₙ` stores the remaining Π with the
earlier arguments substituted in, so every argument value is spelled again
in every later annotation, and an argument that is itself an application
brings its own annotations along. On a probe, one `Cons(x, r)` at
`List<Char>` is 1 056 nodes and a two-step `calc` over it is 19 370, of
which 13 704 are application annotations: the endpoint value is spelled
about seventeen times. Constructor values — stage 2's subject — are now
under 5 %.

The move is stage 2's, one former over: **an application that carries no
type at all**, whose Π is read off the type its head infers. The checker
already has everything this needs except one selection.

---

## 0. What this changes, in one line each

- **The declarative theory:** one term former at the computing layers,
  `app@(f; a)`, the checked spelling of `app(f; x:S.T; a)`, with the same
  typing-preserving translation `⌊·⌋` as the five of stage 1 (§2.3). Not
  admitted in a `box` payload; the code grammar and its recursors are
  untouched.
- **`typing.rs`:** one inference rule (§3.1); one new selection
  `Sel::App(a)` — `T[a/x]` of `Π(x:S). T` (§3.2).
- **`conv.rs`:** none in its decisions. The typed application rule
  (DESIGN.md, "Application and projection are typed", 2026-09-06) already
  reads the head's inferred Π and ignores the stored annotations; the view
  gains `Option` levels, as `fst@` got (§4).
- **`eval.rs` / `value.rs`:** `Elim::App`'s annotation closures become one
  `Option<PiAnn>`, `None` for `app@`, as stage 2 did for `Elim::Fst` (§5).
- **The elaborator's emission:** the application emitters write `app@`
  outside a quotation, except where the head is a `λ` (§6).
- **The quote boundary:** `spell_checked_in_code` gains the sixth former;
  its record type gains a Π case (§7).

---

## 1. The site

What `Term::App { fun, dom_level, cod_level, dom, cod, arg }` stores is the
Π of `fun`, **instantiated at the arguments before it**: for
`App(App(f, a), b)` the inner node's `cod` is `Π(y:B[a/x]). C[a/x]` and the
outer node's `dom` is `B[a/x]`, `cod` is `C[a/x]` under one binder. Nothing
in the term shares those substitution instances, so the image — a tree —
spells `a` once as an argument and once more per later annotation that
mentions it, recursively. That is the whole mechanism; `trans` (66 M of
`calc_text`), `selected_of_match` (36 M), `le_trans` and `cong_cons` (11 M
each) are simply the callees whose telescopes are dependent in their
earlier arguments and whose arguments are large.

**Who reads the stored annotations** (kernel audit, this tree):

| site | reads | verdict |
|---|---|---|
| `typing.rs` App rule (~2811) | `ty_check`s `dom`/`cod`, checks `fun` against `Π(dom, cod)`, returns `cod[arg/x]` | the one real reader; replaced by §3.1 for `app@` |
| `conv.rs` ~2215, neutral application | `lev_eq` of the stored **levels** only; the Π is the heads' inferred one | `Option` levels (§4) |
| `conv/dom.rs` ~1221, `values.rs` ~1766, views | levels only | `Option` |
| `eval.rs` ~1301, `Elim::App` construction | makes closures of `dom`/`cod` | `Option` (§5) |
| `eval.rs` ~464, ~1662/1710 | copy an existing elim's annotations when re-applying | carry the `Option` |
| `eval/transduce.rs` ~1328, `probe.rs` ~98, `transduce.rs` ~649/1937 | build `Elim::App` from a Π the caller holds (a motive's, or dummies) | unchanged — they write `Some` |
| `conv/dom.rs` ~1755/1835, `reduce.rs` ~673/2170, `eval.rs` ~1970/2211/2634 | build `Term::App` from a Π the caller holds (η, recursor steps) | unchanged — component form stays valid |
| `reduce.rs` ~783/1434 | β and the congruence step copy annotations | one arm each for `app@` |
| `rec.rs` | the code recursors' `tm_app` branch | never meets `app@` (§2.2) |

So the kernel's only consumer of *what the annotations say* is the typing
rule. That is the precondition stage 2 established for the intros
(`intro-by-type-design.md` §2.4's conversion paragraph), and it holds here
because of the 2026-09-06 typed application rule.

---

## 2. The form

### 2.1 Syntax

```
app@(f; a)        infers  T[a/x]   where f infers F and F ⇝* Π^{l,l'}(x:S). T,  a ⇐ S
```

No annotation, no levels. `Term::AppAt { fun: Rc<Term>, arg: Rc<Term> }`.
It is inference-only in the sense that `fun` must infer — which every head
the elaborator writes does, **except a `λ`** (a β-redex the elaborator
emits for a `let` or a generated instantiation): a `λ`'s inference arm
infers its body, and a body that is an unannotated intro is
`NotInferable`. The emitter keeps the annotated `App` for a `λ` head (§6);
the rule does not special-case it.

### 2.2 Why a new former and not `App` with optional annotations

The same two facts as `intro-by-type-design.md` §2.2, and ch. 04 states the
first itself: the application annotations exist "to prepare for a better
formulation of the elimination principle for code" (`04:192–199`).

- The code recursor's application branch types its sub-structures by the
  annotations — `u_f : Trm_c(g ⊢ Π(x:U_S). U_T)`, `u_a : Trm_c(g ⊢ U_S)` —
  and a branch handed no annotation cannot state them.
- Code equality is syntactic (ch. 05, Static Code): an `App` whose
  annotations were optional would give one term two unequal codes.

So `App` keeps its annotations and stays the only application inside a
`box`; `app@` is what the elaborator writes elsewhere. The box side
condition of `intro-by-type-design.md` §2.3 extends to it verbatim, and
the quote boundary (§7) translates it.

### 2.3 Conservativity

`⌊app@(f; a)⌋ = app(⌊f⌋; x:S.T; ⌊a⌋)` where `Π(x:S).T` is the whnf of `f`'s
inferred type in the derivation — the stage-1 translation, one former
more. Typing: the `app@` derivation is the `app` derivation with the
annotation premises (`S`, `T` well-formed; `f : Π(x:S).T` by conversion
from `F`) discharged by `F ⇝* Π(x:S).T` and the inversion of `f`'s own
typing. Reduction: β fires on `app@(λ…; a)` exactly as on `app`, reading
nothing from the application. Conversion: the typed rule never related the
annotations, so it relates two `app@`s, an `app@` and an `app`, and two
`app`s by the same arm (§4). Under a box: nothing, by the side condition.

---

## 3. The checker

### 3.1 The rule

```
app@(f; a) ⇒:   (F, _) = tm_infer(f);
                F is syntactically Π^{l,l'}(x:S). T  →  tm_check(a, S @ l);  ⇒ (Syn T[a/x], l')
                otherwise  view_v(F) = Pi{l, l'}      →  tm_check(a, Sel{F, Dom} @ l);  ⇒ (Sel{F, App(a)}, l')
                                                          else HeadMismatch
```

The **first line is the common case and is today's checker exactly**: a
global's declared type, a local's type, or the previous node of a spine
whose type was already syntax, is literally a Π, and the result is the
same `cod.apply_local(id.extended(a))` the `App` rule returns now. No
description is formed, so the conversion that follows sees the same syntax
it sees today and the reflexivity shortcut hits exactly where it hits now.
This matters: stage 2 raised conversion misses 30–50 % on the small files
because its results are descriptions, and application is the most common
former there is — a rule that formed a `Sel` at every application would
tax every declaration in the library to fix a few.

Only when `F` needs **reduction** to expose its Π — a head whose own type
is already a description (calling a function-typed record field: the head
is a `fst@`/`snd@` projection since stage 2), or a type-level definition
that unfolds to a function type — does the rule take the value-domain view
and return a description. That is §3.3 of the
stage-1 design's rule, unchanged: *the rewriter never runs on a type that
came through a checked spelling*; a syntactic Π read is not a rewrite.

What the rule **drops**, relative to `App`: the two `ty_check`s of the
annotations and the conversion of `F` against `Π(dom, cod)`. Those are the
per-node constant the kernel pays today at every application; `app@` pays
the head's inference instead, which the `App` rule also paid (inside the
`tm_check` of `fun`).

### 3.2 `Sel::App`

`T[a/x]` of `Π(x:S). T` — the Π analogue of `Sel::Snd(a)`, carrying the
argument **term**: arena-free, like every description. Scoped at the same
Γ length as its `of` (unlike `Sel::Cod`, which is the codomain *under* the
binder). `materialize`: `cod.apply_local(id.extended(a))` of the rewriter's
Π; the value view: apply the codomain closure to `eval(a)`.

A spine `f a₁ … aₙ` whose head needs reduction forms a chain
`Sel{Sel{…{F, App(a₁)}…}, App(aₙ)}`, linear in `n`; viewing the `k`-th
evaluates the chain from `F`, so a spine costs `O(n²)` evaluation steps in
the worst case. Theorem heads have `n ≤ 20`; this is recorded as a cost,
not designed around (stage 1b's `sel_evals` column counts it).

### 3.3 The oracle and the differential

`materialize_eagerly` spells `Sel::App` through the rewriter, which makes
the eager mode today's checker on `app@` too. `typing_differential.rs`
gains `app@` in `wt.rs`'s streams (heads: globals, locals, spines, a
reducing type-level head, an `app@` over a `fst@`), off by default for the
bench fixtures as the stage-1 generators are.

---

## 4. Conversion

`TmView::App`'s levels become `Option<(&Level, &Level)>`; the arm compares
them when both sides have them and otherwise skips the comparison — the
levels it uses are the inferred Π's either way, which is the typed rule's
whole point. A neutral `app@` and a neutral `App` compare by that same arm.
No new decision.

---

## 5. Evaluation

`Elim::App { ann: Option<PiAnn>, arg }`, `PiAnn { dom_level, cod_level,
dom, cod }` — one field so "no annotation" is one state, and `Option` rides
the reference's niche, as `SigAnn` did (`Val` and `Elim` stay the size
they are). `eval` builds `None` for `app@` and never views the head's type
to invent one: nothing reads the closures but the copying sites of §1,
which carry the `Option`. The transducer's and the probe's own
constructions keep writing `Some`.

---

## 6. The elaborator's emission

### 6.1 The emitters that change

The mass comes through **three sites**:
`application.rs`'s `apply_explicit` (~515) and `apply_implicit` (~665 for
the main Π walk, ~705 for spilling onto a callable result), through which
almost every surface call goes (about twenty call sites in `lib.rs`, plus
`recursion.rs` and `literals.rs`). Behind `emits_at_forms(cx)` and **a head
that is not a `λ`** (§2.1), each writes `AppAt { fun, arg }`.

The Π the elaborator walks is unchanged: it still `whnf_for_application`s
the running function type, checks the argument against `dom`, and continues
with `cod[arg/x]`. Only the *written* node changes, and with it goes
`emitted_annotations` (~458). That is the `emit_ty_in` respell of `dom` at
0 and `cod` at 1 that every application pays today, in `apply_implicit`'s
metavariable scratch world where the annotations also have to be
instantiated by the goal substitution later. `app@` has no annotation to
respell or instantiate, so this round also removes an elaboration-time
per-node constant (`decl_emit_ns` is where it shows).

**Every other emitter switches in the same sweep** (amended 2026-09-22, the
user's call over this section's first draft, which left them on `App`). The
first draft's reason for leaving them was that their annotations are not
where the mass is; the reason for moving them anyway is that a term built by
a generator and a term built by a surface call meet in `==` comparisons
(`relational_context`, the registry's slot checks, lgg's witnesses), and one
spelling everywhere is what keeps those from declining on an `App` beside an
`app@` for the same call.

- The secondary spine builders — `gen_app`, `gen_spine`, `saturate`
  (gendefs.rs), `try_code_template` (quote.rs), `elab_ty_app` (lib.rs),
  `generalize.rs` — and the ~40 one-off constructions in `vec.rs`, `wf.rs`,
  `forded.rs`, `indexed.rs`, `matching*.rs`, `relational_context` and the
  rest go through `spelling::checked_app(fun, levels, dom, cod, arg)`, which
  writes `app@` unless the head is a λ. It takes the annotations so each
  call site reads as the `app` it replaces.
- It is **unconditional on the quotation state**: none of these builders
  writes a `box` payload itself, and a term pasted into one goes through
  the quote boundary's translator (§7).
- **Still `App`, by necessity:** code that is *built as* a payload —
  certgen's markers and its `mark` walk, whose input is
  `global_body_in_code_form`, already translated; the kernel's own
  recursor-branch and η constructions; the two rebuilders of §6.2 on an
  `App` input; lgg's `App`/`App` generalization. `analyzer_app` (certgen)
  stays too: it applies a registered analyzer to closed arguments and
  nothing reads it but the evaluator.

### 6.2 The readers

The stage-2 lesson is that a reader matching only the component form
**declines silently** rather than failing (`function_ir`'s choice reader,
lgg's root mismatch). Every reader is walked:

- **Shape-only readers, about 50 sites** that match
  `Term::App { fun, arg, .. }` and ignore the annotations. Counts:
  `unification.rs` 6, `relational_context/proof.rs` 6, `indexed.rs` 6,
  `certgen.rs` 4, `gendefs.rs` 4, `display.rs` 3, `lib.rs` 3, `matching.rs`
  2, `traits.rs` 2, `omega_cert.rs` 2, `forded.rs` 2, `measure_context.rs`,
  `emission_walk.rs`, `oracle.rs`, `function_ir_source.rs`
  (`application_spine`), `inductive.rs` and `lgg.rs` 1 each, plus tests.
  They go through one view, `spelling::app_of(t) -> Option<(&fun, &arg)>`,
  beside `inj_of`/`pair_of`/`proj_of`, and any spine walker through
  `spelling::app_spine`. This is the bulk of the round's diff and is
  mechanical.
- **Semantic readers of the annotations**, which need an answer rather
  than a view:
  - `unification.rs` ~304 `matching_value_spine` decides the type-argument
    prefix by `dom == Ty(_)`. For an `app@` spine the domains are the
    head's: peel the head's type. A global's statement is in Ψ; a local's
    type is in Γ; a head that is neither declines, as the function does
    today for a head it cannot read. Add `spelling::app_domains(el, cx,
    head, n)`, which peels `n` Π's off the head's type through
    `Elaborator::whnf` and substitutes the spine's arguments.
  - `relational_context/proof.rs` ~32–49 `relation()` reads the carrier and
    its level off the `dom` of `El(R a b)` and checks homogeneity with
    `first == dom`. The same helper answers it. The file's `==` comparisons
    on whole terms (389, 401, 433, 491, 526, 288) compare annotations
    today. With `app@` there is less to differ, but an `App` beside an
    `AppAt` for the same call is now unequal. Its inputs come from one
    emitter, so that should not arise; the implementer confirms it with a
    probe and does not assume it.
- **Rebuilders:** `indexed.rs` ~126 `set_scrut` and `omega_cert.rs` ~1264
  `with_arg_at` replace an argument and copy the annotations. On `AppAt`
  they replace the argument and copy nothing. The audit flagged
  `with_arg_at`'s copies as a stale-annotation hazard when the telescope is
  dependent; `app@` removes it by construction.
- **Anti-unification and template matching:** `lgg.rs` ~1091 and
  `gendefs.rs` ~632 `Holes::tm` require equal levels and relate `dom`/`cod`.
  Two `AppAt`s relate `fun` and `arg` only. An `App` against an `AppAt` is
  one former written two ways, as stage 2 settled for the intros. Relate
  `fun`/`arg` and **emit `AppAt`**: its head is a generalization of two
  inferable heads, and it carries no annotation that could mention a
  generalized position.
- **Auditors and encoders:** `emission_walk.rs` gets an `AppAt` arm with
  no slot, `module_image.rs` a tag, `crates/cache/src/merkle.rs` a hasher.
- **Code:** certgen's `mark` copies annotations into a `BoxTm`, but its
  input is `global_body_in_code_form`, already translated (§7). The code
  recursor's `tm_app` branch (`reduce.rs` ~1435) never meets `app@`, by the
  box condition.
- **Test readers** asserting that annotations are `El` references
  (`wf.rs` 2205, 2888, 2918, 2945, 3607, 3635; `indexed.rs` 2125) are
  rewritten against the invariant, as stage 2 rewrote its five.

---

## 7. The quote boundary

`typing::spell_checked_in_code` already rewrites the five checked
spellings a payload receives from outside; `app@` is the sixth, and with
application annotations the dominant carrier of statements pasted into
quotations, it is the case that matters most. The record gains
`Spelled::Pi { dom_level, cod_level, dom, cod }`, kept at the §3.1 rule
from whichever branch ran (the syntactic Π's components, or the eager
view's), and the rebuild writes `Term::App` with them. Nothing else in the
translator changes; its fixpoint loop already handles a recorded component
that carries checked spellings of its own.

---

## 7.5 Rejected shapes

- **Optional annotations on `App`.** One term would have two unequal
  codes, and the code recursor's branch could not state its sub-structures'
  types (§2.2).
- **An n-ary application carrying the head's Π once**
  (`apps(f; Π…; a₁ … aₙ)`). Linear rather than zero, and still a new
  former the code grammar would have to exclude. It stores what the head
  already infers, and `app@` is strictly smaller for the same kernel
  change.
- **Dropping only `cod`.** `dom` is 67 M of the 331 M on `calc_text`, and
  the rule that reads `cod` off the head reads `dom` off it for free.
- **Naming the substitution instances** (a `let`, Ψ mints). Refused for
  the stage-1 forms on the user's two criteria, and this round needs no
  name: the head's type is already the shared object.

---

## 8. Measurement

The instrument is in (`HEATHER_IMAGE_ATTRIBUTION`). The before column is
this tree at 0a4004c:
- `calc_text`'s image is 265.5 M nodes, over the 256 M budget;
- the tally's `App.dom`/`App.cod` are 331 M of 362 M;
- a two-step `calc` over one `Cons` at `List<Char>` is 19 370 nodes, of
  which 13 704 are application annotations. The acceptance numbers in
§9 are read off the same instrument and `scripts/perf ab`.

---

## 9. Stages, gates, kill criteria

### Stage 1 — the kernel

The former through the stage-1a transcription (`term.rs`, `subst.rs`,
`bounds.rs`, `fmt.rs`, `reduce.rs` β/neutrality/whnf grammar, `eval.rs`
with `Elim::App { ann: Option<PiAnn> }` and its copying sites, the
conversion views' `Option` levels, `merkle.rs`, `module_image.rs`). §3.1's
rule with its syntactic fast path. `Sel::App` in `ity.rs`, `materialize`,
the value view. The box side condition. `Spelled::Pi` in the quote-boundary
translator. `wt.rs` generating `app@` (off by default), and
`typing_differential.rs` over it.

Golden tests:
- a global head returns **syntax** (the fast path), and a projected record
  field head returns a description;
- `box(app@(…))` is refused and the translator turns it into `app`;
- β on `app@(λ…; a)`;
- the negative control: an ill-typed argument is refused at the domain the
  head infers, with a head whose Π needs reduction.

*Gate:* full `scripts/test` byte-identical in verdicts (no emitter yet);
`typing_differential` green; `scripts/bench --check` against a control saved
on the parent commit.

### Stage 2 — the elaborator

§6.2 first: `spelling::app_of`/`app_spine`/`app_domains` and every reader
through them, while no emitter writes `app@` yet, so the reader changes are
checked with the corpus unchanged. Then §6.1's emitters, all of them.

*Gate:*
- full `scripts/test`, and the `calc_text` showcase gate green;
- **`calc_text`'s image stored under the unchanged 256 M budget** and
  `--only` working on it. The attribution predicts on the order of 30 M,
  the tally less its `App` slots;
- `HEATHER_IMAGE_ATTRIBUTION`'s `App.dom`/`App.cod` near zero outside the
  §6.1 "still `App`" sites and λ heads;
- `scripts/perf ab --base <stage-1 commit>` on `calc_parser` and the three
  curve probes: **`conv_misses` and the kernel gate not up** on the
  corpus. This is the fast path's claim (§3.1), stated as a gate because
  stage 2 of intro-by-type moved misses 30–50 %;
- `decl_emit_ns` reported.

*Kill criteria:*
- if the corpus's kernel gate or misses rise materially, the fast path is
  not holding. Stop and report with the counters, keeping stage 1, which is
  inert without an emitter;
- if the image does not fall under the budget, re-run the attribution
  before touching anything else.

### Out of scope

Stage 3 of
`intro-by-type-design.md` (the elaborator's transient reduct); naming
`Char`'s representation by reference (×2 on character values, a spelling
fix to take separately); code's own sharing
(`issues/code-payload-sharing.md`).

---

## 10. Status

Design written 2026-09-22. Owning issue
`elab-emits-normal-form-of-matched-type-argument`.

**Landed 2026-09-22**, both stages, every emitter (§6.1 as amended):
kernel `a471678b`, elaborator `54bb800f`. Full suite 2870 passed / 0
failed, `bench --check` within thresholds.

Gates, all met:
- **Image:** `calc_text`'s attribution tally is **11.4 M nodes** (362 M
  before; `App.dom`/`App.cod` gone, what remains is led by `PairAt.ty`
  5.4 M, `Lam.dom`, the constructor encoding and case motives). The image
  publishes: a warm `--cache` run replays it in ~1 s, and `--only
  checked_run` works (1.4 s). `checked_run#body` 90 M → 0.37 M.
- **Misses and gate** (`scripts/perf ab --base a471678b`, three interleaved
  cold samples, every metric separates): `calc_parser` conv_misses 299 k →
  58 k, kernel gate 27 s → 3.3 s, wall 50 s → 9.3 s, peak 1.16 GB → 164 MB;
  the curve probes cp9/qt3/qt5 alike (misses −80 %, gate −86 to −88 %,
  qt5's peak 2.7 GB → 168 MB). `check_terms` and `decls_gated` are
  identical across the binaries, so the same work was checked.
- **The showcase gate** checks `calc_text` in 16 s at 0.3 GiB (debug,
  width one), against the manifest's 334 CPU-s / 9.8 GiB.

The fast path's claim held with room to spare: misses fell rather than
rose, because the `app` rule's two annotation `ty_check`s and its
annotation-against-head conversion were the bulk of the kernel's queries on
these files.
