# Annotation-component respelling — design

Deliberate perf round on `issues/wf-field-conversion-cost.md`, 2026-08-13. The
predecessor (`docs/family-type-code-defs-design.md` §10, the 2026-08-12
extension) landed `GenDef::TyCode` and collapsed every *whole-type* occurrence
of `⟦D⟧` in the two `match` lowerings to `El (D#tycode^δ)`. The issue stayed
open on a measured residual, and its attribution — not its opening suspects,
all three closed — is this round's charter:

1. **per-application `dom`/`cod` annotations**: every `Term::App` carries the
   callee's declared parameter and result types verbatim, so a call to
   `cert_chain(ir: Ir, ih: Ihp) -> Cert` writes `⟦Ir⟧` (1,712 nodes) and
   `⟦Cert⟧` (which carries three copies of `⟦Ir⟧` by law 2) into the term,
   per call, and a partially-applied spine carries the whole remaining `Π`
   chain at each step;
2. **field-binder projection chains**: `Elaborator::projection`'s `Fst`/`Snd`
   chain annotates every step with the Σ components of `⟦cᵢ⟧`, and those
   components *contain the field types* — `⟦Ir⟧`, `⟦Pre⟧` — verbatim; a
   `match` arm's payload binder aliases to such a chain, so every *use* of
   the binder replays it.

The spine (38 k of 21 M) and the `Supf`/`ElimWf` shape slots (1.3 k) are
measured negligible and are not touched (`issues/wf-shape-annotation-slots.md`
keeps the shape slots).

## 1. The observation that picks the design

Both residual families are made of types that are **already nameable**. An
`App`'s `dom` is very often *exactly* some declaration's registered lowering;
a projection chain's components are Σ shells of size O(fields) whose mass is
the embedded *field types*, and a field type is again some declaration's
registered lowering. Nothing in the residual needs a new kind of code — it
needs the existing `TyCode` reference written into two more families of
annotation slots, including **inside** compound annotations (a `Π` chain, a
Σ tail) whose top node is not itself a declared type.

So the round's mechanism is one function:

```text
respell_ty_deep(cx, ty, depth) — rebuild `ty` with every sub-type that IS a
registered declaration's lowering replaced by El (D#tycode^δ), guarded per
node by the same structural comparison ty_type_ref has always made; None if
nothing changed.
```

Top-down: at each node first try the whole-node respell (`respell_ty`, whose
guard compares against the registry's inline copy and can only *decline*,
§10.4 of the family-code design); on decline, recurse into the node's type
components (`Pi` dom/cod, `Sigma` fst/snd, `Sum` lhs/rhs, `Vec` elem, `Wf`
shape, `Id`/`SEq` ty). `depth` tracks binders crossed (`Pi` cod, `Sigma` snd
bind one each), and a hit at depth `d` is the reference shifted by `d` — the
same `shift_local` the motive respell already uses, sound because a type that
compares equal to the registry's *closed* copy is itself closed. Terms inside
types (`Id` endpoints, `Vec` length, `El` codes) are not walked: annotations
live in type slots, and a term walk would be new surface for no measured mass.

Idempotence is inherited from `respell_ty`: an already-`El`-headed reference
declines at the top and has no components to recurse into.

## 2. The three site families

The line held throughout is §3.1's, unchanged: **structural reads keep the
inline type; only emitted annotations take the reference.**

### 2.1 Statements (the "statement-side respelling" lever, taken)

`elab_decl_inner`'s closing loop (`lib.rs`, "Close over the telescope") builds
the declaration's statement `Π(x₁:A₁)…. R` and the body's outer `λ`s from the
same `param_info`. Both copies of each `Aᵢ`, and the result `R`, are respelled
there — after the body is elaborated (so every structural read during
elaboration saw inline types, zero behavior change inside the declaration) and
before `apply_global` (so the reference's `goal_base` padding is renumbered
exactly as every body-internal reference already is). Binder `i`'s type sits
under `i` binders and the result under all `n`, which is the `depth` argument;
references are minted against the empty context, matching the `LocalCtx::nil`
the statement is checked and pushed in.

This is the high-leverage half, because it **cascades**: once a callee's Ψ
statement spells its `Π` components as references, *every* later application
of it — in bodies, in theorem statements, in other statements — reads its
`dom`/`cod` annotations off that statement and emits them small, with no
per-`App` work at all. Within-file declaration order does the rest (a callee
is declared before its callers). `apply_explicit`/`apply_implicit` were
originally not touched at all because of that cascade; they now take the one
chokepoint like every other emitter (§2.4's first bullet, §2.5), which is
cheap precisely because the source has already shrunk.

Two consequences, both acceptable and both recorded:

- an *argument* is now sometimes checked against `El (D#tycode^δ)` rather
  than the inline `Wf`. That is not a new situation: a type that arrives as a
  code is `docs/types-as-expressions.md`'s shipped path, every consumer whnfs
  first (`build_ctor`, `elab_match`, `tag_of` through `decoded`), and the
  elaborate phase is 1–6% of a file's cost against the gate's 94–99%;
- `unify_ty` learns nothing through an `El` head — and can lose nothing here,
  because a component respells only if it *is* a closed, unparameterized
  declaration's lowering, which mentions no metavariable and no parameter.

`meta fn` statements (`quote.rs`) are deliberately not in scope: their cost
story is the Layer::Meta gate (`issues/certgen-harness-cost.md`), their
domains are `Ctx`/code types the registry never names, and `gen_ref`'s
meta-numbering is only exercised *inside* meta bodies today.

### 2.2 Projection chains

`Elaborator::projection` (`inductive.rs`): the emitted `Fst`/`Snd` steps take
`respell_ty_deep` on their `fst_ty`/`snd_ty` (`snd` at depth 1 — the Σ
binder). The loop's own working copy (`cur`) and the *returned* field type
stay inline: the return value becomes a `match` binder's alias type, which
§10.3's table already pins as a structural-read position. Every caller —
tier-1 `wf_branch` payload binders, tier-0 `case_tree` arms, `read_ctor`,
`ConstBody::Field`/`Arity` — inherits the small annotations through the one
helper.

### 2.3 Constructor field tuples

`build_fields_skel` (`inductive.rs`): the emitted `Pair`'s `fst_ty`/`snd_ty`
(again `snd` at depth 1) — the same Σ components at the value-construction
side that `projection` copies at the elimination side. A constructor *value*
of an `Ir`-field declaration currently carries `⟦Ir⟧` in its label tuple's
annotations; a `refl` pin between two such values pays it twice. The checking
of each field argument (`elab_check` against `fst`) keeps the inline
component, per the line.

`inject`'s `Inl`/`Inr` lhs/rhs (the sum spine at constructor values and case
trees) are **left alone**: the draft measures them at 38 k nodes of 21 M, and
the charter says not to chase them. If this round's counters show them
dominating what remains, that is the successor's first line, not a rider.

### 2.4 Applications, eliminator slots, and decoded code literals (2026-09-06)

`issues/emission-site-respell-audit.md`'s round, driven by the `Tc::conv_ty`
miss sampler with per-declaration attribution
(`issues/conv-miss-sampler-item-attribution.md`). Every one of its four rows
was two emission sites disagreeing about the same type, and the fix at each
is the line above applied to one more site — no new definitions:

- **Applications.** A callee that is a *local* binder copies its `dom`/`cod`
  off the binder's inline type, and an application embedded in a statement —
  a lemma's `equation: … = operation(…)` hypothesis, a record field's
  `run(state.gprs)` — then met the cascade-respelled twin of that type at
  every use (a section substituted for `operation`, the Σ binder's own
  respelled type). The type the application *continues with* is still
  computed from the structural `cod`.
- **Decoded code literals.** A type that arrives as `El ⌜Σ…⌝` — the quote of
  a `→ Type` body such as `Valuation()` or `RegionHolds(…)` — whnf's one
  level at a time, and a projection chain or field tuple that copied the
  components verbatim spelled each link as the *un*decoded literal of a tail
  whose own annotations, one link down, were its decode; the kernel
  evaluated the whole literal at every link. `inductive::decode_deep` gives
  the fully inline spelling, and decode-then-respell is what an emitted slot
  writes. Emission only: nothing structural reads a decoded copy it did not
  already read.
- **Monomorphized `Wf` slots.** A `sup_f`'s shape/arity (`build_ctor`), an
  `elim_Wf`'s (`build_elim_wf`) and the children tuple's element type
  (`build_children`) have no registered pair to name for a monomorphized
  instance (`List<Node>`) and stayed inline, while the label's injections and
  the field tuples around them respelled — so a constructor value's label
  was checked against an inline shape, and the eliminator's inline arity met
  the value's respelled label inside every `Fin(n[ℓ/x])` the kernel rebuilt.
  They respell shape and arity together or not at all, when `wf_slot_refs`
  declines.

Every site named above — the application annotations (in `apply_implicit`'s
scratch world too), §2.2's and §2.3's, `respell_spine`, and the three `Wf`
slot fallbacks — writes its slot through the one function §2.5 names, so the
list is a history of where the rule was learned rather than a list to keep in
step.

What the audit found *not* to be a spelling pair, left where it was: the
`Id` vs `Id` row is `refl` at a statement whose endpoints genuinely need
computing, and the `El^δ` vs `Σ` row is a constructor literal checked against
a respelled field type — one δ and a compare each, the cost the reference
spelling is meant to have. Both are logged on the audit issue.

### 2.5 The chokepoint and the walker (2026-09-06)

The four rows of §2.4 and both of its riders were one failure repeated —
a site copied a type from wherever it read it while a sibling respelled the
same type — and every fix was the same edit. So the rule stopped living in a
dozen call sites and became one function
(`issues/emission-spelling-chokepoint.md`):

```text
Elaborator::emit_ty(cx, ty, depth) — decode_deep, then respell_ty_deep;
None keeps the caller's original and its sharing.
```

**Every** constructor of a `Term` or `Type` annotation slot in the elaborator
goes through it — the statement cascade of §2.1, the projection chains of
§2.2, the field tuples of §2.3, the application annotations and `Wf` slot
fallbacks of §2.4, a `match` motive, a `Supf` rebuilt by a fording inversion,
and `refl`'s element type — and `emit_ty_in` is the same function in an
application's scratch world. §3.1's line is unchanged and is what the
chokepoint is *not*: a structural read keeps the inline copy (the type a
checking position continues with, `build_fields`' per-field expected,
`projection`'s returned field type, a binder's alias type).

The other half is a walker (`crates/elab/src/emission_walk.rs`) that asks the
same question after the fact. Behind a runtime flag
(`Elaborator::enable_emission_walk`) it visits, for each checked declaration,
the statement and term the kernel is about to be handed and calls `emit_ty`
at every emitted slot; a `Some` is a site still writing a spelling the
chokepoint would not, reported with the variant, the field, the binder depth
and both spellings. Its scope is exactly the chokepoint's, so that "the
walker lists this" and "routing this site through `emit_ty` changes this" are
the same statement: a slot is checked whole and never descended into, terms
inside types are not walked, and code payloads are not walked at all. The
traversal is exhaustive over the kernel's variants with no wildcard arm, so a
new former with an annotation slot does not compile until someone answers for
its spelling.

It runs in two places: the whole-library acceptance load
(`crates/elab/tests/ir_v1.rs`), where the assertion is "no slot outside the
recorded residue" — the slots the round that landed it found and did not
route, listed there by name and owned by
`issues/emission-walker-residual-sites.md`, so that the list only ever
shrinks — and the x86 conversion-miss measurement
(`scripts/measure-x86-conv-miss`), beside the sampler table: a sampler row
and a walker finding are the same disagreement seen from the kernel's end
and the elaborator's.


### 2.6 Default annotation API (2026-09-14)

`Elaborator::annotation_type(cx, ty, depth) -> Type` is the default for an
emitter that needs an annotation. It applies `emit_ty` and preserves the
original type when nothing changes. Callers do not select closed versus
parameterized naming or write their own fallback chain. Structural readers
keep their original type.

`emit_ty` remains the optional rewrite query for the emission walker and
callers preserving an existing `Rc` when no rewrite happens. Scratch-world
annotations still use `emit_ty_in`. Wf shape/arity slots continue to use
`emit_wf_slots` as a pair: a whole-type annotation is not a substitute for
those two components.

The narrower `ty_type_ref` is now called `closed_type_ref`. It recognizes
only registered closed types; its only production caller is the naming
registry's `respell_ty_at`. The three former external callers — children
construction, child-projection motives and match telescopes — all use
`annotation_type`, as does the match motive and code-function template
emission. The constructor's now-unused tag argument was removed.

The child-projection audit found no additional established performance bug:
`build_elim_wf` already canonicalizes its incoming motive. Using the default
API there removes a redundant closed-only policy choice. Regression coverage
checks its emitted motive and kernel-checks it over a neutral `Box<A>` with
an open element type. The API also has controls for plain types, closed
references, parameterized references, idempotence and binder depth; the
previous match-telescope regression remains in place.

For the measured failure that motivated this API, see
`issues/call-run-checked-theorem-cost.md`. This cleanup does not extend
projection eligibility or change kernel conversion.


### 2.7 Representation roles at the recursive telescope boundary (2026-09-14)

`wf_types.rs` gives the shared `Tel` two distinct representations:

- `StructuralWf` borrows a type validated to have a structural `Wf` head.
  Structural readers explicitly call `as_type` or `shifted_structure`.
- `EmittedType` is constructed through `StructuralWf::annotation`, which
  applies `annotation_type`. Its fields are private and it has no `Deref`
  or `From<Type>`. A shift returns another `EmittedType`; `into_type` marks
  the explicit handoff to a raw kernel annotation slot.

`StructuralWf::telescope` accepts `&EmittedType` for the children element
annotation. It delegates to the kernel's existing `wf_step_telescope_at`,
which remains the sole transcription of the telescope. A raw `Type` or a
`StructuralWf` in the element position is a Rust type error. The structural
and emitted `Tel` fields consequently cannot be swapped implicitly either.

This guarantee is local to the telescope boundary. The kernel AST and its
raw annotation slots still use `Type`; explicit accessors can cross back to
that representation. The wrappers classify representation roles, not binder
contexts or equality between two independently constructed types. The
existing kernel checks retain those responsibilities.

The three structural accesses in `indexed.rs` were made explicit, preserving
their existing representations. Spine and Wf slot-pair APIs retain their
existing contracts. The wrappers introduce no additional normalization:
they call the same annotation policy and kernel telescope code as before.

Validation includes a temporary mutation at the real telescope call site:
substituting `&structural` for `&emitted` fails `cargo check` with E0308,
“expected &EmittedType, found &StructuralWf”. The mutation was reverted.
Unit coverage rejects non-Wf structural inputs (including named codes),
checks that shifts retain the emitted representation, and retains the
open-type child-projection and parameterized-match emission controls.

### 2.8 Independent regression checks and remaining-site probes (2026-09-14)

Three checks protect different parts of the contract:

- `wf.rs::children_annotations_name_both_the_container_and_varying_payload`
  inspects the actual emitted children-vector domain for payload widths
  2/8/32. It compares the container and argument with the registry's
  `TyCodeFn(Box)` and `TyCode(Payload)` identities; the expected result is
  never generated by the annotation API under test.
- `tests/telescope_roles_compile.rs` compiles the real private wrapper
  module against the kernel dependency. Its positive fixture must compile;
  replacing the emitted argument with the structural wrapper must produce
  E0308 for those types. Minimal frontend signature stubs avoid making the
  wrappers public merely for a test.
- `tests/annotation_cost.rs` checks deterministic evaluator-step growth,
  with one kernel worker and setup excluded. Counts must be nonzero; the
  gates use generous ratios, not wall times or exact snapshots. A temporary
  inline-annotation mutation was accepted semantically but failed the cost
  guard, confirming that it detects the intended regression.

The indexed audit compared emitted annotations at `wf_ih_at` and
`wf_branch_env` with the current structural annotations, retaining the
structural pattern-alias type and reconstruction of `Supf`. On a three-case
recursive index and a parameterized indexed family, the family's declaration
alone was a weak probe: its constant motive discards the child term. A
recursive copy with a dependent return type retains that work. Naming the
annotations saved about 2.5% of its steps without changing the payload-width
trend (counts in [[call-run-checked-theorem-cost]]). That experiment was
reverted: no second dominant annotation-cost defect was established. The
fixture bounds the existing trend and covers open parameters, neutral
matches, literal computations, checking positions and a false equation.

The projection fixture substitutes bare and computed receivers into a record
whose later equality field refers to an earlier output field. It varies
field-chain depth 1/2/3 and rebuilding steps 0/1/2/4/8, checks the field's use
at an open type and at a literal, and rejects a false equality on the same
path. These small cases support retaining the current receiver policy;
they do not prove all substitution depths cheap. The broader boundary and
native scaling workloads remain owned by
[[per-instantiation-projection-boundaries]].

## 3. Rejected shapes, with reasons

- **A projection-chain code (`GenDef` per constructor component / sum tail),
  the issue's second filed lever.** It would name the O(fields) Σ shell and
  the sum tails that no whole-type code can name — but the measured mass of
  the chains is the embedded *field types*, which the existing `TyCode`s
  already name; the shells themselves are small. A new code family costs a
  registration boundary, a look-alike-negative surface, and a recognizer
  story per key kind, to collapse nodes the deep respell already collapses
  minus an O(fields) remainder. Filed as the fallback if measurement had
  said otherwise; it did not (§5).
- **Respelling inside `lower_instance` itself** (making `⟦D⟧`'s field types
  references at the source). Largest possible win on paper — it would shrink
  law 2's 3·|⟦T⟧| in the structural copy too — and rejected outright: the
  inline lowering is the *identity* every structural reader and both
  recognizer fingerprints anchor on, and `ty_type_ref`'s guard compares
  against it, so a registry whose copies were themselves respelled would turn
  every guard comparison into a spelling-sensitive one. That is the credulous
  read the fingerprint rounds exist to prevent.
- **Per-`App` respelling at the three `Term::App` emission sites.** Correct
  and local, but strictly dominated by the statement-side respell: it pays a
  guarded comparison per application forever, shrinks nothing in Ψ, and
  misses the `Π`-chain `cod`s that the statement respell gets for free.
- **Walking terms inside types** (respelling `App` annotations embedded in an
  `Id` endpoint of a *statement*). The cascade makes it moot for everything
  elaborated after this round lands — those `App`s are born small — and a
  term walk would touch every `Term` variant for no measured residual mass.

## 4. Correctness argument, and the test plan

The reference and the inline type are convertible by construction (the code
is `code_of` of the registry's copy; `ty_type_ref` declines anything else),
so every change is a spelling choice in an annotation slot the kernel checks
by conversion — the same conservativity argument as §1.3 of the family-code
design, now applied at component granularity. The guard's look-alike
negatives (`wf.rs mod tycode`) already pin the dangerous direction (a type
`tag_of` routes to `D` that is not `⟦D⟧`; `El` of the wrong code; a
byte-identical user global), and `respell_ty_deep` adds no new resolution
path — it calls the same guarded `respell_ty` per node.

New tests (`wf.rs mod tycode`, extending the existing module), on
`docs/testing-generated-terms.md`'s axes:

- the deep respell itself: a compound type (`Π` over two coded declarations,
  a Σ chain with a coded component under the binder) respells its components
  and *only* them, at the right depths — checked structurally;
- a statement really is respelled: a declared `fn f(t: T) -> T`'s Ψ statement
  carries `El (T#tycode^δ)` in its `Π` dom, and a *call* to it emits an `App`
  whose `dom` is the reference (the cascade, pinned rather than assumed);
- the four axes crossed with the new spellings: literal and neutral
  scrutinees through calls and field projections, an **open** element type
  (the parameterized `Box<A>` respells nothing and still elaborates beside
  coded declarations — coexistence), **checking** positions (a constructor
  literal checked against a respelled `dom`; a `refl` pinning a computation
  through respelled projections), and the negative control (a false equation
  through the respelled paths is still refused);
- depth: a projection chain under a `match` binder used in a *proof* (the
  shift-sensitive case — axis 2's reason).

## 5. Measurement

Per the issue's protocol: release build, wall best-of-3 under the CLAUDE.md
ulimits, exact node counts from a throwaway counter at the two kernel-gate
sites (reverted before final verification), A/B via a temporary env
kill-switch on `respell_ty_deep` (also removed before final). Workloads: the
`ir_v1` declarations prefix, prefix + landed `certgen_cert`, prefix + the
`Ir`-field draft (the issue's reproducer), prefix + `certgen_code`, and the
whole `lib/` trio as the suite sees it. Numbers live in the issue log only;
this document keeps shape claims.

Success criteria, from the charter: a measured reduction on the draft
reproducer and on `lib/certgen_code.hthr`'s program-layer helpers, and — as
evidence for the deferred certgen constructor-fields feature — a re-run of
the non-Nat design §2.2 cost shape showing the with-fields configuration no
longer threatens the harness rail.

---

## 6. Landed (2026-08-13), and the two findings the counters forced

Everything in §1–§4 shipped as designed, plus one extension the per-site
counters demanded and two findings that were not in the charter. Numbers are
in `issues/wf-field-conversion-cost.md`'s log, per policy; the shapes:

1. **A fourth site family: `inject` at constructor values** (§2.3's last
   paragraph, revised). The charter's "spine is negligible" was measured on
   a *match body*; on **values** — every constructor value written in a
   theorem statement or an arm — the `Inl`/`Inr` annotations carry the sum
   tails, each embedding every remaining field type, per injection step per
   value. `build_ctor` now injects over an emission copy of the spine
   (`respell_spine`), components deep-respelled; the structural spine
   (checking, container projection) is untouched. The match lowerings' own
   spine uses stay inline, still per the charter.

2. **Two-thirds of what then remained was `Level` trees, not types.** The
   lowering's level joins (`lower_shape`/`lower_ctor`) accumulated raw
   `Max` trees that compound quadratically across the Σ/Sum spine and are
   copied into every level slot; a single nullary constructor value carried
   a level-tree multiple of the whole type's size. Fixed at the two joins
   with `normalize().canonical()` — `equiv`-preserving by construction, so
   again a spelling change. This was worth roughly as much wall time on
   `lib/certgen_code.hthr` as the respell itself. (The closed
   `issues/level-normalization-allocation.md` was about comparison-time
   allocation; this is emission-side size — a different defect at the same
   type.)

3. **A latent kernel conversion gap, found by the statement respell and
   fixed in the kernel** (`conv.rs`, `tm_w`): term conversion never
   δ-unfolded its *type*, so two canonical values at `El (u^δ)` for a
   defined `u` fell into the neutral-type arm and compared `NotConvertible`
   — even two identical literals. Unreachable while defined codes never
   stood in the type slot of an `Id` (typing whnfs types before comparing;
   the elaborator's speculative auto-`refl` passes the `Id` component raw),
   and surfaced as every `{}` hole over a coded declaration's result type
   going unsolved (`lib/list_algos.hthr`). The fix is the mirror of
   `ty_w`'s existing δ stage, gated by the same `has_defs` and layer rules;
   pinned kernel-side (`crates/kernel/tests/definitions.rs`,
   `canonical_values_compare_at_a_defined_el_type`) and end-to-end
   (`wf.rs mod tycode`,
   `an_auto_refl_hole_solves_at_a_respelled_result_type`).

4. **The reflection boundary needs the inverse spelling** — found by the
   full suite, not the workloads. A `meta` analyzer reads a fn's statement
   *as code*, and at layer m a boxed global reference is syntax by design —
   so the respelled statement made every enumeration-result fn opaque to the
   certgen signature checker (an in-language decline) and to the Rust
   agreement peel (a "fragment drift" panic). The opaque-globals round's own
   doctrine names the fix: unfolding-for-analysis happens **at the
   reflection boundary**. `Elaborator::unspell_ty_deep` (the exact inverse
   walk, replacing `El (D#tycode^δ)` with the registry's inline copy) now
   runs in `fn_type_code` and in `certgen.rs`'s `sig_peel`, so the analyzer
   sees the very type it analyzed before the respell existed. One subtlety
   worth the comment it got: the two sites resolve references against
   *different worlds* (`fn_type_code` rescopes to the current Ψ; `sig_peel`
   reads the raw prefix-scoped statement), so the resolver takes the anchor
   length explicitly rather than guessing — the padded `gen_def_of`
   arithmetic is wrong at both.

What remains open on the issue after this round, re-attributed by wall time
rather than node count: the `Supf`/`ElimWf` **shape/arity slots at values**
(one whole shape and one arity per constructor value — dominant in
value-heavy statements now that everything nameable is a reference), which
is [[wf-shape-annotation-slots]]'s fix shape at a site that issue should now
record; and conversion's own cost on large values, which no spelling change
reaches.
