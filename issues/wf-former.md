---
title: Wf former: finitary branching inductives in the kernel
status: closed
labels: [kernel,inductives,metatheory]
created: 2026-07-25
updated: 2026-07-28
---

The kernel round for route C of [[tier1-branching-constructors]]: three
formers (`Vec`, `Fin`, `Wf`) giving finitary branching inductives with
Σ-tuple children and a `Fin`-indexed ih. **Rules:**
`docs/wf-former-design.md` (written before the code, still the spec the
implementation is checked against). **Decision record:**
`docs/branching-inductives-choice.md` §15. **Kernel summary:**
`crates/kernel/DESIGN.md`, Fragment section, last two paragraphs.

## Status: all five phases landed

| | Phase | State |
|---|---|---|
| 1 | `Vec` + `Fin` formers | **done** — commit `f538141`, `crates/kernel/tests/vec_fin.rs` (12) |
| 2 | `Wf` / `sup_f` / `elim_Wf` | **done** — commit `2ddd20b`, `crates/kernel/tests/wf.rs` (12) |
| 3 | codes + `rec.rs` branches; lifts the layer-c gate | **done** — commit `1c43729`, `crates/kernel/tests/wf_codes.rs` (8) |
| 4 | ch. 07 logical relations | **done** — `docs/metatheory-ch07-extensions.md` part II. **Abort criterion not triggered.** One kernel defect found, split out as [[unit-level-and-vec-preservation]] — **closed**, route (a) |
| 5 | generator round (one regime) | **done** — `docs/inductive-tier1-wf-lowering.md`, `crates/elab/src/wf.rs`, `crates/elab/tests/inductive_tier1.rs` (13). Closed [[tier1-branching-constructors]] |

## Phase 5, as landed

**Delivered.** A branching tier-1 declaration written at the *surface* lowers
onto the former: the type, constructors, the recursor with a `Fin`-indexed ih
reached by a guarded self-call, and both halves of no-confusion. The scheme is
`docs/inductive-tier1-wf-lowering.md` (written before the code, then corrected
in one place *by* it, §7); the mechanization is `crates/elab/src/wf.rs`;
`crates/elab/tests/inductive_tier1.rs` is its §10 checklist, all eight items.

**The acceptance**, and it is the issue's own: `Tree { Leaf, Node(Tree,
Tree) }` declared at the surface and `mirror (mirror t) = t` proved by an
ordinary recursive `theorem` through the generated recursor — the same
theorem `crates/kernel/tests/wf.rs` proves by hand, with no funext anywhere
and `β` firing on open children.

**Two things it did not deliver**, split rather than dropped:

- **`Rose` is not one step away**, and the design doc's "nearly free" was
  right about the *type* and wrong about the *lowering*. Arity-as-a-term does
  make the child count data, but a declaration whose field type is a
  user-declared `List` would make the generator identify that `List` with the
  kernel's `Vec`, and `fromVec (toVec xs) ≡ xs` holds only for canonical
  `xs` — so `match (Node xs) { … }` would stop firing on an open `xs`, which
  is the one property this tier exists for. What unblocks it is surface
  support for a children-container field type: a surface-language round.
  Split out as [[nested-inductives-container-fields]]; argument in
  `docs/inductive-tier1-wf-lowering.md` §8.1.
- **Polymorphic containers are a surface gap, not a lowering one.** The
  level constraint is gone and the lowering takes its level from the shape
  throughout, assuming nothing; but the surface's type grammar (`Nat`, a
  named declaration, `=`) has no inhabitant above level 0 to instantiate a
  parameter with. `wf.rs::polymorphic_shape` stays the kernel-side coverage.

**Findings from the round worth not rediscovering:**

- **A constant motive frees the step from `ih`, not from `cs`.** Both halves
  of no-confusion looked like "`elim_Wf` at a constant motive with a case
  tree on the tag", and that is right for disjointness and for a *payload*
  field. It is wrong for a *recursive* field: reading the `t`-th child needs
  `nth` at the literal arity, and outside a tag branch `cs : Vec(D; n[a/x])`
  is stuck on the variable `a`. That case needs the same `cs`-generalization
  `match` does, and now shares the code. The kernel caught it as a
  `NotConvertible` — the cheap half of the tier's hazard class.
- **An arm binder is an alias, not a kernel binder**, so the guardedness
  analysis has no binder *position* to compare a self-call's argument
  against. It compares terms instead, which keeps the shadowing property the
  positional comparison gave for `Nat` — and is syntactic, which is the
  brittleness split out as [[guard-matches-self-calls-by-term]].
- **Distinct constructors routinely share a shape summand.** `Leaf` and
  `Node` both lower to `Σ(#tag). Unit⁰` — the same kernel type. The injection
  is what distinguishes them, and the nominal tag still separates `Tree` from
  a structurally identical declaration.
- **Every shift in the lowering was a no-op**, because a monomorphic
  declaration lowers to a *closed* `⟦D⟧` — so `wf.rs`'s
  `d_ty.shift_local(…)`, `build_children`'s `snd_ty` shift and `inject`'s
  spine shifts were written to be correct and observed by nothing. The audit
  that established this turned up a live tier-0 wrong-type bug,
  [[tyvar-scoping-in-lowered-fields]] — **fixed**, and its fix is what
  created the observer: `inductive_tier1.rs`'s
  `the_lowering_shifts_are_exercised_by_a_dependent_parameter` runs the whole
  `mirror (mirror t) = t` acceptance over `Tree<n = n>`, where `⟦D⟧` has a
  free local and every one of those shifts is load-bearing. It fails against
  the pre-fix elaborator, so it is a real observer and not a passing test.
- **The de Bruijn hazard landed where the issue predicted.** `App`'s `cod`
  binds its argument, and the step's two trailing applications
  (`(case a) cs ih`) are exactly where that bites; `wf.rs::apply_cs_ih`
  writes all four instantiations out rather than folding them.

## What exists now

- `Type::Vec { level, elem, len }`, `Type::Fin { len }`,
  `Type::Wf { level, shape, arity }`; `Term::Supf`, `Term::ElimWf`; the
  codes `Term::TmVec`, `Term::TmFin`, `Term::TmWf`.
- `term::nth(level, elem, len, cs, idx)` — the fixed `elim_Nat` schema, not
  a former; materialized by the `Wf` rules.
- `term::wf_step_telescope(gamma, level, motive_level, shape, arity,
  motive) -> (cs_ty, ih_ty, step_ty)` — built once and shared verbatim by
  `typing.rs`, `conv.rs`, `rec.rs` and `reduce.rs`, deliberately, so the
  four transcriptions of the step telescope cannot drift.
- **No layer-c gate any more**: all three formers, `sup_f`/`elim_Wf` and
  the three codes are layer-c citizens, and the code recursors carry all
  eight new branches (`ty_vec`/`tm_vec`, `ty_fin`/`tm_fin`, `ty_wf`/
  `tm_wf`, `tm_supf`, `tm_elim_wf`; 37 → **45**), so the branch bundle is
  still exhaustive **over the syntactic formers** at layer `c`.
  Not "over all boxed code": ch. 06's neutral grammar (`06:31–38`) lists
  `elim_Typ(…; box U^δ)` and `elim_Trm(…; box u^δ)` as neutral forms and says
  so outright — *"for the recursive principles, we block on global
  variables"*. Global variables are legal at layer `c` and have no branch by
  design. `reduce.rs` implements exactly that
  (`recursors_block_on_boxed_global_variables`), and
  `docs/metatheory-ch07-extensions.md` §8 counts it correctly; only the
  shorthand here was overstated.

## Phase 4: the falsifier, spent

Full argument: `docs/metatheory-ch07-extensions.md` §§10–17. What phase 5
and any later reader need from it:

- **`Vec`/`Fin` have no LR case at all** — stronger than predicted. Type
  rules are keyed on the whnf; canonical lengths reduce away (weak-head
  expansion inherits the `Unit`/`Σ`/`Empty`/`+` clause) and neutral lengths
  hit the existing neutral-type rule. They owe two Congruence-for-Neutrals
  laws, of a new kind: the first neutral-type congruences with a *type*
  premise (`El ν`'s premise is a term).
- **`Wf` is a restriction of `W`'s in three senses** — type rule (a `Nat`
  term relation where `W` has a position-*type* relation), term relation
  (finite Σ-spine where `W` has a subtree quantifier), layering restriction
  (one contravariant premise where `W` has two). `NfEqWf` is a `Wf`-shaped
  inductive definition where `NfEqW` is a `W`-shaped one.
- **The spine recursion is on the arity's `NfEqNat` derivation, not on
  either length.** The two sides' arities are related, not equal; `NfEqNat`
  is what forces them to reduce in lockstep. This is the one place a
  careless copy of `W`'s clause goes wrong.
- **One new lemma**, the index lemma (§13): `elim_Wf`'s arm needs
  relatedness at arbitrary `Fin` indices, which the finite spine does not
  hand over. Four cases, all reductions the kernel already performs.
- **No funext obligation in the `elim_Wf` arm.** The only `Π` is the ih and
  the `Π` term relation is the applied form — the semantic counterpart of
  "the ih is transient".

### The kernel defect it turned up — split out as its own issue

`Vec^l(T; 0) ⇝ Unit` **drops the level**, so ch. 06's *Preservation* lemma
fails for every `l ≠ 0`. Full write-up and measurements:
[[unit-level-and-vec-preservation]]; **decided 2026-07-25 as route (a),
level-indexed `Unit^l`/`Empty^l`** — rules and phases in
`docs/unit-empty-level-indexing.md`.

**CLOSED 2026-07-25** by route (a), level-indexed `Unit^l`/`Empty^l`
(`docs/unit-empty-level-indexing.md`, four phases). The sequencing constraint
it imposed on phase 5 is **gone**: `Vec^l(child; 0) ⇝ Unit^l` keeps its level,
so a polymorphic container's nullary constructor builds. The end-to-end
acceptance test is `wf.rs::polymorphic_shape` — a real `Wf` at level 1 whose
`Node` carries a type payload. **Phase 5 may go polymorphic.**

Two things from it worth carrying here:

- **`Vec` is the kernel's first type former whose whnf is chosen by a term
  that carries no level.** `El`'s term is a code and does; `Vec`'s length is
  a bare `Nat`. That is the whole source of the defect, and it is a property
  of the `Wf` group specifically.
- **The witness was never rare — the observer was missing.** `gen_wt_type`
  takes `Vec`'s level from its element and picks a small literal length two
  times in three, so it had been producing `Vec^{l>0}(T;0)` hundreds of times
  per run since phase 1. The suite had the *term* half of preservation and no
  type half. Corrected below.

## Findings from phases 1–3 worth not rediscovering

- **The `Vec`/`Wf` branches bind one universe, not two.** `ty_w`'s shape
  and positions are both types, so it binds `ℓ, ℓ'`; an arity is a `Nat`
  term and contributes no level, so `ty_vec`/`ty_wf`/`tm_vec`/`tm_wf` bind
  only `ℓ`, and `ty_fin`/`tm_fin` bind none. Copying `ty_w`'s dims verbatim
  is the mistake to avoid.
- **A type-motive branch can have a term-motive recursive call.** In
  `ty_vec`/`ty_fin`/`ty_wf` the length/arity recursion goes at the *term*
  motive (`ty_el` is the ch. 04 precedent), so their `BRANCH_DIMS` entries
  end `(…, false, false)`: `Var(0)` does *not* inhabit the branch type.
- **Deep telescopes cost stack.** The `nth` schema inside
  `wf_step_telescope` made the 45-branch recursor check overflow the 2 MiB
  test-thread stack; `scripts/test` now sets `RUST_MIN_STACK=8M`. If
  elaboration ever runs recursors over deeply nested code, the same limit
  applies there.
- **Generated proof-irrelevant types break "η is not blind" negatives.**
  Adding `Vec` to `crates/kernel/tests/common/wt.rs` made
  `sigma_eta_and_neutral_distinctness` fail: `Vec(T;0) ⇝ Unit`, so a Σ of
  such components really does identify its inhabitants — the kernel was
  right. That negative now runs at `Σ(S, Nat)`, relevant by construction.


- **The motive is an ordinary `Type` binding `z`** — no `Ty`-code round
  trip. The postulate prototypes needed codes because their eliminator was a
  term with a `Ty`-valued motive; a real former does not, so the generated
  recursor (phase 5) is simpler than
  `crates/elab/tests/branching_route_c_nary.rs` suggests.
- **`Empty`-η is not needed for the nullary arm**, contrary to what the
  route-A round implied. Arity 0 is `Vec(T; 0) ⇝ Unit`, and proof
  irrelevance already collapses every nullary constructor form — including
  the `u : Unit` payload in the tag. `Empty`-η stays independently nice for
  tier-2 `Acc` under `W`, but nothing here depends on it.
- **`Fin` was the sheddable piece** if phases 3–4 ran heavy: it never
  mentions `Wf`, so it could revert to an inlined `El (elim_Nat …)` schema
  (the n-ary prototype did exactly that and it worked). Neither round needed
  it — phase 4 gave `Fin` no LR case at all, which is the cheapest possible
  outcome — so it stays primitive, for goal readability and symmetry.
- **`Rose`-style nesting falls out of arity-as-a-term**: `Rose { Node(A,
  List Rose) }` is `Wf` with `S = Σ(a : A). Nat` and `n = snd x` — the child
  list *is* the `Vec`, its length is data in the shape. Worth exercising in
  phase 5.
- Watch de Bruijn indices in hand-built test terms: `App`'s `cod` binds its
  argument, so it sits one level deeper than the ambient. Both acceptance
  tests failed first on exactly that — in the test, not the kernel.
- **Half a lemma is a blind spot shaped like its other half.** The suite had
  `reduction_preserves_type` (the *term* half of ch. 06's Preservation) and
  no type half, which is the *only* reason phase 4's defect survived from
  phase 1 — the generator had been producing the witness all along.
  `conv_properties::type_reduction_preserves_level` now exists and failed on
  seed 102, first run. **Swept: [[metatheory-lemma-sweep]]** — all 53 lemmas
  of ch. 05/06 audited (`docs/ch05-06-lemma-audit.md`), nine new property
  tests, and the generalization sharpened: it is not only lemmas with halves,
  it is **anything the implementation emits and never re-reads** — an inferred
  type, a generated witness, a classification predicate kept in two places.
  The one defect the sweep found was of that second kind, in the *generator*
  rather than the kernel (see below).
- **The generator's own oracle was under-powered.** `gen_wt_term` produced an
  ill-typed term at a rate of 1 in 3000; the only check on that precondition
  was 300 cases on one seed stream. Cause was a layer slip — `Δ` for a
  contextual type built at layer `p` (correct per ch. 04) hosting a layer-`c`
  body that then lifted a `p`-only entry type into an annotation. Fixed by
  building code-hosting `Δ`s at layer `c`. Every property test in the crate
  rests on that precondition, so phases 1–4's *negative* results are only as
  strong as it is.
- **Check a proposed fix against ch. 04's design constraints, not just the
  failing case.** The one-line `Unit`-polymorphism repair made the failing
  test pass and quietly broke uniqueness of types, which ch. 04
  §Non-cumulativity says the code eliminator depends on. The `rec.rs` branch
  telescopes are the tell: `ty_ty` binds a universe, `ty_unit` does not.

## Also in scope, decision-independent — split out, not done

`Empty`-η in `conv.rs` rode along as "cheap, plainly sound, not blocking"
through all five phases and was needed by none of them — the nullary arm
turned out to be `Vec^l(child; 0) ⇝ Unit^l`, whose irrelevance already does
the job. Split out as [[empty-eta-conversion]] rather than done as a
drive-by: it is a change to *conversion*, which is the one part of the kernel
this round deliberately did not touch, and a new η rule is not in ch. 06 so
it owes a ch. 07 clause. Its customer is tier-2 `Acc`.

## Log

- 2026-07-25: Phase 1 landed — Type::Vec and Type::Fin in the kernel. Reductions on the length (Vec(T;0)⇝Unit, Vec(T;S k)⇝Σ(_:T).Vec(T;k), Fin(0)⇝Empty, Fin(S k)⇝Unit+Fin(k)), neutral at a neutral length with structural congruence there; formation rules (Vec at its element's level, Fin at 0, length checked at Nat); no introduction/elimination forms — all eta is inherited through the reductions, which is the design's whole premise. Sites touched: term.rs (enum), subst.rs (length at same depth, no binder), reduce.rs (step_type + is_whnf_type/is_neutral_type keyed on whether the length is stuck + explicit beta_elim_ty block), typing.rs (formation + not_code_layer gate), conv.rs (neutral-length congruence + tm_nf neutral-type arm), fmt.rs. GATE: Vec/Fin are rejected at layer c until phase 3 gives them code formers and rec.rs branches, so boxed code stays exhaustively recursable; beta_elim_ty returns None (stuck) rather than mis-firing as belt-and-braces. Tests: crates/kernel/tests/vec_fin.rs (12), including sigma_eta_reaches_through_vec — for a NEUTRAL tuple cs : Vec(Nat;2), cs is convertible with its own projections repackaged, i.e. the equation route A needs funext for, discharged here by existing Sigma-eta + Unit-irrelevance. Also added Vec/Fin to the property-test type generator (common/mod.rs arms 16/17, >20/300 hit rate verified by test), so subst_laws/conv_properties/reduce now exercise them; full suite 289 passing.
- 2026-07-25: Phase 2 landed — Wf, sup_f, elim_Wf. Formation (Wf^l(x:S).n at level l — the arity is a Nat TERM with the shape free, so it contributes no level, unlike W whose positions are a type), introduction with Vec-tuple children, dependent elimination with the Fin-indexed ih, and the beta rule that synthesizes the ih lambda around the recursive call (same 'only beta rule that builds a binder' shape as elim_W's, but over a Fin index). nth is NOT a former: it is a fixed elim_Nat schema materialized by the rules (term::nth), and the step telescope is built once in term::wf_step_telescope and shared verbatim by typing.rs and conv.rs so the two transcriptions cannot drift — the hazard the design doc flagged. Sites: term.rs, subst.rs (arity binds one, motive one, step three), reduce.rs (beta + neutrality + whnf), typing.rs, conv.rs (Wf type congruence, sup_f value comparison at Vec type, elim_Wf neutral congruence), fmt.rs, tests/common (count + generators). Still layer-c gated until phase 3. ACCEPTANCE MET (crates/kernel/tests/wf.rs, 12 tests): Tree { Leaf, Node(Tree,Tree) } built on the real former, and mirror (mirror t) = t proved with every beta-marker deleted — the Leaf arm is literally refl_tree(leaf()) and the Node arm is cong + cong + trans, versus route A's funext-per-arm. sigma_eta_bridges_the_constructor_form pins the headline at the real former: for a NEUTRAL tuple cs, sup_f(inr u; cs) is convertible with node (nth 2 cs 0) (nth 2 cs 1). Two notes for phase 3: the motive is an ordinary Type binding z (no Ty-code round trip, unlike the postulate prototypes, since the eliminator is a former now), and Empty-eta turned out NOT to be needed for the Leaf arm — arity 0 is Vec(T;0) which reduces to Unit, whose proof irrelevance already collapses every nullary constructor form. Full suite 301 passing.
- 2026-07-25: Phase 3 landed — codes and the eight recursor branches; the layer-c gate is gone. New codes Term::TmVec/TmFin/TmWf with El decoding (only the element/shape decodes; the length and the arity are Nat terms and ride across unchanged). New branches ty_vec/tm_vec (1 univ, 3 globals, 2 locals), ty_fin/tm_fin (0/2/1), ty_wf/tm_wf (1/3/2), tm_supf (1/5/4), tm_elim_wf (2/6/5) — the last comparable to tm_elim_w but one universe shallower, its step binding built by wf_step_telescope so rec.rs/typing.rs/reduce.rs share one transcription. Sites: term.rs (3 variants + 8 Branches fields), rec.rs (branch_terms/branch_specs 37→45), subst.rs (code depths + map_branches), reduce.rs (El decoding, beta_elim_ty Vec/Fin/Wf replacing the None gate, beta_elim_tm TmVec/TmFin/TmWf/Supf/ElimWf, whnf classification), typing.rs (TmVec/TmFin/TmWf rules; not_code_layer deleted outright — it had no other users), conv.rs (congruence for the three codes), fmt.rs. Tests: crates/kernel/tests/wf_codes.rs (8) — El decoding, layer-c acceptance, and the identity recursor round-tripping box(Vec), box(Fin), box(Wf), box(TmVec/TmFin/TmWf), box(sup_f) and box(elim_Wf) in one β-step, which is the sharp cross-check of the new telescopes against reduce.rs's fire; plus a poisoned-branch negative and a generator-coverage check. BRANCH_DIMS is 45, identity_branches (both copies) grew eight hand-written arms, and both generators now reach the new formers — the scope-only one in common/mod.rs and, new here, the well-typed one in common/wt.rs (Vec/Fin/Wf types and TmVec/TmFin/TmWf encodings), so the subject-reduction and identity-recursor property suites cover them. Two incidental fixes fell out: scripts/test needs RUST_MIN_STACK=8M for the deeper telescope, and conv_pair_properties' 'η is not blind' negative moved to Σ(S, Nat) because a generated Vec(T;0) is genuinely proof-irrelevant. Full suite 309 passing.
- 2026-07-25: Phase 4 landed — the ch. 07 pen-and-paper pass, `docs/metatheory-ch07-extensions.md` part II (§§10–17). ABORT CRITERION NOT TRIGGERED; the branching-inductives decision is final and route A is no longer a live fallback. Vec/Fin turn out to need NO logical-relations case at all (stronger than the design doc's §8 prediction of "restricted clauses"): every type-relation rule of 07 is keyed on the whnf, so at a canonical length they reduce away and weak-head expansion inherits the Unit/Σ/Empty/+ clause, while at a neutral length they ARE the whnf and the existing neutral-type rule applies — they owe only two Congruence-for-Neutrals laws, which are a new kind (first neutral-type congruence with a type premise; El ν's premise is a term). Wf's case is a restriction of W's in three separately checkable senses: its type rule is W's with a term relation at Nat replacing the position-type relation F; its term relation NfEqWf replaces W's subtree quantifier with a finite Σ-spine, recursing on the arity's NfEqNat derivation (NOT on either length — the two sides' arities are related, not equal, and NfEqNat is what forces lockstep reduction; this is the one place a careless copy of W's clause goes wrong); and its layering-restriction case has one contravariant premise where W has two. Consequence worth keeping: NfEqWf is a Wf-shaped inductive definition where NfEqW is a W-shaped one, so a mechanization needs only finitary branching induction where W needs infinitary — the object-level restriction holds one level up too. The single new obligation is the index lemma (§13): elim_Wf's arm needs relatedness at arbitrary Fin indices, which the finite spine does not hand over directly; four cases (arity ze/su/neutral, and NfEqSum on the index), all reductions the kernel already performs, all at an arbitrary weakening because the children premise stays Kripke-quantified. No funext obligation appears in the elim_Wf arm: the only Π is the ih and the Π term relation is the applied form, the semantic counterpart of "the ih is transient". KERNEL DEFECT FOUND AND FIXED, and it is the pass paying for itself: writing the fundamental-theorem arm for Vec-formation exposed that Vec^l(T;0) ⇝ Unit DROPS THE LEVEL, so a well-formed Π^{1,0}(_ : Vec^1(T;0)). Nat stepped to an ill-formed Π^{1,0}(_ : Unit). Nat — type-level subject reduction failed for every l ≠ 0. Invisible until now because a generated shape is a sum of records at level 0. Fixed by making the two component-free formers (Unit, Empty) level-polymorphic in formation: typing.rs::ty_check special-cases them ahead of the level comparison, ty_infer still reports 0, now documented as the LEAST rather than the canonical level. Not cumulativity — every other former keeps an exact level and Vec only ever over-declares (successor preserves l, nullary drops to 0), so nothing large enters a small universe; conv.rs needed no change since ty_nf already ignores its level argument. Two regressions in crates/kernel/tests/vec_fin.rs (vec_at_zero_reduces_without_dropping_its_level, only_unit_and_empty_are_level_polymorphic). Recorded in crates/kernel/DESIGN.md (Fragment) and docs/wf-former-design.md §1.1. Also recounted §8 of the ch07 doc: 13 type + 32 term formers at layer c = 45 branches, matching term.rs and BRANCH_DIMS. Honest caveat carried in §17: this is pen and paper like part I, and the transitivity/irrelevance cases for Wf were checked for shape against W's rather than written out — the composite spine recursion in transitivity is the one construction that appears twice and was written once. Full suite 311 passing.
- 2026-07-25 (same day, follow-up): The phase-4 level fix was WRONG and is reverted. Investigating the "level 0 hides level bugs" hypothesis showed it was false — common/wt.rs's gen_wt_type takes Vec's level from its element and picks a small literal length two times in three, so Vec^{l>0}(T;0) had been generated hundreds of times per run since phase 1. What was missing was the OBSERVER: conv_properties had reduction_preserves_type, the term half of DeLaM ch. 06's Preservation lemma (If ⊢ T @ l and T ⇝ T' then ⊢ T' @ l; if ⊢ t : T @ l and t ⇝ t' then ⊢ t' : T @ l), and no type half. Added conv_properties::type_reduction_preserves_level; with the kernel reverted it fails on seed 102, first run, no tuning. Then checking ch. 04 showed the fix itself was unsound in design: §Non-cumulativity says "we must specify in each case how do we construct the original code from its components; therefore, it is the most convenient, when each term has a unique type", i.e. uniqueness of types is load-bearing FOR THE CODE ELIMINATOR. box T : □(Δ ⊢ Ty l) is checking-only and checks T at l via ty_check, so a level-polymorphic Unit is a term with many types. Measured: box Unit : CodeTy(0/1/2) all Ok while box Nat correctly stays at 0 only; and elim_CodeTy(code_level=1; box Unit) TYPECHECKS while firing into the ty_unit branch, which rec.rs builds with tele.univs = 0 and instantiates at ℓ := 0 — so the redex is typed at M[1/ℓ] and the reduct verified at M[0/ℓ]. For the identity motive the reduct survives because box Unit now inhabits both, i.e. the polymorphism masks its own damage; for a motive genuinely depending on ℓ it does not. Preservation simply moved from Vec to the code recursor, which is the worse place. The tell was visible in rec.rs all along: ty_ty binds univs:1 and reconstructs at lvar(0) because Ty ℓ's level varies, ty_nat/ty_unit bind none. Reverted to the pre-fix kernel; the Vec gap is open and now PINNED by vec_fin::vec_at_zero_drops_its_level_known_gap, with the invariant any fix must preserve pinned by vec_fin::every_type_has_exactly_one_level (including the box consequence). type_reduction_preserves_level stays live and skips only this reduct with only this error, mirroring the NotInferable/box-synthesis-gap skip already in the same file. typing.rs::ty_check's doc comment now warns the next reader off the one-line fix. Split out as issues/unit-level-and-vec-preservation.md with three costed candidates: (a) level-INDEXED Unit^l/Empty^l, parameterized rather than polymorphic as non-cumulative systems do it, which restores uniqueness on the nose and turns ty_unit/ty_empty into copies of ty_ty — favoured, but a phase-3-sized round since Triv and ElimEmpty must carry levels too or the disease returns at tm_triv; (b) layer-gate the polymorphism to p/m only, since §4's argument is entirely about layer c and box checks its body at c — roughly two lines, but gated on an unanswered question, namely whether anything requires every layer-p MLTT type at level l to have a code at Ty l; (c) make Vec^l(T;0) its own proof-irrelevant whnf, which costs an LR case and an intro rule and reintroduces non-uniqueness at Triv. Phase 4's LR results are unaffected — §§11–17 do not route through Vec's nullary reduct and the abort criterion turns on the shape of the recursion. Full suite 312 passing.
- 2026-07-25: Post-phase-4 sweep landed: [[metatheory-lemma-sweep]]. All 53 lemma environments of DeLaM ch. 05/06 audited in docs/ch05-06-lemma-audit.md with a verdict each (property-checked / instance-only / open gap / by-construction / not expressible); nine new property tests in crates/kernel/tests/ch05_06_lemmas.rs closing seven paper lemmas or halves; suite 312 -> 322. Two more instances of the missing-half pattern: the TYPE half of ch. 06 Soundness (06:148) was absent next to the term half, one lemma before Preservation; and Determinacy (06:310/:319) holds by construction but its presupposition does not — step().is_none() must be exactly is_whnf(), two independent copies of the Vec/Fin stuck-length condition, now checked. The one real defect was in the SUITE: gen_wt_term produced an ill-typed term at 1 in 3000, and the only observer of that precondition was 300 cases on a single seed stream; cause was Delta for a contextual type generated at layer p (correct per ch. 04) hosting a layer-c body that lifted a p-only entry type into a J motive. Fixed by generating code-hosting Deltas at layer c — still valid p-contexts by ch. 05 Lifting, which this round machine-checked. Also settled while auditing: no Tarski-completeness claim exists in the paper, which is evidence (not a verdict) for candidate (b) of [[unit-level-and-vec-preservation]].
- 2026-07-26: Phase 5 landed — the generator round, so [[tier1-branching-constructors]] is CLOSED. Scheme first per the tier's discipline: docs/inductive-tier1-wf-lowering.md, written against the kernel phases 1-4 landed, mechanized by crates/elab/src/wf.rs. ACCEPTANCE MET: Tree { Leaf, Node(Tree, Tree) } declared at the surface and mirror (mirror t) = t proved by an ordinary recursive theorem through the generated recursor (crates/elab/tests/inductive_tier1.rs, 13 tests), matching crates/kernel/tests/wf.rs by hand. Shape = tier 0's sum-of-Σs with the recursive fields deleted; arity = tier 0's constant-motive case tree at the motive Nat; step telescope = term::wf_step_telescope, called rather than transcribed a fifth time. Constructors are sup_f with a literal children tuple built at the LITERAL arity (conversion closes the gap to n[label/x], since the arity is a Case on an injection). The recursor is one elim_Wf whose step cases on the tag with cs AND ih generalized in the case motive, because outside a tag branch the arity is stuck on a variable and neither Vec nor Fin reduces — the shape wf.rs's mirror uses, now generated. An arm's recursive binder aliases to nth cs' ι_t and a guarded self-call on it becomes ih' ι_t, so Guard grew a Wf kind carrying a table of (child, ih) pairs and matches self-call arguments by TERM rather than by binder position (an arm binder is an alias, not a kernel binder, so there is no position to compare). No-confusion: disjointness by elim_Wf at the motive Ty 0 (large elimination over a Wf needs no new kernel power — its motive is an arbitrary Type, exactly as Case's is), injectivity at a payload field by fst/snd and at a recursive field by nth. ONE CORRECTION to the scheme, made by the kernel: a constant motive frees the step from ih but NOT from cs, so the recursive half of injectivity needs §6.2's generalization too and now shares build_elim_wf over a Branches choice of branch body; docs §7 records it. Two things NOT delivered and split rather than dropped. (1) Rose: the former types nested recursion (arity-as-a-term makes the child count data), but a surface declaration whose field type is a user-declared List would make the generator identify that List with the kernel's Vec, and fromVec(toVec xs) is convertible with xs only for canonical xs — so it would cost beta on OPEN subterms, the property this tier exists for. It needs surface support for a children-container field type: a surface-language round, argued in docs/inductive-tier1-wf-lowering.md §8.1. The design doc's 'nearly free' was right about the type and wrong about the lowering. (2) Polymorphic containers: the level constraint is gone and the lowering assumes nothing (levels come from the shape throughout), but the surface's type grammar (Nat, a named declaration, =) has no inhabitant above level 0 to instantiate a parameter with, so nothing at the surface can reach the polymorphic case. wf.rs::polymorphic_shape remains the kernel-side coverage. Full suite 331 -> 341.
- 2026-07-26: CLOSED. All five phases landed; docs/wf-former-design.md §9 is the record and its acceptance is met at both ends — by hand in crates/kernel/tests/wf.rs (phase 2) and from the surface in crates/elab/tests/inductive_tier1.rs (phase 5). Two in-scope items are split out rather than silently dropped: [[empty-eta-conversion]] (the decision-independent conv.rs item, needed by no phase, owing a ch. 07 clause, customer is tier-2 Acc) and [[nested-inductives-container-fields]] (Rose, which needs a surface children-container field type, not a generator tweak). Full suite 289 at phase 1 -> 344 now.
- 2026-07-28: Cost of `Wf` elimination now has a number, from the bench suite ([[kernel-benchmarks]]): 38 reduction steps per constructor -- flat in depth, so the elimination itself is linear in the data as designed -- but 35 us per step, because substituting the step body rebuilds its closed annotations every time ([[subst-rebuilds-unchanged-subterms]]). Nothing here is wrong with the former or its rules; the constant lives in subst.rs. wf/mirror-involution is the standing end-to-end fixture.
