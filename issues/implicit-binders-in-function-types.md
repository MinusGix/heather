---
title: Implicit binders in function types and lambdas
status: closed
labels: [frontend,elaboration,design]
created: 2026-07-26
updated: 2026-09-17
---

`{x: A} -> B` and `λ {x: A} => e`. Wanted, deliberately **out of scope** for
[[surface-function-types]], and split out here so it does not get lost as a
struck line in that issue.

Wanted because implicit arguments are useful on a function passed **by
value**, not only on a named declaration: the moment a `Compile` instance or
an optimization pass takes a lemma-shaped callback
([[compile-typeclass-design]], [[certifying-generator]]), that callback wants
its endpoints inferred exactly as `trans`/`sym` do today. Without this, every
higher-order use is `@`-spelled and the ergonomics that
[[elab-stage2-metas]] bought at the declaration level stop at the first
lambda.

## Why it did not come with function types

Structural, not effort. Implicitness is **not** in the kernel: `Type::Pi` has
`dom_level`/`cod_level`/`dom`/`cod` and no flag, and that is right — an
implicit argument is an elaboration concern, and the kernel must re-check the
saturated term either way.

Today it lives in the elaborator as `ParamMeta.implicit` on a *declaration*,
reached **by name**:

- `params_of` / `implicit_mask` (`crates/elab/src/lib.rs:1303–1315`) look the
  parameter list up in `self.globals` by the callee's name,
- `apply_implicit` (`lib.rs:1362`) consumes that `mask` to decide, per Π in
  the spine, whether to insert a fresh Ψ-meta or take the next argument.

So there are two gaps. A function **type** has nowhere to record the flag,
and a λ-bound **value** has no `ParamMeta` to look up. The consequence in the
current design is stated in [[surface-function-types]] §5.3: implicit
insertion is name-directed, so applying a function value is always explicit.

## What it would take

The flag has to travel with the type, without entering the kernel. The
options, roughly in increasing order of invasiveness:

1. **An implicitness spine beside the type.** The elaborator carries
   `(Type, Vec<bool>)` — or a small `FnShape` — wherever it carries a callee
   type, and `apply_implicit` reads the mask from there instead of from
   `params_of`. Cheap where types are built by the elaborator; the question is
   what happens to the mask when a type arrives from `whnf`, from a
   `GlobalSubst`, or out of an `inductive` field, where it is lost.
2. **A surface-level type wrapper.** Keep an elaborator-side type language
   that mirrors `Type` plus implicitness, and erase to `Type` at the kernel
   boundary. Honest and total, but it is a second type representation to keep
   in sync — the cost the codebase has so far avoided everywhere.
3. **Named-argument style instead of positional implicits** for function
   values, sidestepping inference. Not really the same feature.

Option 1 is the obvious first cut; option 2 is where it ends up if the mask
keeps getting lost.

## Sequencing

Not urgent while the surface has **no universe**: `TyKind` cannot say `Type`,
so `{A: Type} -> …` is not writable and implicit *value* binders
(`{n: Nat} -> …`) are the only expressible case. The feature becomes properly
valuable at the same time universe polymorphism reaches the surface, which is
layer-m work ([[elab-unifier-completeness]] notes level-meta inference is
naturally sequenced there too). Likely picked up with, or just after, the
trait layer.

~~Until then `{` in a function type or lambda binder is a diagnostic pointing
here ([[surface-function-types]] §8).~~ Shipped 2026-08-06: both spellings
parse and the skeleton design (option 1) is implemented — see
docs/language/implicit-binders-design.md and the closing log entry.

## Log

- 2026-07-26: Split out of [[surface-function-types]], whose scheme doc found
  the structural reason implicit binders could not ride along with function
  types. Kept as its own issue at the user's request: implicit arguments on a
  by-value function are a real feature, not just a symmetry with `fn`.
- 2026-08-06: DECISION (user): implicitness is a property of the SURFACE type, erased at the kernel boundary — the elaborator carries a positional implicitness skeleton beside the kernel type (this issue's option 1; option 2, the full mirrored type language, is the named fallback if the skeleton keeps getting lost). Two alternatives named and rejected: a kernel Pi flag (forks the function space or threads inert data through conversion — either way a shared-notion edit taxing every Pi-touching lemma, the 52-branch walkers, and the in-progress Coq formalization, for data with no semantic content); and the Lean/Agda shape (binderInfo carried in the term but ignored by defeq) — the same cost structure hidden in every kernel traversal, printer, and transcription slot. The accepted degradation, stated up front: a function type that arrives by COMPUTATION (out of an eliminator, through a decoded code) has no skeleton and offers no implicit insertion — explicit spelling, today's behavior, never wrongness; the motivating uses (Compile instances, algebraic structures, lemma-shaped callbacks — record fields and declaration signatures) are all syntactic positions the elaborator lowers itself and can decorate at the source. Hazard named for the design round: this is stored elaboration metadata, and [[module-scope-of-stored-syntax]] shows how stored metadata goes stale — a skeleton dodges the name-resolution version (it is positional, nothing in it resolves) but the round must state its substitution story explicitly (skeletons travel with the context entry). Also to re-verify: the sequencing note above predates [[surface-universe]] landing (2026-07-27); whether a function type can now quantify over a type decides how much of the feature is expressible this round. Timing endorsed: before the trait layer, as its prerequisite, on the fresh apply_implicit machinery of the unifier round (docs/elaborator/unifier-completeness-design.md).
- 2026-08-06: SHIPPED (implementation round of docs/language/implicit-binders-design.md; closing). `{x: A} -> B` and `λ {x} / λ {x: A} => e` parse (the two parser diagnostics retired with successor pins in `crates/syntax/src/parser.rs` tests and `crates/elab/tests/function_types.rs`); implicitness is a positional `Skel` beside the kernel type, erased at the boundary — NO kernel change. Carriers: `Cx.skels` (one push path), `Alias.skel`, `DotResolution::Project`'s on-demand field skeleton, and — a deviation from the design's §3.1.4, amended there — `ParamMeta.skel`, the parameter's own domain skeleton, without which argument-position lambdas against a *global* callee had no expected skeleton (the design's own §10-positive-2). `apply_implicit` AND `apply_explicit` now take the parameter table from the caller (`params: Rc<Vec<ParamMeta>>`; value sites synthesize it from the skeleton), which is also what stops a skeleton-less local from borrowing a same-named global's hints (pinned). Value heads insert at application, bare in checking position (the §5.2 prefix route, for locals, aliases and projections), and defer/harvest with the unifier round's machinery unchanged; `@f(…)` on a value clears the whole mask (§7.1); unsolvable-implicit messages on a value offer only `@` and eta-expansion, never `<…>`. The §5.3 suppression composes with the 414531f universe-domain hotfix (skeleton consulted first where one exists, erased-type check as the fallback — the skeleton half is what covers value-implicit heads). Lambda coherence per §6.2 (implicit mark requires an implicit expected position; explicit binders accepted anywhere); `let`-RHS harvest per §6.3. §3.4 refusals: declaration result types, `D<…>`/`f<T>` type arguments, `[T; n]` element types, valparam and index types, meta signatures. Suite: `crates/elab/tests/implicit_fn_binders.rs` (16 tests incl. the degradation pinned as behavior), 3 parser pins; full `scripts/test` green, protected suites untouched. FOLLOW-ON NOTES (kept here per coordinator decision, not standalone issues): (1) result-position skeletons — `fn mk() -> {A: Type<0>} -> …` is refused today; carrying a skeleton on `GlobalInfo` so `mk()(x)` inserts is coherent future work, pick it up when the refusal first annoys someone. (2) A value-head `<…>` spelling — would give values written type arguments and dissolve §7.1's `@`-asymmetry. (3) No skeleton field on `Goal` this round (coordinator decision): an `on`-discharge lambda against a skeletal goal type sees a computed type — implicit-marked binders there are refused with the §7.3-2 message, explicit binders work; the fix is one field on `Goal` if wanted. Residual degradations, all explicit-spelling-not-wrongness: match-arm binder aliases carry field skeletons only on the tier-0/record `elab_arm` path and only for child-free constructors (the Σ walk is declaration-ordered only there); the indexed/forded/wf/pattern arm paths and match *motive bodies* leave marks inert rather than refused. (4) The §7.3-2 message says "computed, not written" for any skeleton-less expected type, including a *written but fully explicit* annotation (`skel_of_ty` is sparse) — the refusal is right, the wording lies in that one corner.
- 2026-09-17: A **parenthesized** implicit binder does not parse at all: `({a: A} → P(a)) ↔ R` is `parse error: expected `}`, found Colon`, where the explicit `((a: A) → P(a)) ↔ R` is fine. Found 2026-09-17 beside [[binder-headed-arrow-as-connective-operand]] and confirmed pre-existing on that round's parent commit, so the `↔` is incidental — the `(` + `{ Ident :` opening is what fails, and the ordinary parenthesis escape hatch is therefore absent for the implicit spelling. Distinct from this issue's deliberate positional restriction ("implicit binders take effect in parameter types, `let` annotations, field types, and lambdas"), which is a *post-parse* refusal and fires with a clear message; this one is the parser declining a grouping. Not fixed by that round, and left here as the owner of the spelling rather than filed separately.
